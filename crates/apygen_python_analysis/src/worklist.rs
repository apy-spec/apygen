use crate::abstract_environment::AbstractEnvironment;
use crate::genkill::statements::gen_statement;
use apy::OneOrMany;
use apy::v1::QualifiedName;
use apygen_analysis::cfg::{Cfg, EdgeData, ProgramPoint};
pub use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::{
    Location, NamespaceLocation, Namespaces, NamespacesContext, NamespacesProxy,
};
use apygen_finder::filesystem::{Error as FilesystemError, Filesystem};
use apygen_finder::pathfinder::{FileLoader, ModuleSpec};
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::mpsc::{Sender, channel};
use thiserror::Error;

pub fn merge_with(
    namespaces: &mut Namespaces<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    override_namespaces: Namespaces<QualifiedName, AbstractEnvironment>,
    override_dependents: HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
) -> bool {
    let mut changed = false;

    for (from, tos) in override_dependents {
        let dependents_entry = dependents.entry(from).or_default();
        for to in tos {
            if !dependents_entry.contains(&to) {
                changed = true;
                dependents_entry.insert(to);
            }
        }
    }

    for (location, env_map) in override_namespaces.locations {
        let environment_entry = namespaces.locations.entry(location).or_default();
        for (program_point, environment) in env_map.environments {
            if !environment_entry.environments.contains_key(&program_point) {
                changed = true;
                environment_entry
                    .environments
                    .insert(program_point, environment);
            }
        }
    }

    changed
}

pub fn worklist(
    context: &mut impl NamespacesContext<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    import_tx: &Sender<NamespaceLocation<QualifiedName>>,
    namespace_location: NamespaceLocation<QualifiedName>,
) {
    context.reset_abstract_environments(&namespace_location);

    let cfg = cfgs
        .get(&namespace_location.module)
        .map(|cfg| {
            Some({
                if let Some(program_point_id) = namespace_location.program_point_id {
                    cfg.sub_cfg(program_point_id)?
                } else {
                    cfg
                }
            })
        })
        .flatten()
        .expect("Should exist since worklist is only called on modules in the project data");

    let mut worklist: HashSet<ProgramPoint> = HashSet::from_iter([ProgramPoint::Entry]);
    while !worklist.is_empty() {
        worklist = worklist
            .into_iter()
            .flat_map(|program_point| {
                let location = Location {
                    namespace_location: namespace_location.clone(),
                    program_point,
                };

                let res_abstract_environments = if let Some(node_data) =
                    cfg.node_data(&program_point)
                {
                    gen_statement(
                        context,
                        dependents,
                        cfgs,
                        import_tx,
                        location,
                        node_data.statement(),
                    )
                    .unwrap()
                } else {
                    HashMap::from_iter([(EdgeData::Unconditional, AbstractEnvironment::default())])
                };

                let mut worklist: HashSet<ProgramPoint> = HashSet::new();
                for successor in cfg.successors(&program_point).cloned() {
                    let successor_location = Location {
                        namespace_location: namespace_location.clone(),
                        program_point: successor,
                    };

                    let edges = cfg
                        .edge_data(program_point, successor)
                        .expect("Should exist since successor is returned by cfg.successors");

                    for edge in edges {
                        if let Some(res_abstract_environment) = res_abstract_environments
                            .get(edge)
                            .or_else(|| res_abstract_environments.get(&EdgeData::Unconditional))
                        {
                            let new_successor_environment =
                                match context.get_abstract_environment(&successor_location) {
                                    Some(successor_environment) => {
                                        if successor_environment
                                            .includes(context, res_abstract_environment)
                                            .unwrap()
                                        {
                                            continue;
                                        }
                                        successor_environment
                                            .join(context, res_abstract_environment)
                                            .unwrap()
                                    }
                                    None => res_abstract_environment.clone(),
                                };

                            context
                                .abstract_environment_entry(successor_location.clone())
                                .insert_entry(new_successor_environment);

                            worklist.insert(successor);
                        }
                    }
                }

                worklist
            })
            .collect();
    }
}

#[derive(Debug, Error)]
pub enum ImportModuleError {
    #[error("Filesystem error: {0}")]
    FilesystemError(#[from] FilesystemError),
    #[error("Failed to parse module source code")]
    CfgParseError(String),
    #[error("Module spec does not have a source file loader")]
    NonSourceFileLoader,
}

pub fn load_cfg(module_spec: &ModuleSpec<impl Filesystem>) -> Result<Cfg, ImportModuleError> {
    match &module_spec.file_loader {
        FileLoader::SourceFileLoader { filesystem, path } => {
            let source = filesystem.read_file(&path)?;
            Ok(Cfg::parse(&source).ok_or_else(|| ImportModuleError::CfgParseError(source))?)
        }
        FileLoader::NamespaceLoader | FileLoader::ExtensionFileLoader { .. } => {
            Err(ImportModuleError::NonSourceFileLoader)
        }
    }
}

pub fn import_module_spec<'a>(
    qualified_name: &'a QualifiedName,
    module_spec: &'a ModuleSpec<impl Filesystem>,
) -> impl ParallelIterator<Item = (&'a QualifiedName, Result<Cfg, ImportModuleError>)> {
    fn all_submodule_specs<'a, F: Filesystem>(
        qualified_name: &'a QualifiedName,
        module_spec: &'a ModuleSpec<F>,
    ) -> Vec<(&'a QualifiedName, &'a ModuleSpec<F>)> {
        rayon::iter::once((qualified_name, module_spec))
            .chain(module_spec.submodule_specs.par_iter().flat_map(
                |(submodule_qualified_name, submodule_spec)| {
                    all_submodule_specs(submodule_qualified_name, submodule_spec)
                },
            ))
            .collect()
    }

    all_submodule_specs(qualified_name, module_spec)
        .into_par_iter()
        .map(|(qualified_name, module_spec)| (qualified_name, load_cfg(&module_spec)))
}

pub fn cfg_worklist<F: Filesystem>(
    module_specs: HashMap<QualifiedName, ModuleSpec<F>>,
    target_modules: HashSet<QualifiedName>,
) -> Option<(
    Namespaces<QualifiedName, AbstractEnvironment>,
    HashMap<Arc<QualifiedName>, Cfg>,
)> {
    let mut namespaces: Namespaces<QualifiedName, AbstractEnvironment> = Namespaces::new();
    let mut dependents: HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    > = HashMap::new();
    let mut cfgs: HashMap<_, _> = target_modules
        .par_iter()
        .flat_map(|qualified_name| {
            import_module_spec(qualified_name, module_specs.get(qualified_name).unwrap())
        })
        .map(|(qualified_name, cfg)| {
            (
                Arc::new(qualified_name.clone()),
                cfg.unwrap_or(Cfg::empty()),
            )
        })
        .collect();

    let mut cfg_worklist: HashSet<_> = cfgs
        .keys()
        .map(|module| NamespaceLocation::from(module.clone()))
        .collect();

    let module_specs_ref = &module_specs;
    while !cfg_worklist.is_empty() {
        let (import_tx, import_rx) = channel::<NamespaceLocation<QualifiedName>>();
        let (cfg_tx, cfg_rx) = channel::<(Arc<QualifiedName>, Cfg)>();

        let cfgs_ref = &cfgs;
        let namespaces_ref = &namespaces;

        let (override_namespaces, override_dependents) = rayon::scope(move |scope| {
            scope.spawn(move |scope| {
                let mut current_cfgs: HashSet<QualifiedName> = HashSet::new();

                for namespace_location in import_rx {
                    let root_package = QualifiedName {
                        identifiers: OneOrMany::one(
                            namespace_location.module.identifiers.first().clone(),
                        ),
                    };

                    if cfgs_ref.contains_key(&root_package) || current_cfgs.contains(&root_package)
                    {
                        continue;
                    }

                    let Some(module_spec) = module_specs_ref.get(&root_package) else {
                        continue;
                    };

                    current_cfgs.insert(root_package.clone());

                    let cfg_tx = cfg_tx.clone();
                    scope.spawn(move |_| {
                        let module_cfgs: Vec<_> = import_module_spec(&root_package, module_spec)
                            .map(|(qualified_name, cfg)| {
                                (
                                    Arc::new(qualified_name.clone()),
                                    cfg.unwrap_or(Cfg::empty()),
                                )
                            })
                            .collect();

                        for (qualified_name, cfg) in module_cfgs {
                            cfg_tx
                                .send((qualified_name, cfg))
                                .expect("Should be able to send imported cfg to main thread");
                        }
                    });
                }
            });

            let worklist_results = cfg_worklist
                .into_par_iter()
                .map(|namespace_location| {
                    let mut context = NamespacesProxy::new(namespaces_ref);
                    let mut dependents: HashMap<
                        NamespaceLocation<QualifiedName>,
                        HashSet<NamespaceLocation<QualifiedName>>,
                    > = HashMap::new();
                    worklist(&mut context, &mut dependents, &cfgs_ref, &import_tx, namespace_location.clone());

                    debug_assert!(
                        context
                            .override_namespaces
                            .locations
                            .contains_key(&namespace_location),
                        "Worklist {:?} should have computed an environment for the exit point of the module",
                        namespace_location
                    );
                    (context.override_namespaces, dependents)
                })
                .reduce(
                    || (Namespaces::new(), HashMap::new()),
                    |(mut acc_namespaces, mut acc_dependents),
                     (override_namespaces, override_dependents)| {
                        merge_with(
                            &mut acc_namespaces,
                            &mut acc_dependents,
                            override_namespaces,
                            override_dependents,
                        );
                        (acc_namespaces, acc_dependents)
                    });

            worklist_results
        });

        cfg_worklist = dependents
            .keys()
            .par_bridge()
            .flat_map(|dependent| {
                if let Some(dependents) = dependents.get(&dependent) {
                    dependents.iter().cloned().collect::<Vec<_>>()
                } else {
                    Vec::new()
                }
            })
            .collect();

        merge_with(
            &mut namespaces,
            &mut dependents,
            override_namespaces,
            override_dependents,
        );

        for (module, cfg) in cfg_rx {
            cfgs.insert(module.clone(), cfg);
            cfg_worklist.insert(NamespaceLocation::from(module));
        }

        cfg_worklist.retain(|namespace_location| {
            cfgs.contains_key(&namespace_location.module)
                && !namespaces.locations.contains_key(&namespace_location)
        });
    }

    Some((namespaces, cfgs))
}
