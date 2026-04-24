use crate::abstract_environment::{AbstractEnvironment, BUILTINS_MODULE};
use crate::genkill::statements::gen_statement;
use apy::OneOrMany;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::cfg::{Cfg, EdgeData, NodeData, ProgramPoint};
pub use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::{
    Location, NamespaceLocation, Namespaces, NamespacesContext, NamespacesProxy,
};
use apygen_finder::filesystem::{Error as FilesystemError, Filesystem};
use apygen_finder::pathfinder::{FinderSpec, ModuleKind, ModuleSpec, Spec, StubSpec};
use log::{debug, info};
use rayon::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::mpsc::{Sender, channel};
use thiserror::Error;

pub struct WorklistResult {
    pub namespaces: Namespaces<QualifiedName, AbstractEnvironment>,
    pub dependents:
        HashMap<NamespaceLocation<QualifiedName>, HashSet<NamespaceLocation<QualifiedName>>>,
}

fn merge_dependents_with(
    left: &mut HashMap<NamespaceLocation<QualifiedName>, HashSet<NamespaceLocation<QualifiedName>>>,
    right: HashMap<NamespaceLocation<QualifiedName>, HashSet<NamespaceLocation<QualifiedName>>>,
) {
    for (from, tos) in right {
        match left.entry(from) {
            Entry::Occupied(mut entry) => {
                entry.get_mut().extend(tos);
            }
            Entry::Vacant(entry) => {
                entry.insert(tos);
            }
        }
    }
}

pub fn merge(mut left: WorklistResult, right: WorklistResult) -> WorklistResult {
    merge_dependents_with(&mut left.dependents, right.dependents);

    for (location, namespace) in right.namespaces.locations {
        match left.namespaces.locations.entry(location) {
            Entry::Occupied(_) => {
                panic!("Namespaces should not have overlapping locations");
            }
            Entry::Vacant(entry) => {
                entry.insert(namespace);
            }
        }
    }

    left
}

pub fn merge_with(
    namespaces: &mut Namespaces<QualifiedName, AbstractEnvironment>,
    dependents: &mut HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    >,
    cfgs: &HashMap<Arc<QualifiedName>, Cfg>,
    worklist_result: WorklistResult,
) -> HashSet<NamespaceLocation<QualifiedName>> {
    let mut changed: HashSet<NamespaceLocation<QualifiedName>> = HashSet::new();

    merge_dependents_with(dependents, worklist_result.dependents);

    changed.extend(
        cfgs.keys()
            .map(|module| NamespaceLocation::new(module.clone()))
            .chain(
                dependents
                    .keys()
                    .filter(|namespace_location| cfgs.contains_key(&namespace_location.module))
                    .cloned(),
            )
            .filter(|module| !namespaces.locations.contains_key(module)),
    );

    for (location, namespace) in worklist_result.namespaces.locations {
        let namespace_changed = match namespaces.locations.entry(location.clone()) {
            Entry::Occupied(mut entry) => {
                let occupied_namespace = entry.get_mut();
                if occupied_namespace.environments != namespace.environments {
                    *occupied_namespace = namespace;
                    true
                } else {
                    false
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(namespace);
                true
            }
        };

        if namespace_changed {
            if let Some(location_dependents) = dependents.get(&location) {
                changed.extend(
                    location_dependents
                        .iter()
                        .filter(|namespace_location| cfgs.contains_key(&namespace_location.module))
                        .cloned(),
                );
            }
            changed.insert(location);
        }
    }

    let changed_dependants = changed
        .par_iter()
        .filter_map(|namespace_location| dependents.get(namespace_location))
        .flatten()
        .filter(|namespace_location| namespaces.locations.contains_key(namespace_location))
        .collect::<HashSet<_>>();

    changed.retain(|namespace_location| !changed_dependants.contains(namespace_location));

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
        .map(|module_cfg| namespace_location.resolve(module_cfg))
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

                let res_abstract_environments = if let Some(NodeData::Statement(statement_data)) =
                    cfg.node_data(&program_point)
                {
                    gen_statement(
                        context,
                        dependents,
                        cfgs,
                        import_tx,
                        location,
                        statement_data.statement(),
                    )
                    .unwrap()
                } else {
                    HashMap::from_iter([(EdgeData::Unconditional, AbstractEnvironment::default())])
                };

                let mut worklist: HashSet<ProgramPoint> = HashSet::new();
                for successor in cfg.successors(&program_point).unwrap().cloned() {
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

    context
        .abstract_environment_entry(Location {
            namespace_location: namespace_location.clone(),
            program_point: ProgramPoint::Exit,
        })
        .or_default();
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

pub fn load_cfg(spec: &Spec<impl Filesystem>) -> Result<Cfg, ImportModuleError> {
    match spec {
        Spec::Module(ModuleSpec {
            kind: ModuleKind::Source,
            file_loader,
            ..
        })
        | Spec::Module(ModuleSpec {
            kind: ModuleKind::Extension,
            stub_spec: Some(StubSpec { file_loader, .. }),
            ..
        })
        | Spec::Stub(StubSpec { file_loader, .. }) => {
            let source = file_loader.read_file()?;
            Ok(Cfg::parse(&source).ok_or_else(|| ImportModuleError::CfgParseError(source))?)
        }
        _ => Err(ImportModuleError::NonSourceFileLoader),
    }
}

pub fn convert_specs<F: Filesystem>(
    specs: HashMap<Identifier, FinderSpec<Identifier, F>>,
) -> HashMap<Identifier, HashMap<QualifiedName, Spec<F>>> {
    pub fn convert_package_specs<F: Filesystem>(
        package_identifiers: OneOrMany<Identifier>,
        finder_spec: FinderSpec<Identifier, F>,
    ) -> HashMap<QualifiedName, Spec<F>> {
        rayon::iter::once((
            QualifiedName::new(package_identifiers.clone()),
            finder_spec.spec,
        ))
        .chain(finder_spec.submodules.into_par_iter().flat_map(
            |(submodule_identifier, submodule_spec)| {
                let mut submodule_identifiers = package_identifiers.clone();
                submodule_identifiers.push(submodule_identifier);
                convert_package_specs(submodule_identifiers, submodule_spec)
            },
        ))
        .collect()
    }

    specs
        .into_par_iter()
        .map(|(identifier, finder_spec)| {
            (
                identifier.clone(),
                convert_package_specs(OneOrMany::one(identifier), finder_spec),
            )
        })
        .collect()
}

pub fn cfg_worklist<F: Filesystem>(
    specs: HashMap<Identifier, FinderSpec<Identifier, F>>,
    target_modules: &HashSet<Identifier>,
) -> Option<(
    Namespaces<QualifiedName, AbstractEnvironment>,
    HashMap<Arc<QualifiedName>, Cfg>,
)> {
    let module_specs = convert_specs(specs);

    let mut namespaces: Namespaces<QualifiedName, AbstractEnvironment> = Namespaces::new();
    let mut dependents: HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    > = HashMap::new();
    let mut cfgs: HashMap<_, _> = target_modules
        .par_iter()
        .flat_map(|identifier| {
            module_specs[identifier]
                .par_iter()
                .map(|(name, module_spec)| {
                    (
                        Arc::new(name.clone()),
                        load_cfg(module_spec).unwrap_or(Cfg::empty()),
                    )
                })
        })
        .chain(
            module_specs[&Identifier::parse(BUILTINS_MODULE)]
                .par_iter()
                .map(|(name, module_spec)| {
                    (
                        Arc::new(name.clone()),
                        load_cfg(module_spec).unwrap_or(Cfg::empty()),
                    )
                }),
        )
        .collect();

    let mut cfg_worklist: HashSet<_> = cfgs
        .keys()
        .map(|module| NamespaceLocation::from(module.clone()))
        .collect();

    let module_specs_ref = &module_specs;
    let mut iteration: usize = 0;
    while !cfg_worklist.is_empty() {
        iteration += 1;
        info!(
            "Iteration {iteration} (Worklist size: {})",
            cfg_worklist.len()
        );
        let iteration_start = std::time::Instant::now();

        let (import_tx, import_rx) = channel::<NamespaceLocation<QualifiedName>>();
        let (cfg_tx, cfg_rx) = channel::<(Arc<QualifiedName>, Cfg)>();

        let cfgs_ref = &cfgs;
        let namespaces_ref = &namespaces;

        let override_result = rayon::scope(move |scope| {
            scope.spawn(move |scope| {
                let mut current_cfgs: HashSet<QualifiedName> = HashSet::new();

                for namespace_location in import_rx {
                    let root_package =
                        QualifiedName::from(namespace_location.module.identifiers.first().clone());

                    if cfgs_ref.contains_key(&root_package) || current_cfgs.contains(&root_package)
                    {
                        continue;
                    }

                    let Some(package_specs) =
                        module_specs_ref.get(root_package.identifiers.first())
                    else {
                        continue;
                    };

                    current_cfgs.insert(root_package.clone());

                    let cfg_tx = cfg_tx.clone();
                    scope.spawn(move |_| {
                        package_specs
                            .par_iter()
                            .map(|(name, module_spec)| {
                                (
                                    Arc::new(name.clone()),
                                    load_cfg(module_spec).unwrap_or(Cfg::empty()),
                                )
                            })
                            .for_each(|(qualified_name, cfg)| {
                                cfg_tx
                                    .send((qualified_name, cfg))
                                    .expect("Should be able to send imported cfg to main thread");
                            });
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

                    WorklistResult {
                        namespaces: context.override_namespaces,
                        dependents,
                    }
                })
                .reduce(
                    || WorklistResult {
                        namespaces: Namespaces::new(),
                        dependents: HashMap::new(),
                    },
                    merge);

            debug!(
                "Processed the worklists in workers (after {:?})",
                iteration_start.elapsed()
            );

            worklist_results
        });

        debug!(
            "Waited for the workers to finish (after {:?})",
            iteration_start.elapsed()
        );

        cfgs.extend(cfg_rx);

        debug!(
            "Collected and merged the new cfgs (after {:?})",
            iteration_start.elapsed()
        );

        cfg_worklist = merge_with(&mut namespaces, &mut dependents, &cfgs, override_result);

        debug!(
            "Created the new worklist (after {:?})",
            iteration_start.elapsed()
        );
    }

    Some((namespaces, cfgs))
}
