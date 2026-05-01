use crate::abstract_environment::{AbstractEnvironment, BUILTINS_MODULE, Type, TypeUnion};
use crate::genkill::statements::gen_statement;
use apy::OneOrMany;
use apy::v1::{Identifier, QualifiedName};
use apygen_analysis::cfg::{Cfg, EdgeData, NodeData, ProgramPoint};
pub use apygen_analysis::lattice::Lattice;
use apygen_analysis::namespace::{
    Location, NamespaceLocation, NamespaceLocations, NamespaceLocationsProxy, Namespaces,
};
use apygen_finder::filesystem::{Error as FilesystemError, Filesystem};
use apygen_finder::pathfinder::{FinderSpec, ModuleKind, ModuleSpec, Spec, StubSpec};
use log::{debug, info};
use rayon::iter::once;
use rayon::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;
use std::sync::mpsc::{Sender, channel};
use thiserror::Error;

pub type Dependents = HashSet<NamespaceLocation<QualifiedName>>;
pub type Arguments = HashMap<Arc<Identifier>, Arc<Type>>;
pub struct WorklistContext<
    'a,
    N: Namespaces<QualifiedName, AbstractEnvironment> = NamespaceLocationsProxy<
        'a,
        QualifiedName,
        AbstractEnvironment,
    >,
> {
    pub namespaces: N,
    pub dependents: HashMap<NamespaceLocation<QualifiedName>, Dependents>,
    pub calls: HashMap<NamespaceLocation<QualifiedName>, Arguments>,
    pub cfgs: &'a HashMap<Arc<QualifiedName>, Cfg>,
    pub import_tx: &'a Sender<NamespaceLocation<QualifiedName>>,
}

impl<N: Namespaces<QualifiedName, AbstractEnvironment>> WorklistContext<'_, N> {
    pub fn clone_abstract_environment(
        &self,
        location: &Location<QualifiedName>,
    ) -> AbstractEnvironment {
        self.namespaces
            .get_abstract_environment(&location)
            .cloned()
            .unwrap_or_default()
    }
}

pub fn worklist(
    context: &mut WorklistContext,
    namespace_location: NamespaceLocation<QualifiedName>,
) {
    context
        .namespaces
        .reset_abstract_environments(&namespace_location);

    let cfg = context
        .cfgs
        .get(&namespace_location.module)
        .map(|module_cfg| namespace_location.resolve(module_cfg))
        .flatten()
        .expect("Should exist since worklist is only called on modules in the project data");

    let mut worklist: BTreeSet<ProgramPoint> = BTreeSet::from_iter([ProgramPoint::Entry]);
    while let Some(program_point) = worklist.pop_first() {
        let location = Location {
            namespace_location: namespace_location.clone(),
            program_point,
        };

        let res_abstract_environments =
            if let Some(NodeData::Statement(statement_data)) = cfg.node_data(&program_point) {
                gen_statement(context, location, statement_data.statement()).unwrap()
            } else {
                HashMap::from_iter([(EdgeData::Unconditional, AbstractEnvironment::default())])
            };

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
                    let new_successor_environment = match context
                        .namespaces
                        .get_abstract_environment(&successor_location)
                    {
                        Some(successor_environment) => {
                            if successor_environment
                                .includes(&context.namespaces, res_abstract_environment)
                                .unwrap()
                            {
                                continue;
                            }
                            successor_environment
                                .join(&context.namespaces, res_abstract_environment)
                                .unwrap()
                        }
                        None => res_abstract_environment.clone(),
                    };

                    context
                        .namespaces
                        .abstract_environment_entry(successor_location.clone())
                        .insert_entry(new_successor_environment);

                    worklist.insert(successor);
                }
            }
        }
    }

    context
        .namespaces
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

pub fn cfg_worklist<'a, F: Filesystem>(
    specs: HashMap<Identifier, FinderSpec<Identifier, F>>,
    target_modules: &HashSet<Identifier>,
) -> Option<(
    NamespaceLocations<QualifiedName, AbstractEnvironment>,
    HashMap<Arc<QualifiedName>, Cfg>,
)> {
    let module_specs = convert_specs(specs);

    let mut namespaces: NamespaceLocations<QualifiedName, AbstractEnvironment> =
        NamespaceLocations::new();
    let mut dependents: HashMap<
        NamespaceLocation<QualifiedName>,
        HashSet<NamespaceLocation<QualifiedName>>,
    > = HashMap::new();
    let mut calls: HashMap<NamespaceLocation<QualifiedName>, HashMap<Arc<Identifier>, Arc<Type>>> =
        HashMap::new();

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

        let (cfg_tx, cfg_rx) = channel::<(Arc<QualifiedName>, Cfg)>();
        let mut calls_changed: HashSet<NamespaceLocation<QualifiedName>> = HashSet::new();

        let cfgs_ref = &cfgs;
        let namespaces_ref = &namespaces;
        let dependents_ref = &mut dependents;
        let calls_ref = &mut calls;
        let calls_changed_ref = &mut calls_changed;

        let changed_locations = rayon::scope(move |scope| {
            let (import_tx, import_rx) = channel::<NamespaceLocation<QualifiedName>>();

            scope.spawn(move |scope| {
                let mut current_cfgs: HashSet<Identifier> = HashSet::new();

                for namespace_location in import_rx {
                    let root_package =
                        QualifiedName::from(namespace_location.module.identifiers.first().clone());

                    if cfgs_ref.contains_key(&root_package)
                        || current_cfgs.contains(root_package.identifiers.first())
                    {
                        continue;
                    }

                    let Some(package_specs) =
                        module_specs_ref.get(root_package.identifiers.first())
                    else {
                        continue;
                    };

                    current_cfgs.insert(root_package.identifiers.first().clone());

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

                debug!(
                    "Finished importing the cfgs (after {:?})",
                    iteration_start.elapsed()
                );
            });

            debug!("Spawned import job (after {:?})", iteration_start.elapsed());

            let (changed, worker_dependents): (Vec<_>, Vec<_>) = cfg_worklist
                .into_par_iter()
                .map(|namespace_location| {
                    let mut context = WorklistContext {
                        namespaces: NamespaceLocationsProxy::new(&namespaces_ref),
                        dependents: HashMap::new(),
                        calls: HashMap::new(),
                        cfgs: cfgs_ref,
                        import_tx: &import_tx,
                    };

                    worklist(&mut context, namespace_location.clone());

                    let namespace = context
                        .namespaces
                        .override_namespaces
                        .locations
                        .remove(&namespace_location)
                        .expect("Worklist should have computed this namespace");

                    debug_assert!(
                        context.namespaces.override_namespaces.locations.is_empty(),
                        "Worklist should only compute the namespace for the given location",
                    );

                    if namespace_location.module.identifiers.first() != BUILTINS_MODULE
                        || namespace_location.module.identifiers.len() != 1
                    {
                        context
                            .dependents
                            .entry(NamespaceLocation::new(Arc::new(QualifiedName::parse(
                                BUILTINS_MODULE,
                            ))))
                            .or_default()
                            .insert(namespace_location.clone());
                    }

                    (
                        (namespace_location, namespace),
                        (context.dependents, context.calls),
                    )
                })
                .unzip();

            drop(import_tx);

            debug!(
                "Analysed the namespaces (after {:?})",
                iteration_start.elapsed()
            );

            scope.spawn(move |_| {
                for (new_dependents, new_calls) in worker_dependents {
                    for (from, tos) in new_dependents {
                        match dependents_ref.entry(from) {
                            Entry::Occupied(mut entry) => {
                                entry.get_mut().extend(tos);
                            }
                            Entry::Vacant(entry) => {
                                entry.insert(tos);
                            }
                        }
                    }
                    for (namespace_location, arguments) in new_calls {
                        let mut call_changed = false;

                        match calls_ref.entry(namespace_location.clone()) {
                            Entry::Occupied(mut entry) => {
                                let existing_arguments = entry.get_mut();
                                for (argument_name, argument_type) in arguments {
                                    match existing_arguments.entry(argument_name.clone()) {
                                        Entry::Occupied(mut entry) => {
                                            let existing_argument_type = entry.get_mut();

                                            if !existing_argument_type
                                                .includes(namespaces_ref, &argument_type)
                                                .is_ok_and(|included| included)
                                            {
                                                call_changed = true;
                                                *existing_argument_type = {
                                                    let mut new_argument_type = TypeUnion::new();
                                                    new_argument_type
                                                        .add_type(existing_argument_type.clone());
                                                    new_argument_type.add_type(argument_type);
                                                    new_argument_type.simplify()
                                                };
                                            }
                                        }
                                        Entry::Vacant(entry) => {
                                            call_changed = true;
                                            entry.insert(argument_type);
                                        }
                                    }
                                }
                            }
                            Entry::Vacant(entry) => {
                                entry.insert(arguments);
                                call_changed = true;
                            }
                        }

                        if call_changed {
                            calls_changed_ref.insert(namespace_location);
                        }
                    }
                }
            });

            debug!(
                "Spawned dependencies merge job (after {:?})",
                iteration_start.elapsed()
            );

            let changed_locations: Vec<_> = changed
                .into_par_iter()
                .filter_map(|(location, namespace)| {
                    if let Some(existing_namespace) = namespaces_ref.locations.get(&location) {
                        if existing_namespace.environments != namespace.environments {
                            Some((location, namespace))
                        } else {
                            None
                        }
                    } else {
                        Some((location, namespace))
                    }
                })
                .collect();

            debug!(
                "Collected the changed locations (after {:?})",
                iteration_start.elapsed()
            );

            changed_locations
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

        cfg_worklist = changed_locations
            .par_iter()
            .flat_map(|(namespace_location, _)| {
                once(namespace_location)
                    .chain(dependents.get(namespace_location).into_par_iter().flatten())
                    .filter(|namespace_location| cfgs.contains_key(&namespace_location.module))
            })
            .cloned()
            .chain(calls_changed)
            .collect();

        namespaces.locations.extend(changed_locations);

        cfg_worklist.extend(
            cfgs.keys()
                .map(|module| NamespaceLocation::new(module.clone()))
                .filter(|module| !namespaces.locations.contains_key(module)),
        );

        debug!(
            "Created the new worklist (after {:?})",
            iteration_start.elapsed()
        );
    }

    Some((namespaces, cfgs))
}
