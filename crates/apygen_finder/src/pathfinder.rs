use crate::filesystem::{AbsolutePathBuf, Error, ErrorKind, Filesystem};
use rayon::prelude::*;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ffi::OsStr;
use std::hash::Hash;
use std::str::FromStr;
use std::sync::Arc;

const SOURCE_FILE_EXTENSION: &str = "py";
#[cfg(target_family = "windows")]
const EXTENSION_FILE_EXTENSION: &str = "pyd";
#[cfg(target_family = "unix")]
const EXTENSION_FILE_EXTENSION: &str = "so";
const STUB_FILE_EXTENSION: &str = "pyi";

const INIT_FILE_PREFIX: &str = "__init__";
const STUBS_SUFFIX: &str = "-stubs";

const PY_TYPED_FILE: &str = "py.typed";

fn is_inside<'a>(locations: &Vec<AbsolutePathBuf>, directory: &AbsolutePathBuf) -> bool {
    locations.iter().any(|path| path.starts_with(&directory))
}

fn join_ord<O: Ord>(left: O, right: O) -> O {
    if left > right { left } else { right }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Loader<F: Filesystem> {
    pub filesystem: Arc<F>,
    pub path: AbsolutePathBuf,
}

impl<F: Filesystem> Loader<F> {
    pub fn read_file(&self) -> Result<String, Error> {
        self.filesystem.read_file(&self.path)
    }

    pub fn list_dir(&self) -> Result<Vec<AbsolutePathBuf>, Error> {
        self.filesystem.list_dir(&self.path)
    }

    pub fn is_file(&self) -> bool {
        self.filesystem.is_file(&self.path)
    }

    pub fn is_dir(&self) -> bool {
        self.filesystem.is_dir(&self.path)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StubSpec<F: Filesystem> {
    pub file_loader: Loader<F>,
    pub submodule_search_locations: Vec<AbsolutePathBuf>,
}

impl<F: Filesystem> StubSpec<F> {
    pub fn is_inside(&self, directory: &AbsolutePathBuf) -> bool {
        self.file_loader.path.starts_with(directory)
            || is_inside(&self.submodule_search_locations, directory)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModuleKind {
    Source,
    Extension,
}

/// # References:
/// - [PEP 451 - A ModuleSpec Type for the Import System](https://peps.python.org/pep-0451/)
/// - [Importlib module - ModuleSpec](https://docs.python.org/3/library/importlib.html#importlib.machinery.ModuleSpec)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleSpec<F: Filesystem> {
    pub kind: ModuleKind,
    pub typed: bool,
    pub file_loader: Loader<F>,
    pub stub_spec: Option<StubSpec<F>>,
    pub submodule_search_locations: Vec<AbsolutePathBuf>,
}

impl<F: Filesystem> ModuleSpec<F> {
    pub fn is_inside(&self, directory: &AbsolutePathBuf) -> bool {
        self.file_loader.path.starts_with(directory)
            || is_inside(&self.submodule_search_locations, directory)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NamespaceSpec {
    pub submodule_search_locations: Vec<AbsolutePathBuf>,
}

impl NamespaceSpec {
    pub fn is_inside(&self, directory: &AbsolutePathBuf) -> bool {
        is_inside(&self.submodule_search_locations, directory)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Spec<F: Filesystem> {
    Module(ModuleSpec<F>),
    Stub(StubSpec<F>),
    Namespace(NamespaceSpec),
}

impl<F: Filesystem> Spec<F> {
    pub fn is_inside(&self, directory: &AbsolutePathBuf) -> bool {
        match self {
            Spec::Module(module_spec) => module_spec.is_inside(directory),
            Spec::Stub(stub_spec) => stub_spec.is_inside(directory),
            Spec::Namespace(namespace_spec) => namespace_spec.is_inside(directory),
        }
    }
}

/// # References:
/// - [Type Checker Module Resolution Order](https://peps.python.org/pep-0561/#type-checker-module-resolution-order)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
enum ResolutionOrder {
    TypeshedPackage,
    PyTypedPackage,
    StubPackage,
    UserPackage,
    ManualPackage,
}

impl ResolutionOrder {
    fn join(self, other: Self) -> Self {
        join_ord(self, other)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TypeStatus {
    NotTyped,
    Partial,
    Typed,
}

impl TypeStatus {
    fn is_typed(&self) -> bool {
        match self {
            TypeStatus::NotTyped => false,
            TypeStatus::Partial | TypeStatus::Typed => true,
        }
    }
}

impl TypeStatus {
    fn join(self, other: Self) -> Self {
        join_ord(self, other)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct StubSpecWithOrder<F: Filesystem> {
    order: ResolutionOrder,
    stub_only: bool,
    type_status: TypeStatus,
    file_loader: Loader<F>,
    submodule_search_locations: Vec<AbsolutePathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ModuleSpecWithOrder<F: Filesystem> {
    kind: ModuleKind,
    order: ResolutionOrder,
    type_status: TypeStatus,
    file_loader: Loader<F>,
    stub_spec_with_order: Option<StubSpecWithOrder<F>>,
    submodule_search_locations: Vec<AbsolutePathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct NamespaceSpecWithOrder {
    order: ResolutionOrder,
    stub_only: bool,
    type_status: TypeStatus,
    submodule_search_locations: Vec<AbsolutePathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SpecWithOrder<F: Filesystem> {
    Module(ModuleSpecWithOrder<F>),
    Stub(StubSpecWithOrder<F>),
    Namespace(NamespaceSpecWithOrder),
}

impl<F: Filesystem> Into<Spec<F>> for SpecWithOrder<F> {
    fn into(self) -> Spec<F> {
        match self {
            SpecWithOrder::Module(module_spec_with_order) => Spec::Module(ModuleSpec {
                kind: module_spec_with_order.kind,
                typed: module_spec_with_order.type_status.is_typed(),
                file_loader: module_spec_with_order.file_loader,
                stub_spec: module_spec_with_order.stub_spec_with_order.map(
                    |stub_spec_with_order| StubSpec {
                        file_loader: stub_spec_with_order.file_loader,
                        submodule_search_locations: stub_spec_with_order.submodule_search_locations,
                    },
                ),
                submodule_search_locations: module_spec_with_order.submodule_search_locations,
            }),
            SpecWithOrder::Stub(stub_spec_with_order) => Spec::Stub(StubSpec {
                file_loader: stub_spec_with_order.file_loader,
                submodule_search_locations: stub_spec_with_order.submodule_search_locations,
            }),
            SpecWithOrder::Namespace(namespace_spec_with_order) => Spec::Namespace(NamespaceSpec {
                submodule_search_locations: namespace_spec_with_order.submodule_search_locations,
            }),
        }
    }
}

pub struct FinderSpec<I: Clone + Eq + Hash + Send + FromStr, F: Filesystem> {
    pub spec: Spec<F>,
    pub submodules: HashMap<I, FinderSpec<I, F>>,
}

/// # References:
/// - [PEP 420 - Implicit Namespace Packages](https://peps.python.org/pep-0420/)
/// - [PEP 451 - A ModuleSpec Type for the Import System](https://peps.python.org/pep-0451/)
/// - [PEP 561 – Distributing and Packaging Type Information](https://peps.python.org/pep-0561/)
/// - [Import System - Searching](https://docs.python.org/3/reference/import.html#searching)
pub struct PathFinder<F: Filesystem> {
    filesystem: Arc<F>,
    python_paths: Vec<AbsolutePathBuf>,
    stubs_paths: Vec<AbsolutePathBuf>,
    working_directory: Option<AbsolutePathBuf>,
    typeshed_path: Option<AbsolutePathBuf>,
}

impl<F: Filesystem> PathFinder<F> {
    pub fn new(
        filesystem: Arc<F>,
        python_paths: Vec<AbsolutePathBuf>,
        stubs_paths: Vec<AbsolutePathBuf>,
        working_directory: Option<AbsolutePathBuf>,
        typeshed_path: Option<AbsolutePathBuf>,
    ) -> Self {
        Self {
            filesystem,
            python_paths,
            stubs_paths,
            working_directory,
            typeshed_path,
        }
    }

    pub fn filesystem(&self) -> &Arc<F> {
        &self.filesystem
    }

    pub fn python_paths(&self) -> &[AbsolutePathBuf] {
        &self.python_paths
    }

    pub fn stubs_paths(&self) -> &[AbsolutePathBuf] {
        &self.stubs_paths
    }

    pub fn working_directory(&self) -> Option<&AbsolutePathBuf> {
        self.working_directory.as_ref()
    }

    pub fn typeshed_path(&self) -> Option<&AbsolutePathBuf> {
        self.typeshed_path.as_ref()
    }

    fn get_type_status(
        &self,
        package_path: &AbsolutePathBuf,
        default: TypeStatus,
    ) -> Option<TypeStatus> {
        let py_typed_file_path = package_path.join(PY_TYPED_FILE);

        match self.filesystem.read_file(&py_typed_file_path) {
            Ok(data) => {
                if data.is_empty() {
                    Some(TypeStatus::Typed)
                } else if data == "partial\n" {
                    Some(TypeStatus::Partial)
                } else {
                    None
                }
            }
            Err(Error {
                kind: ErrorKind::NotFound,
                ..
            }) => Some(default),
            Err(_) => None,
        }
    }

    fn combine_specs(previous_spec: &mut SpecWithOrder<F>, new_spec: SpecWithOrder<F>) {
        match (&mut *previous_spec, new_spec) {
            (
                SpecWithOrder::Namespace(previous_namespace_spec),
                SpecWithOrder::Namespace(new_namespace_spec),
            ) => {
                previous_namespace_spec.order =
                    previous_namespace_spec.order.join(new_namespace_spec.order);
                previous_namespace_spec.stub_only =
                    previous_namespace_spec.stub_only && new_namespace_spec.stub_only;
                previous_namespace_spec
                    .submodule_search_locations
                    .extend(new_namespace_spec.submodule_search_locations);
            }
            (
                SpecWithOrder::Namespace(previous_namespace_spec),
                SpecWithOrder::Module(new_module_spec),
            ) => {
                if new_module_spec.order > previous_namespace_spec.order {
                    *previous_spec = SpecWithOrder::Module(new_module_spec)
                } else if previous_namespace_spec.type_status == TypeStatus::Partial {
                    *previous_spec = SpecWithOrder::Module(ModuleSpecWithOrder {
                        kind: new_module_spec.kind,
                        order: previous_namespace_spec.order,
                        type_status: previous_namespace_spec.type_status,
                        file_loader: new_module_spec.file_loader,
                        stub_spec_with_order: new_module_spec.stub_spec_with_order,
                        submodule_search_locations: previous_namespace_spec
                            .submodule_search_locations
                            .clone(),
                    });
                }
            }
            (
                SpecWithOrder::Module(previous_module_spec),
                SpecWithOrder::Namespace(new_namespace_spec),
            ) => {
                if new_namespace_spec.order > previous_module_spec.order {
                    if new_namespace_spec.type_status == TypeStatus::Partial {
                        previous_module_spec.order = new_namespace_spec.order;
                        previous_module_spec.type_status = new_namespace_spec.type_status;
                        previous_module_spec
                            .submodule_search_locations
                            .extend(new_namespace_spec.submodule_search_locations);
                    } else {
                        *previous_spec = SpecWithOrder::Namespace(new_namespace_spec);
                    }
                }
            }
            (
                SpecWithOrder::Namespace(previous_namespace_spec),
                SpecWithOrder::Stub(new_stub_spec),
            ) => {
                if new_stub_spec.order > previous_namespace_spec.order {
                    *previous_spec = SpecWithOrder::Stub(new_stub_spec)
                } else if previous_namespace_spec.type_status == TypeStatus::Partial {
                    *previous_spec = SpecWithOrder::Stub(StubSpecWithOrder {
                        order: previous_namespace_spec.order,
                        stub_only: previous_namespace_spec.stub_only && new_stub_spec.stub_only,
                        type_status: previous_namespace_spec.type_status,
                        file_loader: new_stub_spec.file_loader,
                        submodule_search_locations: previous_namespace_spec
                            .submodule_search_locations
                            .clone(),
                    });
                }
            }
            (
                SpecWithOrder::Stub(previous_stub_spec),
                SpecWithOrder::Namespace(new_namespace_spec),
            ) => {
                if new_namespace_spec.order > previous_stub_spec.order {
                    if new_namespace_spec.type_status == TypeStatus::Partial {
                        previous_stub_spec.order = new_namespace_spec.order;
                        previous_stub_spec.stub_only =
                            previous_stub_spec.stub_only && new_namespace_spec.stub_only;
                        previous_stub_spec.type_status = new_namespace_spec.type_status;
                        previous_stub_spec
                            .submodule_search_locations
                            .extend(new_namespace_spec.submodule_search_locations);
                    } else {
                        *previous_spec = SpecWithOrder::Namespace(new_namespace_spec);
                    }
                }
            }
            (SpecWithOrder::Module(previous_module_spec), SpecWithOrder::Stub(new_stub_spec)) => {
                if previous_module_spec.order <= new_stub_spec.order
                    || previous_module_spec.type_status == TypeStatus::NotTyped
                {
                    previous_module_spec.stub_spec_with_order = Some(new_stub_spec);
                }
            }
            (
                SpecWithOrder::Stub(previous_stub_spec),
                SpecWithOrder::Module(mut new_module_spec),
            ) => {
                if new_module_spec.order > previous_stub_spec.order
                    && new_module_spec.type_status != TypeStatus::NotTyped
                {
                    *previous_spec = SpecWithOrder::Module(new_module_spec);
                } else {
                    new_module_spec.stub_spec_with_order = Some(StubSpecWithOrder {
                        order: previous_stub_spec.order,
                        stub_only: previous_stub_spec.stub_only,
                        type_status: previous_stub_spec.type_status,
                        file_loader: Loader {
                            filesystem: previous_stub_spec.file_loader.filesystem.clone(),
                            path: previous_stub_spec.file_loader.path.clone(),
                        },
                        submodule_search_locations: previous_stub_spec
                            .submodule_search_locations
                            .clone(),
                    });
                    *previous_spec = SpecWithOrder::Module(new_module_spec);
                }
            }
            (SpecWithOrder::Stub(previous_stub_spec), SpecWithOrder::Stub(new_stub_spec)) => {
                if new_stub_spec.order > previous_stub_spec.order {
                    if new_stub_spec.type_status == TypeStatus::Partial {
                        previous_stub_spec.order = new_stub_spec.order;
                        previous_stub_spec.stub_only =
                            previous_stub_spec.stub_only && new_stub_spec.stub_only;
                        previous_stub_spec.type_status = new_stub_spec.type_status;
                        previous_stub_spec.file_loader = Loader {
                            filesystem: new_stub_spec.file_loader.filesystem.clone(),
                            path: new_stub_spec.file_loader.path.clone(),
                        };
                        previous_stub_spec
                            .submodule_search_locations
                            .extend(new_stub_spec.submodule_search_locations);
                    } else {
                        *previous_spec = SpecWithOrder::Stub(new_stub_spec);
                    }
                }
            }
            (SpecWithOrder::Module(_), SpecWithOrder::Module(_)) => {}
        }
    }

    fn get_module_spec<I: Clone + Eq + Hash + Send + FromStr>(
        &self,
        candidate_module_path: &AbsolutePathBuf,
        type_status: TypeStatus,
        order: ResolutionOrder,
        stub_only: bool,
    ) -> Option<(I, SpecWithOrder<F>)> {
        // Directories are handled in the get_package_loader method
        if !self.filesystem.is_file(candidate_module_path) {
            return None;
        }

        let file_prefix = candidate_module_path.file_prefix()?;

        // Init files are handled in the get_package_spec method
        if file_prefix == OsStr::new(INIT_FILE_PREFIX) {
            return None;
        }

        let identifier = I::from_str(file_prefix.to_str()?).ok()?;

        let extension = candidate_module_path.extension()?;

        let spec_with_order = if !stub_only && extension == OsStr::new(SOURCE_FILE_EXTENSION) {
            SpecWithOrder::Module(ModuleSpecWithOrder {
                kind: ModuleKind::Source,
                order,
                type_status,
                file_loader: Loader {
                    filesystem: self.filesystem.clone(),
                    path: candidate_module_path.to_owned(),
                },
                stub_spec_with_order: None,
                submodule_search_locations: Vec::new(),
            })
        } else if !stub_only && extension == OsStr::new(EXTENSION_FILE_EXTENSION) {
            SpecWithOrder::Module(ModuleSpecWithOrder {
                kind: ModuleKind::Extension,
                order,
                type_status,
                file_loader: Loader {
                    filesystem: self.filesystem.clone(),
                    path: candidate_module_path.to_owned(),
                },
                stub_spec_with_order: None,
                submodule_search_locations: Vec::new(),
            })
        } else if extension == OsStr::new(STUB_FILE_EXTENSION) {
            SpecWithOrder::Stub(StubSpecWithOrder {
                order,
                stub_only,
                type_status,
                file_loader: Loader {
                    filesystem: self.filesystem.clone(),
                    path: candidate_module_path.to_owned(),
                },
                submodule_search_locations: Vec::new(),
            })
        } else {
            return None;
        };

        Some((identifier, spec_with_order))
    }

    fn get_package_loader<I: Clone + Eq + Hash + Send + FromStr>(
        &self,
        candidate_package_path: &AbsolutePathBuf,
        mut type_status: TypeStatus,
        mut order: ResolutionOrder,
        mut stub_only: bool,
    ) -> Option<(I, SpecWithOrder<F>)> {
        // Files are handled in the get_module_spec method
        if !self.filesystem.is_dir(candidate_package_path) {
            return None;
        }

        let mut file_prefix = candidate_package_path.file_prefix()?.to_str()?;

        let mut default_type_status = TypeStatus::NotTyped;
        if let Some(stub_file_prefix) = file_prefix.strip_suffix(STUBS_SUFFIX) {
            file_prefix = stub_file_prefix;
            order = order.join(ResolutionOrder::StubPackage);
            stub_only = true;
            default_type_status = TypeStatus::Typed;
        }

        let identifier = I::from_str(file_prefix).ok()?;

        let init_file_path = candidate_package_path.join(INIT_FILE_PREFIX);
        let stub_init_file_path = init_file_path.with_extension(STUB_FILE_EXTENSION);

        type_status = type_status.join(
            self.get_type_status(candidate_package_path, default_type_status)
                .unwrap_or(default_type_status),
        );

        let stub_spec_with_order = if self.filesystem.is_file(&stub_init_file_path) {
            Some(StubSpecWithOrder {
                order,
                stub_only,
                type_status,
                file_loader: Loader {
                    filesystem: self.filesystem.clone(),
                    path: stub_init_file_path,
                },
                submodule_search_locations: Vec::new(),
            })
        } else {
            None
        };

        let source_init_file_path = init_file_path.with_extension(SOURCE_FILE_EXTENSION);
        let extension_init_file_path = init_file_path.with_extension(EXTENSION_FILE_EXTENSION);

        let spec_with_order = if !stub_only && self.filesystem.is_file(&source_init_file_path) {
            SpecWithOrder::Module(ModuleSpecWithOrder {
                kind: ModuleKind::Source,
                order,
                type_status,
                file_loader: Loader {
                    filesystem: self.filesystem.clone(),
                    path: source_init_file_path.to_owned(),
                },
                stub_spec_with_order,
                submodule_search_locations: vec![candidate_package_path.to_owned()],
            })
        } else if !stub_only && self.filesystem.is_file(&extension_init_file_path) {
            SpecWithOrder::Module(ModuleSpecWithOrder {
                kind: ModuleKind::Extension,
                order,
                type_status,
                file_loader: Loader {
                    filesystem: self.filesystem.clone(),
                    path: extension_init_file_path.to_owned(),
                },
                stub_spec_with_order,
                submodule_search_locations: vec![candidate_package_path.to_owned()],
            })
        } else if let Some(mut stub_spec) = stub_spec_with_order {
            stub_spec.submodule_search_locations = vec![candidate_package_path.to_owned()];
            SpecWithOrder::Stub(stub_spec)
        } else {
            SpecWithOrder::Namespace(NamespaceSpecWithOrder {
                order,
                stub_only,
                type_status,
                submodule_search_locations: vec![candidate_package_path.to_owned()],
            })
        };

        Some((identifier, spec_with_order))
    }

    fn get_submodule_search_locations_specs<'a, I: Clone + Eq + Hash + Send + FromStr>(
        &self,
        spec: &SpecWithOrder<F>,
    ) -> HashMap<I, FinderSpec<I, F>> {
        match spec {
            SpecWithOrder::Module(module_spec) => self.get_search_locations_specs(
                module_spec
                    .submodule_search_locations
                    .par_iter()
                    .chain(
                        module_spec
                            .stub_spec_with_order
                            .as_ref()
                            .map(|stub_spec| &stub_spec.submodule_search_locations)
                            .unwrap_or(&Vec::new()),
                    )
                    .map(|path| (path, module_spec.type_status, module_spec.order, false)),
            ),
            SpecWithOrder::Stub(stub_spec) => self.get_search_locations_specs(
                stub_spec.submodule_search_locations.par_iter().map(|path| {
                    (
                        path,
                        stub_spec.type_status,
                        stub_spec.order,
                        stub_spec.stub_only,
                    )
                }),
            ),
            SpecWithOrder::Namespace(namespace_spec) => self.get_search_locations_specs(
                namespace_spec
                    .submodule_search_locations
                    .par_iter()
                    .map(|path| {
                        (
                            path,
                            namespace_spec.type_status,
                            namespace_spec.order,
                            namespace_spec.stub_only,
                        )
                    }),
            ),
        }
    }

    fn get_search_locations_specs<
        'a,
        I: Clone + Eq + Hash + Send + FromStr,
        L: ParallelIterator<Item = (&'a AbsolutePathBuf, TypeStatus, ResolutionOrder, bool)>,
    >(
        &self,
        search_locations: L,
    ) -> HashMap<I, FinderSpec<I, F>> {
        let search_location_specs: Vec<_> = search_locations
            .flat_map(|(search_location, type_status, order, stub_only)| {
                self.filesystem
                    .list_dir(search_location)
                    .unwrap_or(Vec::new())
                    .into_par_iter()
                    .map(move |candidate_path| (candidate_path, type_status, order, stub_only))
            })
            .filter_map(|(candidate_path, type_status, order, stub_only)| {
                self.get_module_spec(&candidate_path, type_status, order, stub_only)
                    .or_else(|| {
                        self.get_package_loader(&candidate_path, type_status, order, stub_only)
                    })
            })
            .collect();

        let mut specs: HashMap<I, SpecWithOrder<F>> = HashMap::new();
        for (identifier, spec) in search_location_specs {
            match specs.entry(identifier) {
                Entry::Occupied(mut spec_entry) => {
                    Self::combine_specs(spec_entry.get_mut(), spec);
                }
                Entry::Vacant(entry) => {
                    entry.insert(spec);
                }
            }
        }

        specs
            .into_par_iter()
            .filter_map(|(identifier, spec)| {
                let submodules = self.get_submodule_search_locations_specs(&spec);

                if matches!(spec, SpecWithOrder::Namespace(..)) && submodules.is_empty() {
                    return None;
                }

                Some((
                    identifier,
                    FinderSpec {
                        spec: spec.into(),
                        submodules,
                    },
                ))
            })
            .collect()
    }

    pub fn get_specs<I: Clone + Eq + Hash + Send + FromStr>(&self) -> HashMap<I, FinderSpec<I, F>> {
        let stubs_locations = self.stubs_paths.par_iter().map(|stub_path| {
            (
                stub_path,
                self.get_type_status(stub_path, TypeStatus::Typed)
                    .unwrap_or(TypeStatus::Typed),
                ResolutionOrder::ManualPackage,
                false,
            )
        });
        let python_locations = self.python_paths.par_iter().map(|python_path| {
            if self
                .working_directory()
                .is_some_and(|working_directory| python_path.starts_with(working_directory))
            {
                (
                    python_path,
                    self.get_type_status(python_path, TypeStatus::Typed)
                        .unwrap_or(TypeStatus::Typed),
                    ResolutionOrder::UserPackage,
                    false,
                )
            } else {
                (
                    python_path,
                    self.get_type_status(python_path, TypeStatus::NotTyped)
                        .unwrap_or(TypeStatus::NotTyped),
                    ResolutionOrder::PyTypedPackage,
                    false,
                )
            }
        });
        let typeshed_locations = self.typeshed_path.par_iter().map(|typeshed_path| {
            (
                typeshed_path,
                TypeStatus::Typed,
                ResolutionOrder::TypeshedPackage,
                true,
            )
        });

        self.get_search_locations_specs(
            stubs_locations
                .chain(python_locations)
                .chain(typeshed_locations),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::filesystem::{Error, LocalFilesystem};
    use std::collections::HashSet;
    use std::path::PathBuf;

    fn modules_data_dir() -> Result<AbsolutePathBuf, Error> {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let absolute_manifest_dir = AbsolutePathBuf::try_from(manifest_dir)?;
        let data_dir = absolute_manifest_dir.try_join("tests/data/modules")?;
        Ok(data_dir)
    }

    fn new_path_finder() -> PathFinder<LocalFilesystem> {
        PathFinder::new(
            Arc::new(LocalFilesystem),
            vec![modules_data_dir().expect("Modules data directory should be an absolute path")],
            Vec::new(),
            None,
            None,
        )
    }

    #[test]
    fn test_list_modules() {
        let path_finder = new_path_finder();

        let module_specs: HashMap<String, _> = path_finder.get_specs();

        assert_eq!(
            module_specs
                .keys()
                .map(String::as_str)
                .collect::<HashSet<_>>(),
            HashSet::from(["package", "hello", "calculator",])
        );
        assert_eq!(
            module_specs["package"]
                .submodules
                .keys()
                .map(String::as_str)
                .collect::<HashSet<_>>(),
            HashSet::from(["submodule"])
        );
        assert!(module_specs["hello"].submodules.is_empty());
        assert!(module_specs["calculator"].submodules.is_empty());
    }
}
