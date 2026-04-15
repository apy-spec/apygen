use crate::filesystem::{AbsolutePathBuf, Filesystem};
pub use apy::OneOrMany;
pub use apy::v1::{Identifier, QualifiedName};
use rayon::prelude::*;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ffi::OsStr;
use std::sync::Arc;

const SOURCE_SUFFIX: &str = "py";
#[cfg(target_family = "windows")]
const EXTENSION_SUFFIX: &str = "pyd";
#[cfg(target_family = "unix")]
const EXTENSION_SUFFIX: &str = "so";

const INIT_FILE_PREFIX: &str = "__init__";

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FileLoader<F: Filesystem> {
    SourceFileLoader {
        filesystem: Arc<F>,
        path: AbsolutePathBuf,
    },
    ExtensionFileLoader {
        filesystem: Arc<F>,
        path: AbsolutePathBuf,
    },
    NamespaceLoader,
}

/// # References:
/// - [PEP 451 - A ModuleSpec Type for the Import System](https://peps.python.org/pep-0451/)
/// - [Importlib module - ModuleSpec](https://docs.python.org/3/library/importlib.html#importlib.machinery.ModuleSpec)
#[derive(Clone, Debug)]
pub struct ModuleSpec<F: Filesystem> {
    pub file_loader: FileLoader<F>,
    pub submodule_specs: HashMap<QualifiedName, ModuleSpec<F>>,
    pub submodule_search_locations: Vec<AbsolutePathBuf>,
}

impl<F: Filesystem> ModuleSpec<F> {
    pub fn new(file_loader: FileLoader<F>) -> Self {
        ModuleSpec {
            file_loader,
            submodule_specs: HashMap::new(),
            submodule_search_locations: Vec::new(),
        }
    }

    pub fn with_one_location(file_loader: FileLoader<F>, location: AbsolutePathBuf) -> Self {
        ModuleSpec {
            file_loader,
            submodule_specs: HashMap::new(),
            submodule_search_locations: Vec::from([location]),
        }
    }

    pub fn is_package(&self) -> bool {
        !self.submodule_search_locations.is_empty()
    }

    pub fn is_inside(&self, directory: &AbsolutePathBuf) -> bool {
        if self.is_package() {
            self.submodule_search_locations
                .iter()
                .any(|location| location.starts_with(directory))
        } else {
            match &self.file_loader {
                FileLoader::SourceFileLoader { path, .. } => path.starts_with(directory),
                FileLoader::ExtensionFileLoader { path, .. } => path.starts_with(directory),
                FileLoader::NamespaceLoader => false,
            }
        }
    }
}

/// # References:
/// - [PEP 420 - Implicit Namespace Packages](https://peps.python.org/pep-0420/)
/// - [PEP 451 - A ModuleSpec Type for the Import System](https://peps.python.org/pep-0451/)
/// - [Import System - Searching](https://docs.python.org/3/reference/import.html#searching)
pub struct PathFinder<F: Filesystem> {
    filesystem: Arc<F>,
    python_paths: Vec<AbsolutePathBuf>,
}

impl<F: Filesystem> PathFinder<F> {
    pub fn new(filesystem: Arc<F>, python_paths: Vec<AbsolutePathBuf>) -> Self {
        Self {
            filesystem,
            python_paths,
        }
    }

    pub fn filesystem(&self) -> &Arc<F> {
        &self.filesystem
    }

    pub fn python_paths(&self) -> &[AbsolutePathBuf] {
        &self.python_paths
    }

    fn get_qualified_name(
        package_identifiers: &[Identifier],
        identifier: Identifier,
    ) -> QualifiedName {
        let identifiers = if let Ok(mut identifiers) =
            OneOrMany::try_from_iter(package_identifiers.iter().cloned())
        {
            identifiers.push(identifier);
            identifiers
        } else {
            OneOrMany::one(identifier)
        };

        QualifiedName::new(identifiers)
    }

    fn get_module_loader(
        &self,
        candidate_module_path: &AbsolutePathBuf,
    ) -> Option<(Identifier, FileLoader<F>)> {
        if !self.filesystem.is_file(candidate_module_path) {
            return None;
        }

        let file_prefix = candidate_module_path.file_prefix()?;

        if file_prefix == OsStr::new(INIT_FILE_PREFIX) {
            return None;
        }

        let identifier = Identifier::try_parse(file_prefix.to_str()?).ok()?;

        let extension = candidate_module_path.extension()?;

        let file_loader = if extension == OsStr::new(SOURCE_SUFFIX) {
            FileLoader::SourceFileLoader {
                filesystem: self.filesystem.clone(),
                path: candidate_module_path.to_owned(),
            }
        } else if extension == OsStr::new(EXTENSION_SUFFIX) {
            FileLoader::ExtensionFileLoader {
                filesystem: self.filesystem.clone(),
                path: candidate_module_path.to_owned(),
            }
        } else {
            return None;
        };

        Some((identifier, file_loader))
    }

    fn get_package_loader(
        &self,
        candidate_package_path: &AbsolutePathBuf,
    ) -> Option<(Identifier, FileLoader<F>)> {
        if !self.filesystem.is_dir(candidate_package_path) {
            return None;
        }

        let identifier =
            Identifier::try_parse(candidate_package_path.file_name()?.to_str()?).ok()?;

        let init_file_path = candidate_package_path
            .try_join(INIT_FILE_PREFIX)
            .expect("Joining __init__ to package path should always create an absolute path");
        let source_init_file_path = init_file_path
            .try_with_extension(SOURCE_SUFFIX)
            .expect("Adding a .py extension should always create an absolute path");
        let extension_init_file_path = init_file_path
            .try_with_extension(EXTENSION_SUFFIX)
            .expect("Adding a .pyd or .so extension should always create an absolute path");

        let file_loader = if self.filesystem.is_file(&source_init_file_path) {
            FileLoader::SourceFileLoader {
                filesystem: self.filesystem.clone(),
                path: source_init_file_path,
            }
        } else if self.filesystem.is_file(&extension_init_file_path) {
            FileLoader::ExtensionFileLoader {
                filesystem: self.filesystem.clone(),
                path: extension_init_file_path,
            }
        } else {
            FileLoader::NamespaceLoader
        };

        Some((identifier, file_loader))
    }

    fn get_submodule_specs(
        &self,
        qualified_name: &QualifiedName,
        module_spec: &ModuleSpec<F>,
    ) -> HashMap<QualifiedName, ModuleSpec<F>> {
        let mut search_location_specs: HashMap<QualifiedName, ModuleSpec<F>> = HashMap::new();

        for (submodule_qualified_name, submodule_spec) in self.get_search_locations_specs(
            &qualified_name.identifiers,
            module_spec.submodule_search_locations.par_iter(),
        ) {
            search_location_specs
                .entry(submodule_qualified_name)
                .or_insert(submodule_spec);
        }

        search_location_specs
    }

    fn get_search_locations_specs<'a, I: ParallelIterator<Item = &'a AbsolutePathBuf>>(
        &self,
        package_identifiers: &[Identifier],
        search_locations: I,
    ) -> HashMap<QualifiedName, ModuleSpec<F>> {
        let module_specs: Vec<_> = search_locations
            .flat_map(
                |search_location| match self.filesystem.list_dir(search_location) {
                    Ok(candidate_paths) => candidate_paths.into_par_iter(),
                    Err(_) => Vec::new().into_par_iter(),
                },
            )
            .filter_map(|candidate_path| {
                let (identifier, module_spec) = if let Some((identifier, file_loader)) =
                    self.get_module_loader(&candidate_path)
                {
                    (identifier, ModuleSpec::new(file_loader))
                } else if let Some((identifier, file_loader)) =
                    self.get_package_loader(&candidate_path)
                {
                    (
                        identifier,
                        ModuleSpec::with_one_location(file_loader, candidate_path),
                    )
                } else {
                    return None;
                };

                let qualified_name = Self::get_qualified_name(package_identifiers, identifier);

                Some((qualified_name, module_spec))
            })
            .collect();

        let mut search_location_specs: HashMap<QualifiedName, ModuleSpec<F>> = HashMap::new();
        for (qualified_name, module_spec) in module_specs {
            match search_location_specs.entry(qualified_name) {
                Entry::Occupied(mut spec_entry) => {
                    let previous_spec = spec_entry.get_mut();

                    if !matches!(previous_spec.file_loader, FileLoader::NamespaceLoader) {
                        continue;
                    }

                    if matches!(module_spec.file_loader, FileLoader::NamespaceLoader) {
                        previous_spec
                            .submodule_search_locations
                            .extend(module_spec.submodule_search_locations);
                    } else {
                        previous_spec.file_loader = module_spec.file_loader;
                        previous_spec.submodule_search_locations =
                            module_spec.submodule_search_locations;
                    }
                }
                Entry::Vacant(entry) => {
                    entry.insert(module_spec);
                }
            }
        }

        search_location_specs
            .into_par_iter()
            .filter_map(|(qualified_name, mut module_spec)| {
                module_spec.submodule_specs =
                    self.get_submodule_specs(&qualified_name, &module_spec);

                if matches!(module_spec.file_loader, FileLoader::NamespaceLoader)
                    && module_spec.submodule_specs.is_empty()
                {
                    return None;
                }

                Some((qualified_name, module_spec))
            })
            .collect()
    }

    pub fn get_all_specs(&self) -> HashMap<QualifiedName, ModuleSpec<F>> {
        self.get_search_locations_specs(&[], self.python_paths.par_iter())
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
        )
    }

    #[test]
    fn test_list_modules() {
        let path_finder = new_path_finder();

        let module_specs = path_finder.get_all_specs();

        assert_eq!(
            module_specs.keys().collect::<HashSet<&QualifiedName>>(),
            HashSet::from([
                &QualifiedName::try_from("package").expect("package should be a valid identifier"),
                &QualifiedName::try_from("package.submodule")
                    .expect("package.submodule should be a valid submodule"),
                &QualifiedName::try_from("hello").expect("hello should be a valid identifier"),
                &QualifiedName::try_from("calculator")
                    .expect("calculator should be a valid identifier"),
            ])
        );
    }
}
