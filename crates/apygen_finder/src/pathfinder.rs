use crate::filesystem::{AbsolutePathBuf, Filesystem};
use rayon::prelude::*;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ffi::OsStr;
use std::hash::Hash;
use std::str::FromStr;
use std::sync::Arc;

pub const SOURCE_SUFFIX: &str = "py";
#[cfg(target_family = "windows")]
pub const EXTENSION_SUFFIX: &str = "pyd";
#[cfg(target_family = "unix")]
pub const EXTENSION_SUFFIX: &str = "so";

pub const INIT_FILE_PREFIX: &str = "__init__";

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
    pub submodule_search_locations: Vec<AbsolutePathBuf>,
}

impl<F: Filesystem> ModuleSpec<F> {
    pub fn new(file_loader: FileLoader<F>) -> Self {
        ModuleSpec {
            file_loader,
            submodule_search_locations: Vec::new(),
        }
    }

    pub fn with_one_location(file_loader: FileLoader<F>, location: AbsolutePathBuf) -> Self {
        ModuleSpec {
            file_loader,
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

pub struct FinderSpec<I: Clone + Eq + Hash + Send + FromStr, F: Filesystem> {
    pub module_spec: ModuleSpec<F>,
    pub submodules: HashMap<I, FinderSpec<I, F>>,
}

impl<I: Clone + Eq + Hash + Send + FromStr, F: Filesystem> FinderSpec<I, F> {
    pub fn new(module_spec: ModuleSpec<F>, submodules: HashMap<I, FinderSpec<I, F>>) -> Self {
        FinderSpec {
            module_spec,
            submodules,
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

    fn get_module_loader<I: Clone + Eq + Hash + Send + FromStr>(
        &self,
        candidate_module_path: &AbsolutePathBuf,
    ) -> Option<(I, FileLoader<F>)> {
        if !self.filesystem.is_file(candidate_module_path) {
            return None;
        }

        let file_prefix = candidate_module_path.file_prefix()?;

        if file_prefix == OsStr::new(INIT_FILE_PREFIX) {
            return None;
        }

        let identifier = I::from_str(file_prefix.to_str()?).ok()?;

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

    fn get_package_loader<I: Clone + Eq + Hash + Send + FromStr>(
        &self,
        candidate_package_path: &AbsolutePathBuf,
    ) -> Option<(I, FileLoader<F>)> {
        if !self.filesystem.is_dir(candidate_package_path) {
            return None;
        }

        let identifier = I::from_str(candidate_package_path.file_name()?.to_str()?).ok()?;

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

    fn get_search_locations_specs<
        'a,
        I: Clone + Eq + Hash + Send + FromStr,
        L: ParallelIterator<Item = &'a AbsolutePathBuf>,
    >(
        &self,
        search_locations: L,
    ) -> HashMap<I, FinderSpec<I, F>> {
        let module_specs: Vec<_> = search_locations
            .flat_map(
                |search_location| match self.filesystem.list_dir(search_location) {
                    Ok(candidate_paths) => candidate_paths.into_par_iter(),
                    Err(_) => Vec::new().into_par_iter(),
                },
            )
            .filter_map(|candidate_path| {
                if let Some((identifier, file_loader)) = self.get_module_loader(&candidate_path) {
                    Some((identifier, ModuleSpec::new(file_loader)))
                } else if let Some((identifier, file_loader)) =
                    self.get_package_loader(&candidate_path)
                {
                    Some((
                        identifier,
                        ModuleSpec::with_one_location(file_loader, candidate_path),
                    ))
                } else {
                    None
                }
            })
            .collect();

        let mut search_location_specs: HashMap<I, ModuleSpec<F>> = HashMap::new();
        for (identifier, module_spec) in module_specs {
            match search_location_specs.entry(identifier) {
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
            .filter_map(|(identifier, module_spec)| {
                let submodules = self
                    .get_search_locations_specs(module_spec.submodule_search_locations.par_iter());

                if matches!(module_spec.file_loader, FileLoader::NamespaceLoader)
                    && submodules.is_empty()
                {
                    return None;
                }

                Some((identifier, FinderSpec::new(module_spec, submodules)))
            })
            .collect()
    }

    pub fn get_all_specs<I: Clone + Eq + Hash + Send + FromStr>(
        &self,
    ) -> HashMap<I, FinderSpec<I, F>> {
        self.get_search_locations_specs(self.python_paths.par_iter())
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

        let module_specs: HashMap<String, _> = path_finder.get_all_specs();

        assert_eq!(
            module_specs.keys().collect::<HashSet<_>>(),
            HashSet::from([
                &"package".to_owned(),
                &"hello".to_owned(),
                &"calculator".to_owned(),
            ])
        );
        assert_eq!(
            module_specs[&"package".to_owned()]
                .submodules
                .keys()
                .collect::<HashSet<_>>(),
            HashSet::from([&"submodule".to_owned()])
        )
    }
}
