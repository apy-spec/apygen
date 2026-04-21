use std::ffi::OsStr;
use std::fmt::Display;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use thiserror::Error;

#[derive(Debug, PartialEq, Eq)]
pub enum ErrorKind {
    ReadError,
    NotFound,
    PermissionDenied,
    NotADirectory,
    IsADirectory,
    Unknown,
    IsNotAbsolutePath,
}

#[derive(Debug, PartialEq, Eq, Error)]
#[error("{kind:?}: {message}")]
pub struct Error {
    pub kind: ErrorKind,
    pub message: String,
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error {
            kind: match err.kind() {
                std::io::ErrorKind::NotFound => ErrorKind::NotFound,
                std::io::ErrorKind::PermissionDenied => ErrorKind::PermissionDenied,
                std::io::ErrorKind::NotADirectory => ErrorKind::NotADirectory,
                std::io::ErrorKind::IsADirectory => ErrorKind::IsADirectory,
                std::io::ErrorKind::InvalidData => ErrorKind::ReadError,
                std::io::ErrorKind::UnexpectedEof => ErrorKind::ReadError,
                _ => ErrorKind::Unknown,
            },
            message: err.to_string(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct AbsolutePathBuf {
    // Invariant: inner should always be an absolute path
    inner: PathBuf,
}

impl AbsolutePathBuf {
    pub fn current_dir() -> Result<Self, Error> {
        Self::try_from(std::env::current_dir()?)
    }

    pub fn join<P: AsRef<Path>>(&self, path: P) -> Self {
        self.try_join(path)
            .expect("Joining should never fail if the path is valid and absolute")
    }

    pub fn try_join<P: AsRef<Path>>(&self, path: P) -> Result<Self, Error> {
        Self::try_from(self.inner.join(path))
    }

    pub fn with_extension<S: AsRef<OsStr>>(&self, extension: S) -> Self {
        self.try_with_extension(extension)
            .expect("Changing extension should never fail if the path is valid and absolute")
    }

    pub fn try_with_extension<S: AsRef<OsStr>>(&self, extension: S) -> Result<Self, Error> {
        Self::try_from(self.inner.with_extension(extension))
    }
}

impl TryFrom<PathBuf> for AbsolutePathBuf {
    type Error = Error;

    fn try_from(value: PathBuf) -> Result<Self, Self::Error> {
        if value.is_absolute() {
            Ok(AbsolutePathBuf { inner: value })
        } else {
            Err(Error {
                kind: ErrorKind::IsNotAbsolutePath,
                message: format!("Path must be absolute, got: {:?}", value),
            })
        }
    }
}

impl From<AbsolutePathBuf> for PathBuf {
    fn from(value: AbsolutePathBuf) -> Self {
        value.inner
    }
}

impl Deref for AbsolutePathBuf {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl AsRef<Path> for AbsolutePathBuf {
    fn as_ref(&self) -> &Path {
        &self.inner
    }
}

impl Display for AbsolutePathBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.display().fmt(f)
    }
}

pub trait Filesystem: Sync + Send {
    fn read_file(&self, path: &AbsolutePathBuf) -> Result<String, Error>;
    fn list_dir(&self, path: &AbsolutePathBuf) -> Result<Vec<AbsolutePathBuf>, Error>;
    fn is_file(&self, path: &AbsolutePathBuf) -> bool;
    fn is_dir(&self, path: &AbsolutePathBuf) -> bool;
}

#[derive(Clone, Debug)]
pub struct LocalFilesystem;

impl Filesystem for LocalFilesystem {
    fn read_file(&self, path: &AbsolutePathBuf) -> Result<String, Error> {
        Ok(std::fs::read_to_string(path)?)
    }

    fn list_dir(&self, path: &AbsolutePathBuf) -> Result<Vec<AbsolutePathBuf>, Error> {
        Ok(std::fs::read_dir(path)?
            .map(|entry| Ok(AbsolutePathBuf::try_from(entry?.path())?))
            .collect::<Result<Vec<_>, Error>>()?)
    }

    fn is_file(&self, path: &AbsolutePathBuf) -> bool {
        path.is_file()
    }

    fn is_dir(&self, path: &AbsolutePathBuf) -> bool {
        path.is_dir()
    }
}

#[cfg(feature = "git")]
mod git {
    use super::*;
    use std::sync::{Arc, Mutex, MutexGuard};

    #[derive(Clone)]
    pub struct GitFilesystem<F: Filesystem> {
        repository: Arc<Mutex<git2::Repository>>,
        spec: String,
        fallback_filesystem: F,
    }

    impl GitFilesystem<LocalFilesystem> {
        pub fn new(repository: git2::Repository, spec: String) -> Self {
            GitFilesystem::with_fallback_filesystem(repository, spec, LocalFilesystem)
        }
    }

    impl<F: Filesystem> GitFilesystem<F> {
        pub fn with_fallback_filesystem(
            repository: git2::Repository,
            spec: String,
            fallback_filesystem: F,
        ) -> Self {
            GitFilesystem {
                repository: Arc::new(Mutex::new(repository)),
                spec,
                fallback_filesystem,
            }
        }

        fn repository(&self) -> MutexGuard<'_, git2::Repository> {
            self.repository
                .lock()
                .expect("Should never fail to acquire lock on repository")
        }

        fn get_tree_entry<'tree>(
            &'tree self,
            relative_path: &'tree Path,
        ) -> Result<git2::TreeEntry<'tree>, git2::Error> {
            let repository = self.repository();
            let object = repository.revparse_single(&self.spec)?;
            let tree = object.peel_to_tree()?;
            tree.get_path(relative_path)
        }

        fn relative_path<'a>(&self, path: &'a AbsolutePathBuf) -> Option<&'a Path> {
            let repository = self.repository();
            let Some(prefix) = repository.workdir() else {
                return None;
            };
            assert!(
                prefix.is_absolute(),
                "Repository workdir should be an absolute path"
            );
            let Ok(relative_path) = path.strip_prefix(prefix) else {
                return None;
            };
            Some(relative_path)
        }
    }

    #[cfg(unix)]
    fn git_name(bytes: &[u8]) -> Option<&OsStr> {
        use std::os::unix::ffi::OsStrExt;
        Some(OsStr::from_bytes(bytes))
    }

    #[cfg(windows)]
    fn git_name(bytes: &[u8]) -> Option<&OsStr> {
        None
    }

    impl<F: Filesystem> Filesystem for GitFilesystem<F> {
        fn read_file(&self, path: &AbsolutePathBuf) -> Result<String, Error> {
            let Some(relative_path) = self.relative_path(path) else {
                return LocalFilesystem.read_file(path);
            };

            let repository = self.repository();

            let blob = self
                .get_tree_entry(relative_path)
                .and_then(|entry| repository.find_blob(entry.id()))
                .map_err(|error| Error {
                    kind: match error.code() {
                        git2::ErrorCode::Directory => ErrorKind::IsADirectory,
                        git2::ErrorCode::NotFound => ErrorKind::NotFound,
                        _ => ErrorKind::Unknown,
                    },
                    message: error.to_string(),
                })?;

            let string = String::from_utf8(blob.content().to_vec()).map_err(|e| Error {
                kind: ErrorKind::ReadError,
                message: e.to_string(),
            })?;

            Ok(string)
        }

        fn list_dir(&self, path: &AbsolutePathBuf) -> Result<Vec<AbsolutePathBuf>, Error> {
            let Some(relative_path) = self.relative_path(path) else {
                return LocalFilesystem.list_dir(path);
            };

            let repository = self.repository();

            self.get_tree_entry(relative_path)
                .and_then(|entry| repository.find_tree(entry.id()))
                .map_err(|error| Error {
                    kind: match error.code() {
                        git2::ErrorCode::Invalid => ErrorKind::IsADirectory,
                        git2::ErrorCode::NotFound => ErrorKind::NotFound,
                        _ => ErrorKind::Unknown,
                    },
                    message: error.to_string(),
                })?
                .iter()
                .map(|entry| {
                    let name = git_name(entry.name_bytes()).ok_or_else(|| Error {
                        kind: ErrorKind::Unknown,
                        message: String::from("Invalid filename encoding"),
                    })?;
                    Ok(path.try_join(name)?)
                })
                .collect::<Result<Vec<AbsolutePathBuf>, Error>>()
        }

        fn is_file(&self, path: &AbsolutePathBuf) -> bool {
            let Some(relative_path) = self.relative_path(path) else {
                return self.fallback_filesystem.is_file(path);
            };

            match self.get_tree_entry(relative_path).map(|tree| tree.kind()) {
                Ok(Some(git2::ObjectType::Blob)) => true,
                _ => false,
            }
        }

        fn is_dir(&self, path: &AbsolutePathBuf) -> bool {
            let Some(relative_path) = self.relative_path(path) else {
                return self.fallback_filesystem.is_dir(path);
            };

            match self.get_tree_entry(relative_path).map(|tree| tree.kind()) {
                Ok(Some(git2::ObjectType::Tree)) => true,
                _ => false,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn join(base: &AbsolutePathBuf, path: &str) -> AbsolutePathBuf {
        base.try_join(path)
            .expect("Test data paths should be absolute and valid")
    }

    fn filesystem_data_dir() -> AbsolutePathBuf {
        join(
            &AbsolutePathBuf::try_from(PathBuf::from(env!("CARGO_MANIFEST_DIR")))
                .expect("CARGO_MANIFEST_DIR should be an absolute path"),
            "tests/data/filesystem",
        )
    }

    #[test]
    fn test_local_list_dir() {
        let dir = filesystem_data_dir();

        let entries = LocalFilesystem.list_dir(&dir);

        assert_eq!(
            entries,
            Ok(vec![join(&dir, "data.txt"), join(&dir, "hello.txt")])
        );
    }

    #[test]
    fn test_local_read_file() {
        let file = join(&filesystem_data_dir(), "data.txt");

        let content = LocalFilesystem.read_file(&file);

        assert_eq!(content, Ok(String::from("Some data\n")));
    }
}
