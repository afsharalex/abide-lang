//! Shared CLI target discovery.

use std::collections::BTreeSet;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

/// Error raised while resolving user-supplied source targets.
#[derive(Debug)]
pub enum TargetDiscoveryError {
    /// No targets were supplied.
    NoTargets,
    /// A supplied target does not exist.
    MissingTarget(PathBuf),
    /// A supplied file is not an Abide source file.
    UnsupportedFile(PathBuf),
    /// A supplied directory exists but contains no Abide source files.
    EmptyDirectory(PathBuf),
    /// Filesystem metadata could not be read for a supplied target.
    TargetMetadata { path: PathBuf, source: io::Error },
    /// A directory could not be read while recursively discovering files.
    ReadDirectory { path: PathBuf, source: io::Error },
    /// A discovered source file could not be canonicalized.
    Canonicalize { path: PathBuf, source: io::Error },
}

impl fmt::Display for TargetDiscoveryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoTargets => write!(f, "no source targets provided"),
            Self::MissingTarget(path) => {
                write!(f, "source target not found: {}", path.display())
            }
            Self::UnsupportedFile(path) => write!(
                f,
                "unsupported source target: {}; expected .ab, .abi, or .abp",
                path.display()
            ),
            Self::EmptyDirectory(path) => {
                write!(f, "no Abide source files found in {}", path.display())
            }
            Self::TargetMetadata { path, source } => {
                write!(
                    f,
                    "could not inspect source target {}: {source}",
                    path.display()
                )
            }
            Self::ReadDirectory { path, source } => {
                write!(
                    f,
                    "could not read source directory {}: {source}",
                    path.display()
                )
            }
            Self::Canonicalize { path, source } => {
                write!(
                    f,
                    "could not canonicalize source file {}: {source}",
                    path.display()
                )
            }
        }
    }
}

impl std::error::Error for TargetDiscoveryError {}

/// Resolve explicit source files and source directories into sorted, deduplicated files.
pub fn resolve_source_targets(targets: &[PathBuf]) -> Result<Vec<PathBuf>, TargetDiscoveryError> {
    if targets.is_empty() {
        return Err(TargetDiscoveryError::NoTargets);
    }

    let mut files = BTreeSet::new();
    for target in targets {
        let target_files = resolve_source_target(target)?;
        files.extend(target_files);
    }
    Ok(files.into_iter().collect())
}

/// Return whether a directory recursively contains at least one Abide source file.
pub fn directory_contains_source_files(dir: &Path) -> bool {
    collect_source_files_in_directory(dir).is_ok_and(|files| !files.is_empty())
}

/// Return true when a path has an Abide source extension.
pub fn is_abide_source_file(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("ab" | "abi" | "abp")
    )
}

fn resolve_source_target(path: &Path) -> Result<Vec<PathBuf>, TargetDiscoveryError> {
    let metadata = match std::fs::metadata(path) {
        Ok(metadata) => metadata,
        Err(source) if source.kind() == io::ErrorKind::NotFound => {
            return Err(TargetDiscoveryError::MissingTarget(path.to_path_buf()));
        }
        Err(source) => {
            return Err(TargetDiscoveryError::TargetMetadata {
                path: path.to_path_buf(),
                source,
            });
        }
    };

    if metadata.is_file() {
        if !is_abide_source_file(path) {
            return Err(TargetDiscoveryError::UnsupportedFile(path.to_path_buf()));
        }
        return canonicalize_source_file(path).map(|path| vec![path]);
    }

    if metadata.is_dir() {
        let files = collect_source_files_in_directory(path)?;
        if files.is_empty() {
            return Err(TargetDiscoveryError::EmptyDirectory(path.to_path_buf()));
        }
        return Ok(files);
    }

    Err(TargetDiscoveryError::UnsupportedFile(path.to_path_buf()))
}

fn collect_source_files_in_directory(dir: &Path) -> Result<Vec<PathBuf>, TargetDiscoveryError> {
    let mut files = Vec::new();
    collect_source_files_in_directory_inner(dir, &mut files)?;
    files.sort();
    files.dedup();
    Ok(files)
}

fn collect_source_files_in_directory_inner(
    dir: &Path,
    files: &mut Vec<PathBuf>,
) -> Result<(), TargetDiscoveryError> {
    let mut entries = Vec::new();
    let read_dir =
        std::fs::read_dir(dir).map_err(|source| TargetDiscoveryError::ReadDirectory {
            path: dir.to_path_buf(),
            source,
        })?;

    for entry in read_dir {
        let entry = entry.map_err(|source| TargetDiscoveryError::ReadDirectory {
            path: dir.to_path_buf(),
            source,
        })?;
        entries.push(entry.path());
    }
    entries.sort();

    for path in entries {
        if path.is_dir() {
            collect_source_files_in_directory_inner(&path, files)?;
        } else if is_abide_source_file(&path) {
            files.push(canonicalize_source_file(&path)?);
        }
    }

    Ok(())
}

fn canonicalize_source_file(path: &Path) -> Result<PathBuf, TargetDiscoveryError> {
    std::fs::canonicalize(path).map_err(|source| TargetDiscoveryError::Canonicalize {
        path: path.to_path_buf(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn write_file(path: &Path, contents: &str) {
        std::fs::write(path, contents).expect("write test file");
    }

    #[test]
    fn resolve_source_targets_recurses_sorts_and_deduplicates() {
        let dir = TempDir::new().expect("tempdir");
        let nested = dir.path().join("nested");
        std::fs::create_dir(&nested).expect("create nested dir");
        let first = dir.path().join("first.ab");
        let second = nested.join("second.abi");
        let third = nested.join("third.abp");
        write_file(&third, "module Third\n");
        write_file(&first, "module First\n");
        write_file(&second, "module Second\n");
        write_file(&nested.join("ignored.qa"), "ask entities\n");

        let targets = resolve_source_targets(&[dir.path().to_path_buf(), second.clone()])
            .expect("resolve source targets");

        assert_eq!(
            targets,
            vec![
                std::fs::canonicalize(first).expect("canonicalize first"),
                std::fs::canonicalize(second).expect("canonicalize second"),
                std::fs::canonicalize(third).expect("canonicalize third"),
            ]
        );
    }

    #[test]
    fn resolve_source_targets_rejects_empty_directories() {
        let dir = TempDir::new().expect("tempdir");

        let error = resolve_source_targets(&[dir.path().to_path_buf()])
            .expect_err("empty source directory should fail");

        assert!(matches!(error, TargetDiscoveryError::EmptyDirectory(_)));
    }

    #[test]
    fn directory_contains_source_files_ignores_non_source_files() {
        let dir = TempDir::new().expect("tempdir");
        write_file(&dir.path().join("script.qa"), "ask entities\n");
        assert!(!directory_contains_source_files(dir.path()));

        write_file(&dir.path().join("spec.ab"), "module Spec\n");
        assert!(directory_contains_source_files(dir.path()));
    }
}
