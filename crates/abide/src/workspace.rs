use std::collections::{BTreeSet, HashMap};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use miette::{IntoDiagnostic, WrapErr};

use crate::diagnostic::{Diagnostic, DiagnosticSink};
use crate::driver;
use crate::ir::LowerDiagnostics;
use crate::loader::{self, SourceProvider};
use crate::verify::VerifyConfig;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(u32);

#[derive(Debug)]
struct FileEntry {
    path: PathBuf,
    source: Arc<str>,
    version: u64,
}

#[derive(Debug)]
struct CachedQuery<T> {
    dependencies: Vec<(PathBuf, u64)>,
    value: Arc<T>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(clippy::struct_excessive_bools)]
struct VerifyConfigKey {
    bounded_only: bool,
    unbounded_only: bool,
    overall_timeout_ms: u64,
    induction_timeout_ms: u64,
    bmc_timeout_ms: u64,
    prop_bmc_depth: usize,
    ic3_timeout_ms: u64,
    no_ic3: bool,
    no_prop_verify: bool,
    no_fn_verify: bool,
    progress: bool,
    solver_selection: u8,
    chc_selection: u8,
}

impl From<&VerifyConfig> for VerifyConfigKey {
    fn from(config: &VerifyConfig) -> Self {
        Self {
            bounded_only: config.bounded_only,
            unbounded_only: config.unbounded_only,
            overall_timeout_ms: config.overall_timeout_ms,
            induction_timeout_ms: config.induction_timeout_ms,
            bmc_timeout_ms: config.bmc_timeout_ms,
            prop_bmc_depth: config.prop_bmc_depth,
            ic3_timeout_ms: config.ic3_timeout_ms,
            no_ic3: config.no_ic3,
            no_prop_verify: config.no_prop_verify,
            no_fn_verify: config.no_fn_verify,
            progress: config.progress,
            solver_selection: config.solver_selection as u8,
            chc_selection: config.chc_selection as u8,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct VerifyCacheKey {
    root: FileId,
    config: VerifyConfigKey,
}

pub struct CompilerWorkspace {
    root_dir: PathBuf,
    next_file_id: u32,
    files: HashMap<FileId, FileEntry>,
    file_ids_by_path: HashMap<PathBuf, FileId>,
    path_versions: HashMap<PathBuf, u64>,
    parse_cache: HashMap<FileId, CachedQuery<driver::ParseFileResult>>,
    elaborate_cache: HashMap<FileId, CachedQuery<driver::ElaboratedFiles>>,
    lower_cache: HashMap<FileId, CachedQuery<driver::LoweredFiles>>,
    verify_cache: HashMap<VerifyCacheKey, CachedQuery<driver::VerifiedFiles>>,
}

impl Default for CompilerWorkspace {
    fn default() -> Self {
        Self::new()
    }
}

impl CompilerWorkspace {
    #[must_use]
    pub fn new() -> Self {
        let root_dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        Self::with_root_dir(root_dir)
    }

    #[must_use]
    pub fn with_root_dir(root_dir: impl Into<PathBuf>) -> Self {
        Self {
            root_dir: normalize_path(&root_dir.into()),
            next_file_id: 0,
            files: HashMap::new(),
            file_ids_by_path: HashMap::new(),
            path_versions: HashMap::new(),
            parse_cache: HashMap::new(),
            elaborate_cache: HashMap::new(),
            lower_cache: HashMap::new(),
            verify_cache: HashMap::new(),
        }
    }

    pub fn open_file(&mut self, path: impl AsRef<Path>) -> miette::Result<FileId> {
        let normalized = self.normalize_path(path.as_ref());
        let source = std::fs::read_to_string(&normalized)
            .into_diagnostic()
            .wrap_err_with(|| format!("failed to read {}", normalized.display()))?;
        Ok(self.set_file_source(normalized, source))
    }

    pub fn set_file_source(&mut self, path: impl AsRef<Path>, source: impl Into<String>) -> FileId {
        let normalized = self.normalize_path(path.as_ref());
        self.upsert_file(normalized, source.into())
    }

    pub fn update_file_source(&mut self, file_id: FileId, source: impl Into<String>) -> Option<()> {
        let path = self.files.get(&file_id)?.path.clone();
        let _ = self.upsert_file(path, source.into());
        Some(())
    }

    #[must_use]
    pub fn file_id(&self, path: impl AsRef<Path>) -> Option<FileId> {
        let normalized = self.normalize_path(path.as_ref());
        self.file_ids_by_path.get(&normalized).copied()
    }

    #[must_use]
    pub fn path(&self, file_id: FileId) -> Option<&Path> {
        self.files.get(&file_id).map(|entry| entry.path.as_path())
    }

    #[must_use]
    pub fn source_text(&self, file_id: FileId) -> Option<Arc<str>> {
        self.files
            .get(&file_id)
            .map(|entry| Arc::clone(&entry.source))
    }

    #[must_use]
    pub fn known_files(&self) -> Vec<(FileId, PathBuf)> {
        self.files
            .iter()
            .map(|(file_id, entry)| (*file_id, entry.path.clone()))
            .collect()
    }

    pub fn parse(&mut self, file_id: FileId) -> miette::Result<Arc<driver::ParseFileResult>> {
        let dependency = self.single_file_dependency(file_id)?;
        if let Some(cached) = self.parse_cache.get(&file_id) {
            if self.dependencies_match(&cached.dependencies) {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let entry = self
            .files
            .get(&file_id)
            .ok_or_else(|| miette::miette!("unknown file id {:?}", file_id))?;
        let tokens = driver::lex_source(entry.source.as_ref()).map_err(|errors| {
            miette::miette!(
                "failed to lex {}: {}",
                entry.path.display(),
                errors
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; ")
            )
        })?;
        let mut parser = crate::parse::Parser::new(tokens);
        let (program, parse_errors) = parser.parse_program_recovering();
        let result = Arc::new(driver::ParseFileResult {
            source: entry.source.to_string(),
            program,
            diagnostics: parse_errors
                .into_iter()
                .map(|error| {
                    error
                        .to_diagnostic()
                        .in_file(entry.path.display().to_string())
                })
                .collect(),
        });
        self.parse_cache.insert(
            file_id,
            CachedQuery {
                dependencies: vec![dependency],
                value: Arc::clone(&result),
            },
        );
        Ok(result)
    }

    pub fn elaborate(&mut self, file_id: FileId) -> miette::Result<Arc<driver::ElaboratedFiles>> {
        if let Some(cached) = self.elaborate_cache.get(&file_id) {
            if self.dependencies_match(&cached.dependencies) {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let root_path = self
            .files
            .get(&file_id)
            .ok_or_else(|| miette::miette!("unknown file id {:?}", file_id))?
            .path
            .clone();

        let (result, dependencies) = {
            let mut provider = WorkspaceSourceProvider::new(self);
            let (env, load_errors, all_paths) =
                loader::load_files_with_provider(&mut provider, std::slice::from_ref(&root_path));

            let mut sources = provider.source_map_from_paths(&all_paths);
            if load_errors.is_empty() {
                for loaded_path in &all_paths {
                    let key = loaded_path.display().to_string();
                    if !sources.iter().any(|(name, _)| name == &key) {
                        if let Some(source) = provider.workspace_source_text(loaded_path) {
                            sources.push((key, source));
                        }
                    }
                }

                let include_load_errors = env.include_load_errors.clone();
                let had_include_errors = !include_load_errors.is_empty();
                let (result, mut errors) = crate::elab::elaborate_env(env);
                if had_include_errors {
                    errors.push(crate::elab::error::ElabError::new(
                        crate::elab::error::ErrorKind::UndefinedRef,
                        "one or more included files failed to load (see above)",
                        String::new(),
                    ));
                }

                let mut diagnostics = DiagnosticSink::new();
                diagnostics.extend(WorkspaceSourceProvider::flatten_load_diagnostics(
                    &include_load_errors,
                ));
                diagnostics.extend(
                    errors
                        .iter()
                        .map(crate::elab::error::ElabError::to_diagnostic),
                );

                let elaborated = driver::ElaboratedFiles {
                    result,
                    sources,
                    diagnostics: diagnostics.into_sorted_deduped(),
                };
                (elaborated, provider.dependency_versions())
            } else {
                let diagnostics = WorkspaceSourceProvider::flatten_load_diagnostics(&load_errors);
                let elaborated = driver::ElaboratedFiles {
                    result: crate::elab::types::ElabResult {
                        module_name: None,
                        includes: Vec::new(),
                        use_decls: Vec::new(),
                        aliases: HashMap::new(),
                        types: Vec::new(),
                        entities: Vec::new(),
                        interfaces: Vec::new(),
                        externs: Vec::new(),
                        systems: Vec::new(),
                        preds: Vec::new(),
                        props: Vec::new(),
                        verifies: Vec::new(),
                        scenes: Vec::new(),
                        theorems: Vec::new(),
                        axioms: Vec::new(),
                        lemmas: Vec::new(),
                        consts: Vec::new(),
                        fns: Vec::new(),
                        under_blocks: Vec::new(),
                    },
                    sources: std::mem::take(&mut sources),
                    diagnostics,
                };
                (elaborated, provider.dependency_versions())
            }
        };

        let result = Arc::new(result);
        self.elaborate_cache.insert(
            file_id,
            CachedQuery {
                dependencies,
                value: Arc::clone(&result),
            },
        );
        Ok(result)
    }

    pub fn diagnostics(&mut self, file_id: FileId) -> miette::Result<Arc<Vec<Diagnostic>>> {
        let elaborated = self.elaborate(file_id)?;
        Ok(Arc::new(elaborated.diagnostics.clone()))
    }

    pub fn lower(&mut self, file_id: FileId) -> miette::Result<Arc<driver::LoweredFiles>> {
        if let Some(cached) = self.lower_cache.get(&file_id) {
            if self.dependencies_match(&cached.dependencies) {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let elaborated = self.elaborate(file_id)?;
        let (ir_program, lower_diagnostics) = crate::ir::lower(&elaborated.result);
        let mut diagnostics = DiagnosticSink::new();
        diagnostics.extend(elaborated.diagnostics.iter().cloned());
        diagnostics.extend(lower_diagnostics.diagnostics.iter().cloned());

        let result = Arc::new(driver::LoweredFiles {
            result: elaborated.result.clone(),
            sources: elaborated.sources.clone(),
            ir_program,
            lower_diagnostics,
            diagnostics: diagnostics.into_sorted_deduped(),
        });
        let dependencies = self
            .elaborate_cache
            .get(&file_id)
            .map_or_else(Vec::new, |cached| cached.dependencies.clone());
        self.lower_cache.insert(
            file_id,
            CachedQuery {
                dependencies,
                value: Arc::clone(&result),
            },
        );
        Ok(result)
    }

    pub fn verify(
        &mut self,
        file_id: FileId,
        config: &VerifyConfig,
    ) -> miette::Result<Arc<driver::VerifiedFiles>> {
        let key = VerifyCacheKey {
            root: file_id,
            config: VerifyConfigKey::from(config),
        };
        if let Some(cached) = self.verify_cache.get(&key) {
            if self.dependencies_match(&cached.dependencies) {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let lowered = self.lower(file_id)?;
        let result = Arc::new(driver::VerifiedFiles {
            lowered: driver::LoweredFiles {
                result: lowered.result.clone(),
                sources: lowered.sources.clone(),
                ir_program: lowered.ir_program.clone(),
                lower_diagnostics: LowerDiagnostics {
                    diagnostics: lowered.lower_diagnostics.diagnostics.clone(),
                },
                diagnostics: lowered.diagnostics.clone(),
            },
            results: crate::verify::verify_all(&lowered.ir_program, config),
        });
        let dependencies = self
            .lower_cache
            .get(&file_id)
            .map_or_else(Vec::new, |cached| cached.dependencies.clone());
        self.verify_cache.insert(
            key,
            CachedQuery {
                dependencies,
                value: Arc::clone(&result),
            },
        );
        Ok(result)
    }

    fn upsert_file(&mut self, path: PathBuf, source: String) -> FileId {
        if let Some(&file_id) = self.file_ids_by_path.get(&path) {
            let entry = self.files.get_mut(&file_id).expect("file entry exists");
            if entry.source.as_ref() != source {
                entry.version += 1;
                entry.source = Arc::<str>::from(source);
            }
            self.path_versions.insert(path, entry.version);
            file_id
        } else {
            let file_id = FileId(self.next_file_id);
            self.next_file_id += 1;
            let entry = FileEntry {
                path: path.clone(),
                source: Arc::<str>::from(source),
                version: 1,
            };
            self.path_versions.insert(path.clone(), entry.version);
            self.file_ids_by_path.insert(path, file_id);
            self.files.insert(file_id, entry);
            file_id
        }
    }

    fn normalize_path(&self, path: &Path) -> PathBuf {
        if path.is_absolute() {
            normalize_path(path)
        } else {
            normalize_path(&self.root_dir.join(path))
        }
    }

    fn single_file_dependency(&self, file_id: FileId) -> miette::Result<(PathBuf, u64)> {
        let entry = self
            .files
            .get(&file_id)
            .ok_or_else(|| miette::miette!("unknown file id {:?}", file_id))?;
        Ok((entry.path.clone(), self.path_version(&entry.path)))
    }

    fn path_version(&self, path: &Path) -> u64 {
        self.path_versions.get(path).copied().unwrap_or(0)
    }

    fn dependencies_match(&self, dependencies: &[(PathBuf, u64)]) -> bool {
        dependencies
            .iter()
            .all(|(path, version)| self.path_version(path) == *version)
    }
}

struct WorkspaceSourceProvider<'a> {
    workspace: &'a mut CompilerWorkspace,
    dependency_paths: BTreeSet<PathBuf>,
}

impl<'a> WorkspaceSourceProvider<'a> {
    fn new(workspace: &'a mut CompilerWorkspace) -> Self {
        Self {
            workspace,
            dependency_paths: BTreeSet::new(),
        }
    }

    fn remember_path(&mut self, path: PathBuf) {
        self.workspace
            .path_versions
            .entry(path.clone())
            .or_insert(0);
        self.dependency_paths.insert(path);
    }

    fn dependency_versions(&self) -> Vec<(PathBuf, u64)> {
        self.dependency_paths
            .iter()
            .map(|path| (path.clone(), self.workspace.path_version(path)))
            .collect()
    }

    fn source_map_from_paths(&self, paths: &[PathBuf]) -> driver::SourceMap {
        paths
            .iter()
            .filter_map(|path| {
                self.workspace_source_text(path)
                    .map(|source| (path.display().to_string(), source))
            })
            .collect()
    }

    fn workspace_source_text(&self, path: &Path) -> Option<String> {
        let file_id = self.workspace.file_ids_by_path.get(path)?;
        Some(self.workspace.files.get(file_id)?.source.to_string())
    }

    fn flatten_load_diagnostics(errors: &[loader::LoadError]) -> Vec<Diagnostic> {
        let mut sink = DiagnosticSink::new();
        for error in errors {
            sink.extend(error.diagnostics());
        }
        sink.into_sorted_deduped()
    }
}

impl SourceProvider for WorkspaceSourceProvider<'_> {
    fn canonicalize(&mut self, path: &Path) -> Result<PathBuf, String> {
        let normalized = self.workspace.normalize_path(path);
        if self.workspace.file_ids_by_path.contains_key(&normalized) {
            self.remember_path(normalized.clone());
            return Ok(normalized);
        }

        if let Ok(canonical) = std::fs::canonicalize(&normalized) {
            self.remember_path(canonical.clone());
            return Ok(canonical);
        }

        self.remember_path(normalized.clone());
        Err(format!(
            "include file not found: '{}'",
            normalized.display()
        ))
    }

    fn read_to_string(&mut self, path: &Path) -> Result<String, String> {
        let canonical = self.canonicalize(path)?;
        if let Some(file_id) = self.workspace.file_ids_by_path.get(&canonical).copied() {
            return self
                .workspace
                .files
                .get(&file_id)
                .map(|entry| entry.source.to_string())
                .ok_or_else(|| format!("tracked file disappeared: {}", canonical.display()));
        }

        let source = std::fs::read_to_string(&canonical).map_err(|error| error.to_string())?;
        let _ = self.workspace.upsert_file(canonical, source.clone());
        Ok(source)
    }
}

fn normalize_path(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            Component::Normal(part) => normalized.push(part),
        }
    }
    if normalized.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        normalized
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::VerifyConfig;

    #[test]
    fn parse_query_reuses_cache_until_source_changes() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let file_id = workspace.set_file_source("spec.ab", "entity Order { status: int }");

        let first = workspace.parse(file_id).expect("parse first");
        let second = workspace.parse(file_id).expect("parse second");
        assert!(
            Arc::ptr_eq(&first, &second),
            "parse query should reuse cached Arc"
        );

        workspace
            .update_file_source(file_id, "entity Order { status: bool }")
            .expect("update source");
        let third = workspace.parse(file_id).expect("parse after edit");
        assert!(
            !Arc::ptr_eq(&first, &third),
            "parse query should invalidate after source change"
        );
    }

    #[test]
    fn elaborate_query_tracks_in_memory_include_dependency_changes() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let child_id = workspace.set_file_source("defs.ab", "enum Status = Pending | Done");
        let root_id = workspace.set_file_source(
            "root.ab",
            "include \"defs.ab\"\nentity Order { status: Status = @Pending }",
        );

        let first = workspace.elaborate(root_id).expect("first elaborate");
        assert!(
            first.diagnostics.is_empty(),
            "expected clean elaboration, got {:?}",
            first.diagnostics
        );

        workspace
            .update_file_source(
                child_id,
                "enum Status = Pending | Done\nstruct Broken { x: }",
            )
            .expect("update child");
        let second = workspace.elaborate(root_id).expect("second elaborate");
        assert!(
            !Arc::ptr_eq(&first, &second),
            "elaboration should invalidate when include dependency changes"
        );
        assert!(
            second.diagnostics.iter().any(Diagnostic::is_error),
            "expected diagnostics from broken include, got {:?}",
            second.diagnostics
        );
    }

    #[test]
    fn verify_query_is_cached_per_config() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let root_id = workspace.set_file_source(
            "simple.ab",
            "entity Order { status: int = 0 }\nverify ok for Order[0..1] { assert true }",
        );

        let config = VerifyConfig::default();
        let first = workspace.verify(root_id, &config).expect("first verify");
        let second = workspace.verify(root_id, &config).expect("second verify");
        assert!(
            Arc::ptr_eq(&first, &second),
            "verify query should reuse cached Arc"
        );

        let bounded_only = VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        };
        let third = workspace
            .verify(root_id, &bounded_only)
            .expect("bounded-only verify");
        assert!(
            !Arc::ptr_eq(&first, &third),
            "verify query cache should distinguish configs"
        );
    }

    #[test]
    fn diagnostics_query_returns_shared_diagnostics_for_missing_include() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let root_id = workspace.set_file_source("root.ab", "include \"missing.ab\"");

        let diagnostics = workspace.diagnostics(root_id).expect("diagnostics query");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_deref() == Some("abide::load::io")),
            "expected missing-include diagnostic, got {diagnostics:?}"
        );
    }
}
