//! Abide Language Server (`abide-lsp`).
//!
//! Implements the Language Server Protocol on top of the `abide`
//! library's IDE primitives. The server is a thin shim:
//!
//! - [`LspState`] holds the compiler workspace and the set of currently
//!   open documents. Edits flow through `did_open` / `did_change` into
//!   [`abide::workspace::CompilerWorkspace`].
//! - [`Backend`] implements [`tower_lsp::LanguageServer`]. Each LSP
//!   request rebuilds the workspace index on demand via
//!   [`abide::ide::build_workspace_index`] — there is no incremental
//!   query layer here, the IDE crate is the authority for symbol and
//!   completion lookups.
//! - Diagnostics are republished per-root-file. `published_by_root`
//!   tracks which URIs each root last pushed diagnostics to so that
//!   stale diagnostics can be cleared when an error moves out of a
//!   file.
//!
//! The free functions at the bottom translate between Abide's flat
//! byte-offset [`Span`](abide::span::Span) and LSP's
//! line/column [`Position`].

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use abide::diagnostic::{Diagnostic, DiagnosticSeverity};
use abide::ide::{
    build_workspace_index, classify_abide_cursor, classify_qa_cursor, completion_context,
    identifier_at, AbideCursorContext, CompletionContext, IdeSymbol, IdeSymbolKind,
    QaCursorContext, WorkspaceIndex,
};
use abide::qa::complete::{qa_command_candidates, qa_query_subcommand_candidates};
use abide::qa::model::FlowModel;
use abide::workspace::{CompilerWorkspace, FileId};
use tokio::sync::Mutex;
use tower_lsp::jsonrpc::{Error, Result};
#[allow(clippy::wildcard_imports)]
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

const QA_RUN_SCRIPT_COMMAND: &str = "abide.qa.runScript";

/// Tracking record for one open editor buffer.
///
/// `version` is the monotonic LSP document version — used by
/// [`LspState::should_accept_document_version`] to drop out-of-order
/// edits.
#[derive(Debug)]
struct OpenDocument {
    file_id: FileId,
    version: i32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ProjectFileKind {
    AbideSource,
    QaScript,
    Unsupported,
}

impl ProjectFileKind {
    fn for_path(path: &Path) -> Self {
        path.extension()
            .and_then(std::ffi::OsStr::to_str)
            .map(str::to_ascii_lowercase)
            .map_or(Self::Unsupported, |extension| match extension.as_str() {
                "ab" | "abi" | "abp" => Self::AbideSource,
                "qa" => Self::QaScript,
                _ => Self::Unsupported,
            })
    }

    fn is_project_source(self) -> bool {
        matches!(self, Self::AbideSource | Self::QaScript)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectFile {
    path: PathBuf,
    kind: ProjectFileKind,
}

#[derive(Debug, Clone)]
struct ProjectModel {
    root: PathBuf,
    files: BTreeMap<PathBuf, ProjectFile>,
}

impl ProjectModel {
    fn discover(root: impl AsRef<Path>) -> io::Result<Self> {
        let root = normalize_path_lexical(root.as_ref());
        let mut project = Self::empty(root);
        let root = project.root.clone();
        project.discover_dir(&root)?;
        Ok(project)
    }

    fn empty(root: impl Into<PathBuf>) -> Self {
        Self {
            root: normalize_path_lexical(&root.into()),
            files: BTreeMap::new(),
        }
    }

    fn root(&self) -> &Path {
        &self.root
    }

    #[cfg(test)]
    fn files(&self) -> impl Iterator<Item = &ProjectFile> {
        self.files.values()
    }

    fn register_file(&mut self, path: impl AsRef<Path>) -> Option<ProjectFileKind> {
        let path = self.normalize_under_root(path.as_ref())?;
        let kind = ProjectFileKind::for_path(&path);
        self.files.insert(path.clone(), ProjectFile { path, kind });
        Some(kind)
    }

    fn discover_dir(&mut self, dir: &Path) -> io::Result<()> {
        let mut entries = std::fs::read_dir(dir)?.collect::<io::Result<Vec<_>>>()?;
        entries.sort_by_key(std::fs::DirEntry::path);
        for entry in entries {
            let path = entry.path();
            let file_type = entry.file_type()?;
            if file_type.is_dir() {
                if should_skip_project_dir(&path) {
                    continue;
                }
                self.discover_dir(&path)?;
            } else if file_type.is_file() {
                let kind = ProjectFileKind::for_path(&path);
                if kind.is_project_source() {
                    let _ = self.register_file(path);
                }
            }
        }
        Ok(())
    }

    fn normalize_under_root(&self, path: &Path) -> Option<PathBuf> {
        let absolute = if path.is_absolute() {
            path.to_path_buf()
        } else {
            self.root.join(path)
        };
        let normalized = normalize_path_lexical(&absolute);
        normalized.starts_with(&self.root).then_some(normalized)
    }
}

fn normalize_path_lexical(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                let _ = normalized.pop();
            }
            std::path::Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            std::path::Component::RootDir => normalized.push(component.as_os_str()),
            std::path::Component::Normal(part) => normalized.push(part),
        }
    }
    normalized
}

fn should_skip_project_dir(path: &Path) -> bool {
    path.file_name()
        .and_then(std::ffi::OsStr::to_str)
        .is_some_and(|name| matches!(name, ".git" | ".bd" | "target" | "node_modules"))
}

#[derive(Debug, Clone)]
struct SnapshotFileState {
    kind: ProjectFileKind,
    file_id: Option<FileId>,
    revision: u64,
    open_version: Option<i32>,
}

#[derive(Debug, Clone)]
struct SnapshotCache<T> {
    revision: u64,
    value: Arc<T>,
}

#[derive(Debug, Clone)]
struct WorkspaceIndexCache {
    generation: u64,
    value: Arc<WorkspaceIndex>,
}

struct ProjectSnapshot {
    project: ProjectModel,
    workspace: CompilerWorkspace,
    files: BTreeMap<PathBuf, SnapshotFileState>,
    parse_cache: HashMap<FileId, SnapshotCache<abide::driver::ParseFileResult>>,
    lower_cache: HashMap<FileId, SnapshotCache<abide::driver::LoweredFiles>>,
    diagnostics_cache: HashMap<FileId, SnapshotCache<Vec<Diagnostic>>>,
    workspace_index_cache: Option<WorkspaceIndexCache>,
    workspace_index_generation: u64,
}

impl ProjectSnapshot {
    fn discover(root: impl AsRef<Path>) -> io::Result<Self> {
        let project = ProjectModel::discover(root)?;
        Ok(Self::from_project(project))
    }

    fn empty(root: impl Into<PathBuf>) -> Self {
        Self::from_project(ProjectModel::empty(root))
    }

    fn from_project(project: ProjectModel) -> Self {
        let mut workspace = CompilerWorkspace::with_root_dir(project.root().to_path_buf());
        let mut files = project
            .files
            .values()
            .map(|file| {
                (
                    file.path.clone(),
                    SnapshotFileState {
                        kind: file.kind,
                        file_id: None,
                        revision: 0,
                        open_version: None,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();

        for file in project.files.values() {
            if file.kind != ProjectFileKind::AbideSource {
                continue;
            }
            if let Ok(source) = std::fs::read_to_string(&file.path) {
                let file_id = workspace.set_file_source(&file.path, source);
                if let Some(state) = files.get_mut(&file.path) {
                    state.file_id = Some(file_id);
                }
            }
        }

        Self {
            project,
            workspace,
            files,
            parse_cache: HashMap::new(),
            lower_cache: HashMap::new(),
            diagnostics_cache: HashMap::new(),
            workspace_index_cache: None,
            workspace_index_generation: 0,
        }
    }

    fn file_id(&self, path: impl AsRef<Path>) -> Option<FileId> {
        let path = self.project.normalize_under_root(path.as_ref())?;
        self.files.get(&path)?.file_id
    }

    fn file_kind(&self, path: impl AsRef<Path>) -> Option<ProjectFileKind> {
        let path = self.project.normalize_under_root(path.as_ref())?;
        self.files.get(&path).map(|file| file.kind)
    }

    fn file_kind_for_id(&self, file_id: FileId) -> Option<ProjectFileKind> {
        let path = self.workspace.path(file_id)?;
        self.file_kind(path)
            .or_else(|| Some(ProjectFileKind::for_path(path)))
    }

    fn path(&self, file_id: FileId) -> Option<&Path> {
        self.workspace.path(file_id)
    }

    fn source_text(&self, file_id: FileId) -> Option<Arc<str>> {
        self.workspace.source_text(file_id)
    }

    fn upsert_open_document(&mut self, uri: &Url, version: i32, text: String) -> Option<FileId> {
        let path = uri.to_file_path().ok()?;
        let file_id = self.set_file_source(&path, text);
        if let Some(state) = self.file_state_mut(file_id) {
            state.open_version = Some(version);
        }
        Some(file_id)
    }

    fn set_file_source(&mut self, path: impl AsRef<Path>, source: impl Into<String>) -> FileId {
        let source = source.into();
        let path = self
            .project
            .normalize_under_root(path.as_ref())
            .unwrap_or_else(|| normalize_path_lexical(path.as_ref()));
        let kind = self
            .project
            .register_file(&path)
            .unwrap_or_else(|| ProjectFileKind::for_path(&path));
        let existing_file_id = self.files.get(&path).and_then(|state| state.file_id);
        let file_id = if let Some(file_id) = existing_file_id {
            let _ = self.workspace.update_file_source(file_id, source);
            file_id
        } else {
            self.workspace.set_file_source(&path, source)
        };

        let state = self
            .files
            .entry(path.clone())
            .or_insert_with(|| SnapshotFileState {
                kind,
                file_id: Some(file_id),
                revision: 0,
                open_version: None,
            });
        state.kind = kind;
        state.file_id = Some(file_id);
        state.revision = state.revision.saturating_add(1);
        self.invalidate_file(file_id);
        if kind == ProjectFileKind::AbideSource {
            self.workspace_index_generation = self.workspace_index_generation.saturating_add(1);
            self.workspace_index_cache = None;
            self.invalidate_qa_diagnostics();
        }
        file_id
    }

    fn parse(&mut self, file_id: FileId) -> miette::Result<Arc<abide::driver::ParseFileResult>> {
        let revision = self.file_revision(file_id).unwrap_or(0);
        if let Some(cached) = self.parse_cache.get(&file_id) {
            if cached.revision == revision {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let parsed = self.workspace.parse(file_id)?;
        self.parse_cache.insert(
            file_id,
            SnapshotCache {
                revision,
                value: Arc::clone(&parsed),
            },
        );
        Ok(parsed)
    }

    fn lower(&mut self, file_id: FileId) -> miette::Result<Arc<abide::driver::LoweredFiles>> {
        let _ = self.parse(file_id)?;
        let revision = self.file_revision(file_id).unwrap_or(0);
        if let Some(cached) = self.lower_cache.get(&file_id) {
            if cached.revision == revision {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let lowered = self.workspace.lower(file_id)?;
        self.lower_cache.insert(
            file_id,
            SnapshotCache {
                revision,
                value: Arc::clone(&lowered),
            },
        );
        Ok(lowered)
    }

    fn diagnostics(&mut self, file_id: FileId) -> miette::Result<Arc<Vec<Diagnostic>>> {
        let revision = self.file_revision(file_id).unwrap_or(0);
        if let Some(cached) = self.diagnostics_cache.get(&file_id) {
            if cached.revision == revision {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let diagnostics = match self.file_kind_for_id(file_id) {
            Some(ProjectFileKind::AbideSource) => self.lower(file_id)?.diagnostics.clone(),
            Some(ProjectFileKind::QaScript) => {
                let Some(source) = self.source_text(file_id) else {
                    return Ok(Arc::new(Vec::new()));
                };
                let Some(path) = self.path(file_id) else {
                    return Ok(Arc::new(Vec::new()));
                };
                self.qa_diagnostics(path, source.as_ref())
            }
            Some(ProjectFileKind::Unsupported) | None => Vec::new(),
        };
        let diagnostics = Arc::new(diagnostics);
        self.diagnostics_cache.insert(
            file_id,
            SnapshotCache {
                revision,
                value: Arc::clone(&diagnostics),
            },
        );
        Ok(diagnostics)
    }

    fn workspace_index(&mut self) -> miette::Result<Arc<WorkspaceIndex>> {
        if let Some(cached) = &self.workspace_index_cache {
            if cached.generation == self.workspace_index_generation {
                return Ok(Arc::clone(&cached.value));
            }
        }

        let index = Arc::new(build_workspace_index(&mut self.workspace)?);
        self.workspace_index_cache = Some(WorkspaceIndexCache {
            generation: self.workspace_index_generation,
            value: Arc::clone(&index),
        });
        Ok(index)
    }

    fn identifier_at(
        &mut self,
        file_id: FileId,
        offset: usize,
    ) -> miette::Result<Option<abide::ide::IdeOccurrence>> {
        identifier_at(&mut self.workspace, file_id, offset)
    }

    fn file_revision(&self, file_id: FileId) -> Option<u64> {
        let path = self.workspace.path(file_id)?;
        self.files.get(path).map(|state| state.revision)
    }

    fn file_state_mut(&mut self, file_id: FileId) -> Option<&mut SnapshotFileState> {
        let path = self.workspace.path(file_id)?.to_path_buf();
        self.files.get_mut(&path)
    }

    fn invalidate_file(&mut self, file_id: FileId) {
        self.parse_cache.remove(&file_id);
        self.lower_cache.remove(&file_id);
        self.diagnostics_cache.remove(&file_id);
    }

    fn invalidate_qa_diagnostics(&mut self) {
        let qa_file_ids = self
            .files
            .values()
            .filter(|state| state.kind == ProjectFileKind::QaScript)
            .filter_map(|state| state.file_id)
            .collect::<Vec<_>>();
        for file_id in qa_file_ids {
            self.diagnostics_cache.remove(&file_id);
        }
    }

    fn qa_diagnostics(&self, path: &Path, source: &str) -> Vec<Diagnostic> {
        let mut diagnostics_provider = SnapshotSourceProvider { snapshot: self };
        let mut diagnostics = abide::qa::validate::validate_qa_source_with_provider(
            path,
            source,
            &mut diagnostics_provider,
        );

        let mut embedded_provider = SnapshotSourceProvider { snapshot: self };
        diagnostics.extend(
            abide::qa::validate::validate_embedded_abide_blocks_with_provider(
                path,
                source,
                &mut embedded_provider,
            ),
        );
        diagnostics
    }
}

struct SnapshotSourceProvider<'a> {
    snapshot: &'a ProjectSnapshot,
}

impl abide::loader::SourceProvider for SnapshotSourceProvider<'_> {
    fn canonicalize(&mut self, path: &Path) -> std::result::Result<PathBuf, String> {
        let normalized = if path.is_absolute() {
            normalize_path_lexical(path)
        } else {
            normalize_path_lexical(&self.snapshot.project.root().join(path))
        };
        if self.snapshot.file_id(&normalized).is_some() {
            return Ok(normalized);
        }
        std::fs::canonicalize(&normalized)
            .map(|path| normalize_path_lexical(&path))
            .map_err(|error| error.to_string())
    }

    fn read_to_string(&mut self, path: &Path) -> std::result::Result<String, String> {
        let canonical = self.canonicalize(path)?;
        if let Some(file_id) = self.snapshot.file_id(&canonical) {
            return self
                .snapshot
                .source_text(file_id)
                .map(|source| source.as_ref().to_owned())
                .ok_or_else(|| format!("tracked file disappeared: {}", canonical.display()));
        }
        std::fs::read_to_string(&canonical).map_err(|error| error.to_string())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EditorVerificationTrigger {
    OnChange,
    OnSave,
    Manual,
    Disabled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EditorVerificationPolicy {
    trigger: EditorVerificationTrigger,
    debounce_ms: u64,
    timeout_ms: u64,
}

impl Default for EditorVerificationPolicy {
    fn default() -> Self {
        Self {
            trigger: EditorVerificationTrigger::OnChange,
            debounce_ms: 300,
            timeout_ms: 1_500,
        }
    }
}

impl EditorVerificationPolicy {
    fn from_initialization_options(options: Option<&serde_json::Value>) -> Self {
        let mut policy = Self::default();
        let Some(config) = verification_options(options) else {
            return policy;
        };

        if config.get("enabled").and_then(serde_json::Value::as_bool) == Some(false) {
            policy.trigger = EditorVerificationTrigger::Disabled;
        }
        if let Some(mode) = config.get("mode").and_then(serde_json::Value::as_str) {
            policy.trigger = match mode {
                "change" | "onChange" | "on_change" => EditorVerificationTrigger::OnChange,
                "save" | "onSave" | "on_save" => EditorVerificationTrigger::OnSave,
                "manual" => EditorVerificationTrigger::Manual,
                "disabled" | "off" => EditorVerificationTrigger::Disabled,
                _ => policy.trigger,
            };
        }
        if let Some(debounce_ms) = config.get("debounceMs").and_then(serde_json::Value::as_u64) {
            policy.debounce_ms = debounce_ms;
        }
        if let Some(timeout_ms) = config.get("timeoutMs").and_then(serde_json::Value::as_u64) {
            policy.timeout_ms = timeout_ms;
        }
        policy
    }

    fn should_schedule_on_change(self) -> bool {
        matches!(self.trigger, EditorVerificationTrigger::OnChange)
    }

    fn should_schedule_on_save(self) -> bool {
        matches!(self.trigger, EditorVerificationTrigger::OnSave)
    }

    fn should_run_automatically(self) -> bool {
        self.should_schedule_on_change() || self.should_schedule_on_save()
    }
}

fn verification_options(
    options: Option<&serde_json::Value>,
) -> Option<&serde_json::Map<String, serde_json::Value>> {
    options
        .and_then(|value| value.get("abide"))
        .and_then(|value| value.get("verification"))
        .or_else(|| options.and_then(|value| value.get("verification")))?
        .as_object()
}

/// Per-server-instance state shared behind a `tokio::Mutex`.
///
/// Holds the compiler workspace (source for every file the LSP has
/// touched), the set of buffers the editor currently has open, and a
/// publication ledger so we can clear stale diagnostics when files drop
/// out of the result set.
struct LspState {
    snapshot: ProjectSnapshot,
    documents: HashMap<Url, OpenDocument>,
    /// For each root file we elaborate, the URIs we last published
    /// diagnostics to. Needed because a single elaboration may touch
    /// many files, and when a fix removes errors from one of them we
    /// must explicitly republish empty diagnostics for that URI.
    published_by_root: HashMap<FileId, HashSet<Url>>,
    verification_policy: EditorVerificationPolicy,
}

impl LspState {
    fn new(root_dir: impl AsRef<Path>) -> Self {
        Self::new_with_policy(root_dir, EditorVerificationPolicy::default())
    }

    fn new_with_policy(
        root_dir: impl AsRef<Path>,
        verification_policy: EditorVerificationPolicy,
    ) -> Self {
        let root_dir = root_dir.as_ref();
        let snapshot = ProjectSnapshot::discover(root_dir)
            .unwrap_or_else(|_| ProjectSnapshot::empty(root_dir));
        Self {
            snapshot,
            documents: HashMap::new(),
            published_by_root: HashMap::new(),
            verification_policy,
        }
    }

    fn upsert_open_document(&mut self, uri: &Url, version: i32, text: String) -> Option<FileId> {
        if !self.should_accept_document_version(uri, version) {
            return None;
        }
        let file_id = self.snapshot.upsert_open_document(uri, version, text)?;
        self.documents
            .insert(uri.clone(), OpenDocument { file_id, version });
        Some(file_id)
    }

    fn file_kind(&self, file_id: FileId) -> Option<ProjectFileKind> {
        self.snapshot.file_kind_for_id(file_id)
    }

    /// Returns `true` if `version` is strictly newer than the version we
    /// last recorded for `uri`, or if we have no record. Used to drop
    /// out-of-order edits the editor can send under heavy typing.
    fn should_accept_document_version(&self, uri: &Url, version: i32) -> bool {
        self.documents
            .get(uri)
            .is_none_or(|doc| version > doc.version)
    }

    fn document_version(&self, uri: &Url) -> Option<i32> {
        self.documents.get(uri).map(|doc| doc.version)
    }

    /// Returns `true` if some root file *other than* `root_file_id`
    /// still owns diagnostics for `uri`. We use this to avoid blanking
    /// `uri`'s diagnostics when only one of multiple roots stops
    /// reporting against it.
    fn uri_published_elsewhere(&self, root_file_id: FileId, uri: &Url) -> bool {
        self.published_by_root
            .iter()
            .any(|(other_root, uris)| *other_root != root_file_id && uris.contains(uri))
    }
}

fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::FULL),
                will_save: None,
                will_save_wait_until: None,
                save: Some(TextDocumentSyncSaveOptions::Supported(true)),
            },
        )),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        rename_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![".".to_owned(), "@".to_owned(), ":".to_owned()]),
            ..CompletionOptions::default()
        }),
        code_action_provider: Some(CodeActionProviderCapability::Options(CodeActionOptions {
            code_action_kinds: Some(vec![CodeActionKind::QUICKFIX]),
            resolve_provider: Some(false),
            ..CodeActionOptions::default()
        })),
        execute_command_provider: Some(ExecuteCommandOptions {
            commands: vec![QA_RUN_SCRIPT_COMMAND.to_owned()],
            ..ExecuteCommandOptions::default()
        }),
        ..ServerCapabilities::default()
    }
}

fn verify_config_for_editor_policy(
    verification_policy: EditorVerificationPolicy,
) -> abide::verify::VerifyConfig {
    abide::verify::VerifyConfig {
        overall_timeout_ms: verification_policy.timeout_ms,
        induction_timeout_ms: verification_policy.timeout_ms,
        ..abide::verify::VerifyConfig::default()
    }
}

/// LSP request handler. All async methods serialize through the
/// `state` mutex.
struct Backend {
    client: Client,
    state: Arc<Mutex<LspState>>,
}

type LspDiagnosticMap = HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>;
type LspDocumentVersions = HashMap<Url, Option<i32>>;
type DiagnosticsForRoot = (
    LspDiagnosticMap,
    Vec<Url>,
    LspDocumentVersions,
    Option<String>,
);

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        let verification_policy = EditorVerificationPolicy::from_initialization_options(
            params.initialization_options.as_ref(),
        );
        let root_dir = params
            .root_uri
            .and_then(|uri| uri.to_file_path().ok())
            .or_else(|| std::env::current_dir().ok())
            .unwrap_or_else(|| PathBuf::from("."));
        *self.state.lock().await = LspState::new_with_policy(root_dir, verification_policy);

        Ok(InitializeResult {
            server_info: Some(ServerInfo {
                name: "abide-lsp".to_owned(),
                version: Some(env!("CARGO_PKG_VERSION").to_owned()),
            }),
            capabilities: server_capabilities(),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "abide-lsp initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let text = params.text_document.text;
        if let Some(file_id) = self.upsert_document(&uri, version, text).await {
            self.refresh_diagnostics(file_id).await;
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let Some(change) = params.content_changes.into_iter().last() else {
            return;
        };
        if let Some(file_id) = self.upsert_document(&uri, version, change.text).await {
            self.refresh_diagnostics(file_id).await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;
        let file_id = {
            let state = self.state.lock().await;
            state.documents.get(&uri).map(|doc| doc.file_id)
        };
        if let Some(file_id) = file_id {
            self.refresh_diagnostics(file_id).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        let Ok(path) = uri.to_file_path() else {
            return;
        };

        let stale_uris = {
            let mut state = self.state.lock().await;
            let file_id = state.documents.remove(&uri).map(|doc| doc.file_id);
            if let Some(file_id) = file_id {
                if let Ok(source) = std::fs::read_to_string(&path) {
                    let _ = state.snapshot.set_file_source(&path, source);
                }
                let previous = state.published_by_root.remove(&file_id).unwrap_or_default();
                previous
                    .into_iter()
                    .filter(|published_uri| !state.uri_published_elsewhere(file_id, published_uri))
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            }
        };

        for stale_uri in stale_uris {
            self.client
                .publish_diagnostics(stale_uri, Vec::new(), None)
                .await;
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let mut state = self.state.lock().await;
        Ok(
            completion_items_for_open_document(&mut state, &uri, position)
                .map(CompletionResponse::Array),
        )
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        if !quickfix_actions_requested(params.context.only.as_deref()) {
            return Ok(Some(Vec::new()));
        }
        let state = self.state.lock().await;
        Ok(code_actions_for_document(
            &state,
            &params.text_document.uri,
            &params.context.diagnostics,
        ))
    }

    async fn execute_command(
        &self,
        params: ExecuteCommandParams,
    ) -> Result<Option<serde_json::Value>> {
        if params.command != QA_RUN_SCRIPT_COMMAND {
            return Ok(None);
        }
        let uri = qa_run_command_uri_arg(&params.arguments).map_err(Error::invalid_params)?;
        let (path, source) = {
            let state = self.state.lock().await;
            qa_run_source_for_uri(&state, &uri).map_err(Error::invalid_params)?
        };
        let result = tokio::task::spawn_blocking(move || run_qa_source_to_json(&path, &source))
            .await
            .map_err(|error| Error::invalid_params(format!("QA command task failed: {error}")))?;
        Ok(Some(result))
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some((symbol, range)) = self.symbol_at_position(&uri, position).await else {
            return Ok(None);
        };

        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: format!("```abide\n{}\n```", symbol.detail),
            }),
            range: Some(range),
        }))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let mut state = self.state.lock().await;
        let Some((symbol, _)) = symbol_at_document_position(&mut state, &uri, position) else {
            return Ok(None);
        };
        if let Some(location) =
            location_for_span(&state.snapshot.workspace, symbol.file_id, symbol.span)
        {
            Ok(Some(GotoDefinitionResponse::Array(vec![location])))
        } else {
            Ok(None)
        }
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let mut state = self.state.lock().await;
        let Some((symbol, _)) = symbol_at_document_position(&mut state, &uri, position) else {
            return Ok(None);
        };
        let Ok(index) = state.snapshot.workspace_index() else {
            return Ok(None);
        };

        let locations = reference_locations_for_symbol(
            &state.snapshot,
            &index,
            &symbol,
            params.context.include_declaration,
        );
        Ok(Some(locations))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let mut state = self.state.lock().await;
        let Some((symbol, _)) = symbol_at_document_position(&mut state, &uri, position) else {
            return Ok(None);
        };
        let Ok(index) = state.snapshot.workspace_index() else {
            return Ok(None);
        };

        let changes = rename_changes_for_symbol(&state.snapshot, &index, &symbol, &params.new_name);
        Ok(Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        }))
    }
}

impl Backend {
    /// Registers (or updates) the editor buffer at `uri` with the given
    /// `version` and `text`, and pushes the new source into the
    /// workspace. Returns the workspace `FileId` if the update was
    /// accepted, or `None` if a newer version was already recorded.
    async fn upsert_document(&self, uri: &Url, version: i32, text: String) -> Option<FileId> {
        let mut state = self.state.lock().await;
        let file_id = state.upsert_open_document(uri, version, text)?;
        (state.file_kind(file_id) != Some(ProjectFileKind::Unsupported)).then_some(file_id)
    }

    /// Re-elaborates `root_file_id`, collects the resulting diagnostics
    /// grouped by URI, and publishes them. Diagnostics for URIs that
    /// used to be reported by this root but no longer are get cleared
    /// (unless another root still reports against them — see
    /// [`LspState::uri_published_elsewhere`]).
    async fn refresh_diagnostics(&self, root_file_id: FileId) {
        let (publish, stale, versions, log_error) = {
            let mut state = self.state.lock().await;
            collect_diagnostics_for_root(&mut state, root_file_id)
        };

        if let Some(message) = log_error {
            self.client.log_message(MessageType::ERROR, message).await;
        }
        for (uri, diagnostics) in publish {
            let version = versions.get(&uri).copied().flatten();
            self.client
                .publish_diagnostics(uri, diagnostics, version)
                .await;
        }
        for uri in stale {
            let version = versions.get(&uri).copied().flatten();
            self.client
                .publish_diagnostics(uri, Vec::new(), version)
                .await;
        }
    }

    async fn symbol_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<(IdeSymbol, Range)> {
        let mut state = self.state.lock().await;
        let (symbol, _) = symbol_at_document_position(&mut state, uri, position)?;
        let range = range_from_span(
            state.snapshot.source_text(symbol.file_id)?.as_ref(),
            symbol.span,
        )?;
        Some((symbol, range))
    }
}

fn collect_diagnostics_for_root(state: &mut LspState, root_file_id: FileId) -> DiagnosticsForRoot {
    let mut grouped: LspDiagnosticMap = HashMap::new();
    let mut current = HashSet::new();
    let mut log_error = None;

    match state.file_kind(root_file_id) {
        Some(ProjectFileKind::QaScript) => {
            collect_qa_diagnostics_for_root(state, root_file_id, &mut current, &mut grouped);
        }
        Some(ProjectFileKind::AbideSource) => match state.snapshot.diagnostics(root_file_id) {
            Ok(diagnostics) => {
                for diagnostic in diagnostics.iter() {
                    collect_lsp_diagnostic(
                        state,
                        root_file_id,
                        diagnostic,
                        &mut current,
                        &mut grouped,
                    );
                }

                if state.verification_policy.should_run_automatically() {
                    match state.snapshot.lower(root_file_id) {
                        Ok(lowered) => {
                            let config = verify_config_for_editor_policy(state.verification_policy);
                            let results = abide::verify::verify_function_contracts_only(
                                &lowered.ir_program,
                                &config,
                            );
                            for diagnostic in abide::verify::verification_diagnostics(&results) {
                                collect_lsp_diagnostic(
                                    state,
                                    root_file_id,
                                    &diagnostic,
                                    &mut current,
                                    &mut grouped,
                                );
                            }
                        }
                        Err(error) => {
                            log_error = Some(format!("failed to refresh diagnostics: {error:?}"));
                        }
                    }
                }
            }
            Err(error) => {
                log_error = Some(format!("failed to refresh diagnostics: {error:?}"));
            }
        },
        Some(ProjectFileKind::Unsupported) | None => {}
    }

    let previous = state
        .published_by_root
        .insert(root_file_id, current.clone())
        .unwrap_or_default();
    let stale_uris: Vec<_> = previous
        .difference(&current)
        .filter(|uri| !state.uri_published_elsewhere(root_file_id, uri))
        .cloned()
        .collect();
    let versions = state
        .documents
        .keys()
        .cloned()
        .map(|uri| {
            let version = state.document_version(&uri);
            (uri, version)
        })
        .collect::<HashMap<_, _>>();
    (grouped, stale_uris, versions, log_error)
}

fn collect_qa_diagnostics_for_root(
    state: &mut LspState,
    root_file_id: FileId,
    current: &mut HashSet<Url>,
    grouped: &mut HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>,
) {
    if let Ok(diagnostics) = state.snapshot.diagnostics(root_file_id) {
        for diagnostic in diagnostics.iter() {
            collect_lsp_diagnostic(state, root_file_id, diagnostic, current, grouped);
        }
    }
}

fn is_qa_document_path(path: &Path) -> bool {
    path.extension()
        .and_then(std::ffi::OsStr::to_str)
        .is_some_and(|extension| extension.eq_ignore_ascii_case("qa"))
}

fn collect_lsp_diagnostic(
    state: &LspState,
    root_file_id: FileId,
    diagnostic: &Diagnostic,
    current: &mut HashSet<Url>,
    grouped: &mut HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>,
) {
    let Some((uri, lsp_diagnostic)) =
        diagnostic_to_lsp(&state.snapshot.workspace, root_file_id, diagnostic)
    else {
        return;
    };
    current.insert(uri.clone());
    grouped.entry(uri).or_default().push(lsp_diagnostic);
}

fn qa_run_command_uri_arg(arguments: &[serde_json::Value]) -> std::result::Result<Url, String> {
    let Some(first) = arguments.first() else {
        return Err("expected document URI argument".to_owned());
    };
    if let Some(uri) = first.as_str() {
        return Url::parse(uri).map_err(|error| format!("invalid document URI: {error}"));
    }
    if let Some(uri) = first.get("uri").and_then(serde_json::Value::as_str) {
        return Url::parse(uri).map_err(|error| format!("invalid document URI: {error}"));
    }
    Err("expected document URI string or object with `uri`".to_owned())
}

#[cfg(test)]
fn run_qa_script_for_uri(
    state: &LspState,
    uri: &Url,
) -> std::result::Result<serde_json::Value, String> {
    let (path, source) = qa_run_source_for_uri(state, uri)?;
    Ok(run_qa_source_to_json(&path, &source))
}

fn qa_run_source_for_uri(
    state: &LspState,
    uri: &Url,
) -> std::result::Result<(PathBuf, String), String> {
    let path = uri
        .to_file_path()
        .map_err(|()| "QA run command requires a file URI".to_owned())?;
    if !is_qa_document_path(&path) {
        return Err("QA run command requires a .qa document".to_owned());
    }
    let source = if let Some(document) = state.documents.get(uri) {
        state
            .snapshot
            .source_text(document.file_id)
            .map(|source| source.to_string())
            .ok_or_else(|| "open QA document source is unavailable".to_owned())?
    } else {
        std::fs::read_to_string(&path)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?
    };
    Ok((path, source))
}

fn run_qa_source_to_json(path: &Path, source: &str) -> serde_json::Value {
    let result = abide::qa::runner::run_qa_source(path, source, None, false);
    serde_json::json!({
        "passed": result.passed,
        "failed": result.failed,
        "executed": result.executed,
        "output": result.output,
        "diagnostics": result.diagnostics,
    })
}

fn diagnostic_to_lsp(
    workspace: &CompilerWorkspace,
    root_file_id: FileId,
    diagnostic: &Diagnostic,
) -> Option<(Url, tower_lsp::lsp_types::Diagnostic)> {
    let file_path = diagnostic
        .file
        .as_deref()
        .map(PathBuf::from)
        .or_else(|| workspace.path(root_file_id).map(Path::to_path_buf))?;
    let source = source_for_path(workspace, &file_path)?;
    let range = diagnostic
        .span
        .and_then(|span| range_from_span(&source, span))
        .unwrap_or_else(|| Range::new(Position::new(0, 0), Position::new(0, 0)));

    Some((
        Url::from_file_path(&file_path).ok()?,
        tower_lsp::lsp_types::Diagnostic {
            range,
            severity: Some(match diagnostic.severity {
                DiagnosticSeverity::Error => tower_lsp::lsp_types::DiagnosticSeverity::ERROR,
                DiagnosticSeverity::Warning => tower_lsp::lsp_types::DiagnosticSeverity::WARNING,
                DiagnosticSeverity::Info => tower_lsp::lsp_types::DiagnosticSeverity::INFORMATION,
                DiagnosticSeverity::Hint => tower_lsp::lsp_types::DiagnosticSeverity::HINT,
            }),
            code: diagnostic
                .code
                .as_ref()
                .map(|code| NumberOrString::String(code.clone())),
            code_description: None,
            source: Some("abide".to_owned()),
            message: diagnostic.message.clone(),
            related_information: related_information(workspace, diagnostic),
            tags: None,
            data: None,
        },
    ))
}

fn quickfix_actions_requested(only: Option<&[CodeActionKind]>) -> bool {
    only.is_none_or(|kinds| kinds.iter().any(|kind| kind == &CodeActionKind::QUICKFIX))
}

fn code_actions_for_document(
    state: &LspState,
    uri: &Url,
    diagnostics: &[tower_lsp::lsp_types::Diagnostic],
) -> Option<CodeActionResponse> {
    let file_id = state.documents.get(uri)?.file_id;
    let source = state.snapshot.source_text(file_id)?;
    let path = state.snapshot.path(file_id)?;
    let mut actions = Vec::new();

    for diagnostic in diagnostics {
        match diagnostic_code(diagnostic) {
            Some("abide::qa::semantic::missing_load") => {
                if let Some(action) = missing_load_code_action(path, source.as_ref(), diagnostic) {
                    actions.push(CodeActionOrCommand::CodeAction(action));
                }
            }
            Some("abide::qa::parse::unclosed_block") => {
                if let Some(action) =
                    close_qa_abide_block_code_action(uri, source.as_ref(), diagnostic)
                {
                    actions.push(CodeActionOrCommand::CodeAction(action));
                }
            }
            Some("abide::parse::expected") => {
                if let Some(action) =
                    removed_field_keyword_code_action(uri, source.as_ref(), diagnostic)
                {
                    actions.push(CodeActionOrCommand::CodeAction(action));
                }
            }
            _ => {}
        }
    }

    Some(actions)
}

fn missing_load_code_action(
    script_path: &Path,
    source: &str,
    diagnostic: &tower_lsp::lsp_types::Diagnostic,
) -> Option<CodeAction> {
    let (start, end) = range_to_offsets(source, diagnostic.range)?;
    let load_path = source.get(start..end)?;
    let script_dir = script_path.parent().unwrap_or_else(|| Path::new("."));
    let target = resolve_qa_load_path(script_dir, load_path);
    let target_uri = Url::from_file_path(target).ok()?;
    Some(quickfix_action(
        format!("Create missing load target `{load_path}`"),
        diagnostic,
        WorkspaceEdit {
            changes: None,
            document_changes: Some(DocumentChanges::Operations(vec![
                DocumentChangeOperation::Op(ResourceOp::Create(CreateFile {
                    uri: target_uri,
                    options: Some(CreateFileOptions {
                        overwrite: Some(false),
                        ignore_if_exists: Some(true),
                    }),
                    annotation_id: None,
                })),
            ])),
            change_annotations: None,
        },
        false,
    ))
}

fn close_qa_abide_block_code_action(
    uri: &Url,
    source: &str,
    diagnostic: &tower_lsp::lsp_types::Diagnostic,
) -> Option<CodeAction> {
    let eof = offset_to_position(source, source.len())?;
    let new_text = if source.ends_with('\n') {
        "}\n"
    } else {
        "\n}\n"
    };
    Some(quickfix_action(
        "Close QA abide block",
        diagnostic,
        single_file_edit(uri, Range::new(eof, eof), new_text),
        true,
    ))
}

fn removed_field_keyword_code_action(
    uri: &Url,
    source: &str,
    diagnostic: &tower_lsp::lsp_types::Diagnostic,
) -> Option<CodeAction> {
    if !diagnostic.message.contains("found `field`") {
        return None;
    }
    let (start, end) = range_to_offsets(source, diagnostic.range)?;
    if source.get(start..end)? != "field" {
        return None;
    }
    let delete_end = source
        .get(end..)
        .and_then(|suffix| suffix.chars().next())
        .filter(|ch| ch.is_whitespace())
        .map_or(end, |ch| end + ch.len_utf8());
    let range = Range::new(
        offset_to_position(source, start)?,
        offset_to_position(source, delete_end)?,
    );
    Some(quickfix_action(
        "Remove removed `field` keyword",
        diagnostic,
        single_file_edit(uri, range, ""),
        true,
    ))
}

fn quickfix_action(
    title: impl Into<String>,
    diagnostic: &tower_lsp::lsp_types::Diagnostic,
    edit: WorkspaceEdit,
    is_preferred: bool,
) -> CodeAction {
    CodeAction {
        title: title.into(),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![diagnostic.clone()]),
        edit: Some(edit),
        command: None,
        is_preferred: Some(is_preferred),
        disabled: None,
        data: None,
    }
}

fn single_file_edit(uri: &Url, range: Range, new_text: impl Into<String>) -> WorkspaceEdit {
    WorkspaceEdit {
        changes: Some(HashMap::from([(
            uri.clone(),
            vec![TextEdit {
                range,
                new_text: new_text.into(),
            }],
        )])),
        document_changes: None,
        change_annotations: None,
    }
}

fn diagnostic_code(diagnostic: &tower_lsp::lsp_types::Diagnostic) -> Option<&str> {
    match diagnostic.code.as_ref()? {
        NumberOrString::String(code) => Some(code.as_str()),
        NumberOrString::Number(_) => None,
    }
}

fn range_to_offsets(source: &str, range: Range) -> Option<(usize, usize)> {
    Some((
        position_to_offset(source, range.start)?,
        position_to_offset(source, range.end)?,
    ))
}

fn related_information(
    workspace: &CompilerWorkspace,
    diagnostic: &Diagnostic,
) -> Option<Vec<DiagnosticRelatedInformation>> {
    let infos: Vec<_> = diagnostic
        .related
        .iter()
        .filter_map(|related| {
            let file_path = related.file.as_deref().map(PathBuf::from)?;
            let source = source_for_path(workspace, &file_path)?;
            let span = related.span?;
            let range = range_from_span(&source, span)?;
            let uri = Url::from_file_path(file_path).ok()?;
            Some(DiagnosticRelatedInformation {
                location: Location { uri, range },
                message: related.message.clone(),
            })
        })
        .collect();
    (!infos.is_empty()).then_some(infos)
}

#[cfg(test)]
fn definition_locations(
    workspace: &CompilerWorkspace,
    index: &abide::ide::WorkspaceIndex,
    name: &str,
) -> Vec<Location> {
    index
        .symbols_named(name)
        .into_iter()
        .filter_map(|symbol| location_for_span(workspace, symbol.file_id, symbol.span))
        .collect()
}

fn symbol_at_document_position(
    state: &mut LspState,
    uri: &Url,
    position: Position,
) -> Option<(IdeSymbol, abide::ide::IdeOccurrence)> {
    let file_id = state.documents.get(uri)?.file_id;
    let source = state.snapshot.source_text(file_id)?;
    let offset = position_to_offset(source.as_ref(), position)?;
    let occurrence = state.snapshot.identifier_at(file_id, offset).ok()??;
    let index = state.snapshot.workspace_index().ok()?;
    let symbol = resolve_occurrence_symbol(&state.snapshot, &index, &occurrence)?;
    Some((symbol, occurrence))
}

fn occurrence_resolves_to_symbol(
    snapshot: &ProjectSnapshot,
    index: &WorkspaceIndex,
    occurrence: &abide::ide::IdeOccurrence,
    target: &IdeSymbol,
) -> bool {
    resolve_occurrence_symbol(snapshot, index, occurrence)
        .is_some_and(|symbol| same_symbol_identity(&symbol, target))
}

fn reference_locations_for_symbol(
    snapshot: &ProjectSnapshot,
    index: &WorkspaceIndex,
    symbol: &IdeSymbol,
    include_declaration: bool,
) -> Vec<Location> {
    let definition = location_for_span(&snapshot.workspace, symbol.file_id, symbol.span);
    index
        .occurrences
        .iter()
        .filter(|occurrence| occurrence_resolves_to_symbol(snapshot, index, occurrence, symbol))
        .filter_map(|occurrence| {
            location_for_span(&snapshot.workspace, occurrence.file_id, occurrence.span)
        })
        .filter(|location| include_declaration || Some(location) != definition.as_ref())
        .collect()
}

fn rename_changes_for_symbol(
    snapshot: &ProjectSnapshot,
    index: &WorkspaceIndex,
    symbol: &IdeSymbol,
    new_name: &str,
) -> HashMap<Url, Vec<TextEdit>> {
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for occurrence in &index.occurrences {
        if occurrence_resolves_to_symbol(snapshot, index, occurrence, symbol) {
            if let Some((uri, range)) =
                uri_and_range_for_span(&snapshot.workspace, occurrence.file_id, occurrence.span)
            {
                changes.entry(uri).or_default().push(TextEdit {
                    range,
                    new_text: new_name.to_owned(),
                });
            }
        }
    }
    changes
}

fn resolve_occurrence_symbol(
    snapshot: &ProjectSnapshot,
    index: &WorkspaceIndex,
    occurrence: &abide::ide::IdeOccurrence,
) -> Option<IdeSymbol> {
    let source = snapshot.source_text(occurrence.file_id)?;
    if let Some(symbol) = symbol_declared_at(index, occurrence) {
        return Some(symbol.clone());
    }

    if let Some(qualifier) = qualifier_before_scope(source.as_ref(), occurrence.span.start) {
        return best_symbol_match(
            index
                .module_exports(&qualifier)
                .into_iter()
                .chain(index.enum_variants_by_type(&qualifier))
                .filter(|symbol| symbol.name == occurrence.name),
            occurrence.file_id,
        )
        .cloned();
    }

    if let Some(owner) = qualifier_before_dot(source.as_ref(), occurrence.span.start) {
        return best_symbol_match(
            index
                .members_by_owner(&owner)
                .into_iter()
                .filter(|symbol| symbol.name == occurrence.name),
            occurrence.file_id,
        )
        .cloned();
    }

    let visible = index.visible_symbols(occurrence.file_id, occurrence.span.start);
    best_symbol_match(
        visible
            .iter()
            .filter(|symbol| symbol.name == occurrence.name),
        occurrence.file_id,
    )
    .cloned()
    .or_else(|| {
        best_symbol_match(index.symbols_named(&occurrence.name), occurrence.file_id).cloned()
    })
}

fn symbol_declared_at<'a>(
    index: &'a WorkspaceIndex,
    occurrence: &abide::ide::IdeOccurrence,
) -> Option<&'a IdeSymbol> {
    index.symbols.iter().find(|symbol| {
        symbol.file_id == occurrence.file_id
            && symbol.span == occurrence.span
            && symbol.name == occurrence.name
    })
}

fn best_symbol_match<'a, I>(symbols: I, file_id: FileId) -> Option<&'a IdeSymbol>
where
    I: IntoIterator<Item = &'a IdeSymbol>,
{
    symbols.into_iter().min_by_key(|symbol| {
        (
            usize::from(symbol.file_id != file_id),
            symbol.kind.sort_rank(),
            symbol.name.as_str(),
        )
    })
}

fn same_symbol_identity(left: &IdeSymbol, right: &IdeSymbol) -> bool {
    left.file_id == right.file_id
        && left.span == right.span
        && left.kind == right.kind
        && left.owner == right.owner
        && left.module == right.module
}

fn source_for_path(workspace: &CompilerWorkspace, path: &Path) -> Option<String> {
    let file_id = workspace.file_id(path)?;
    Some(workspace.source_text(file_id)?.to_string())
}

fn location_for_span(
    workspace: &CompilerWorkspace,
    file_id: FileId,
    span: abide::span::Span,
) -> Option<Location> {
    let (uri, range) = uri_and_range_for_span(workspace, file_id, span)?;
    Some(Location { uri, range })
}

fn uri_and_range_for_span(
    workspace: &CompilerWorkspace,
    file_id: FileId,
    span: abide::span::Span,
) -> Option<(Url, Range)> {
    let path = workspace.path(file_id)?;
    let source = workspace.source_text(file_id)?;
    let uri = Url::from_file_path(path).ok()?;
    let range = range_from_span(source.as_ref(), span)?;
    Some((uri, range))
}

fn completion_item_for_symbol(symbol: &IdeSymbol) -> CompletionItem {
    CompletionItem {
        label: symbol.name.clone(),
        kind: Some(match symbol.kind {
            IdeSymbolKind::Type
            | IdeSymbolKind::Record
            | IdeSymbolKind::Alias
            | IdeSymbolKind::Newtype
            | IdeSymbolKind::Interface => CompletionItemKind::CLASS,
            IdeSymbolKind::Variant => CompletionItemKind::ENUM_MEMBER,
            IdeSymbolKind::Entity => CompletionItemKind::STRUCT,
            IdeSymbolKind::Field | IdeSymbolKind::Derived => CompletionItemKind::FIELD,
            IdeSymbolKind::Action
            | IdeSymbolKind::Command
            | IdeSymbolKind::Query
            | IdeSymbolKind::Proc => CompletionItemKind::METHOD,
            IdeSymbolKind::Pred
            | IdeSymbolKind::Prop
            | IdeSymbolKind::Verify
            | IdeSymbolKind::Theorem
            | IdeSymbolKind::Lemma
            | IdeSymbolKind::Scene
            | IdeSymbolKind::Axiom
            | IdeSymbolKind::Const
            | IdeSymbolKind::Function => CompletionItemKind::FUNCTION,
            IdeSymbolKind::Module | IdeSymbolKind::System | IdeSymbolKind::Program => {
                CompletionItemKind::MODULE
            }
            IdeSymbolKind::Invariant => CompletionItemKind::PROPERTY,
        }),
        detail: Some(symbol.detail.clone()),
        ..CompletionItem::default()
    }
}

fn completion_items_for_open_document(
    state: &mut LspState,
    uri: &Url,
    position: Position,
) -> Option<Vec<CompletionItem>> {
    let file_id = state.documents.get(uri)?.file_id;
    let source = state.snapshot.source_text(file_id)?;
    let offset = position_to_offset(source.as_ref(), position)?;
    let path = state.snapshot.path(file_id)?.to_path_buf();

    if is_qa_document_path(&path) {
        if let Some(block) = embedded_abide_block_at(source.as_ref(), offset) {
            return Some(embedded_qa_abide_completion_items(
                state,
                &path,
                source.as_ref(),
                &block,
                offset,
            ));
        }
        return Some(qa_completion_items_for_document(
            state,
            &path,
            source.as_ref(),
            offset,
        ));
    }

    Some(abide_completion_items_for_source(
        state,
        Some(file_id),
        source.as_ref(),
        offset,
    ))
}

fn embedded_abide_block_at(
    source: &str,
    offset: usize,
) -> Option<abide::qa::parse::QAEmbeddedAbideBlock> {
    embedded_abide_block_at_tolerant(source, offset).or_else(|| {
        abide::qa::parse::embedded_abide_blocks(source)
            .ok()?
            .into_iter()
            .find(|block| offset >= block.body_span.start && offset <= block.body_span.end)
    })
}

fn embedded_abide_block_at_tolerant(
    source: &str,
    offset: usize,
) -> Option<abide::qa::parse::QAEmbeddedAbideBlock> {
    let offset = offset.min(source.len());
    let prefix = &source[..offset];
    let marker = prefix.rfind("abide")?;
    let after_marker = &source[marker..];
    let open_relative = after_marker.find('{')?;
    let body_start = marker + open_relative + 1;
    if offset < body_start {
        return None;
    }
    let body_end = find_matching_brace(source, body_start - 1).unwrap_or(source.len());
    if offset > body_end {
        return None;
    }
    Some(abide::qa::parse::QAEmbeddedAbideBlock {
        body: source[body_start..body_end].to_owned(),
        body_span: abide::span::Span {
            start: body_start,
            end: body_end,
        },
    })
}

fn find_matching_brace(source: &str, open_offset: usize) -> Option<usize> {
    let mut depth = 0_u32;
    for (offset, ch) in source[open_offset..].char_indices() {
        match ch {
            '{' => depth = depth.saturating_add(1),
            '}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(open_offset + offset);
                }
            }
            _ => {}
        }
    }
    None
}

fn abide_completion_items_for_source(
    state: &mut LspState,
    file_id: Option<FileId>,
    source: &str,
    offset: usize,
) -> Vec<CompletionItem> {
    let context = completion_context(source, offset);
    let keyword_context = keyword_completion_context(source, offset);
    let mut items = keyword_completions(context, keyword_context);
    if let Ok(index) = state.snapshot.workspace_index() {
        items.extend(completion_symbols_for_context(
            &index, file_id, source, offset, context,
        ));
    }
    items
}

fn completion_symbols_for_context(
    index: &WorkspaceIndex,
    file_id: Option<FileId>,
    source: &str,
    offset: usize,
    context: CompletionContext,
) -> Vec<CompletionItem> {
    let symbols = match context {
        CompletionContext::General => file_id.map_or_else(
            || {
                index
                    .completion_symbols(context)
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>()
            },
            |file_id| {
                index
                    .visible_symbols(file_id, offset)
                    .into_iter()
                    .filter(is_general_completion_symbol)
                    .collect::<Vec<_>>()
            },
        ),
        CompletionContext::AfterAt => index
            .completion_symbols(context)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>(),
        CompletionContext::AfterDot => qualifier_before_dot(source, offset).map_or_else(
            || {
                index
                    .completion_symbols(context)
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>()
            },
            |owner| {
                index
                    .members_by_owner(&owner)
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>()
            },
        ),
        CompletionContext::AfterScope => {
            qualifier_before_scope(source, offset).map_or_else(Vec::new, |owner| {
                let mut scoped = index
                    .module_exports(&owner)
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                scoped.extend(index.enum_variants_by_type(&owner).into_iter().cloned());
                scoped
            })
        }
    };

    symbols.iter().map(completion_item_for_symbol).collect()
}

fn embedded_qa_abide_completion_items(
    state: &mut LspState,
    script_path: &Path,
    script_source: &str,
    block: &abide::qa::parse::QAEmbeddedAbideBlock,
    offset: usize,
) -> Vec<CompletionItem> {
    let body_offset = offset.saturating_sub(block.body_span.start);
    let context = completion_context(&block.body, body_offset);
    let keyword_context = keyword_completion_context(&block.body, body_offset);
    let mut items = keyword_completions(context, keyword_context);

    let Some(index) =
        loaded_qa_workspace_index(state, script_path, script_source, Some(&block.body))
    else {
        return items;
    };
    items.extend(completion_symbols_for_context(
        &index,
        None,
        &block.body,
        body_offset,
        context,
    ));
    items
}

fn is_general_completion_symbol(symbol: &IdeSymbol) -> bool {
    matches!(
        symbol.kind,
        IdeSymbolKind::Type
            | IdeSymbolKind::Record
            | IdeSymbolKind::Alias
            | IdeSymbolKind::Newtype
            | IdeSymbolKind::Entity
            | IdeSymbolKind::Interface
            | IdeSymbolKind::System
            | IdeSymbolKind::Program
            | IdeSymbolKind::Proc
            | IdeSymbolKind::Pred
            | IdeSymbolKind::Prop
            | IdeSymbolKind::Const
            | IdeSymbolKind::Function
    )
}

fn qualifier_before_dot(source: &str, offset: usize) -> Option<String> {
    qualifier_before_trigger(source, offset, ".")
}

fn qualifier_before_scope(source: &str, offset: usize) -> Option<String> {
    qualifier_before_trigger(source, offset, "::")
}

fn qualifier_before_trigger(source: &str, offset: usize, trigger: &str) -> Option<String> {
    let offset = offset.min(source.len());
    let prefix = source.get(..offset)?.trim_end_matches(char::is_whitespace);
    let before_trigger = prefix.strip_suffix(trigger)?;
    let end = before_trigger.len();
    let start = before_trigger[..end]
        .char_indices()
        .rev()
        .find_map(|(index, ch)| {
            if ch == '_' || ch.is_ascii_alphanumeric() {
                None
            } else {
                Some(index + ch.len_utf8())
            }
        })
        .unwrap_or(0);
    let qualifier = before_trigger[start..].trim();
    (!qualifier.is_empty()).then(|| qualifier.to_owned())
}

fn qa_completion_items(source: &str, offset: usize) -> Vec<CompletionItem> {
    let candidates = match qa_completion_context(source, offset) {
        QACompletionContext::Command => qa_command_candidates(),
        QACompletionContext::Query => qa_query_subcommand_candidates(),
        QACompletionContext::LoadPath | QACompletionContext::None => Vec::new(),
    };
    candidates
        .into_iter()
        .map(|label| CompletionItem {
            label,
            kind: Some(CompletionItemKind::KEYWORD),
            ..CompletionItem::default()
        })
        .collect()
}

fn qa_completion_items_for_document(
    state: &mut LspState,
    path: &Path,
    source: &str,
    offset: usize,
) -> Vec<CompletionItem> {
    if let Some(kind) = qa_model_reference_completion_kind(source, offset) {
        if let Some(model) = loaded_qa_flow_model(path, source) {
            return qa_model_reference_completion_items(&model, kind);
        }
    }

    match qa_completion_context(source, offset) {
        QACompletionContext::LoadPath => qa_load_path_completion_items(state, path, source, offset),
        _ => qa_completion_items(source, offset),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QaModelReferenceCompletionKind {
    GraphableField,
    System,
}

fn qa_model_reference_completion_kind(
    source: &str,
    offset: usize,
) -> Option<QaModelReferenceCompletionKind> {
    let line = current_line_prefix(source, offset);
    if !line.ends_with(char::is_whitespace) {
        return None;
    }
    let words = line.split_whitespace().collect::<Vec<_>>();
    match words.as_slice() {
        ["ask" | "explain" | "assert", "reachable" | "path" | "terminal" | "initial" | "cycles" | "transitions" | "updates"
        | "events" | "match-coverage"] => Some(QaModelReferenceCompletionKind::GraphableField),
        ["ask" | "explain" | "assert", "deadlock"] => Some(QaModelReferenceCompletionKind::System),
        ["ask" | "explain" | "assert", "cross-calls", "from"] => {
            Some(QaModelReferenceCompletionKind::System)
        }
        _ => None,
    }
}

fn qa_model_reference_completion_items(
    model: &FlowModel,
    kind: QaModelReferenceCompletionKind,
) -> Vec<CompletionItem> {
    match kind {
        QaModelReferenceCompletionKind::GraphableField => {
            let mut labels = model
                .field_graph_meta
                .values()
                .filter(|meta| meta.graphable)
                .map(|meta| format!("{}.{}", meta.owner, meta.field))
                .collect::<Vec<_>>();
            labels.sort();
            labels.dedup();
            labels
                .into_iter()
                .map(|label| CompletionItem {
                    label,
                    kind: Some(CompletionItemKind::FIELD),
                    ..CompletionItem::default()
                })
                .collect()
        }
        QaModelReferenceCompletionKind::System => {
            let mut labels = model.system_names.clone();
            labels.sort();
            labels.dedup();
            labels
                .into_iter()
                .map(|label| CompletionItem {
                    label,
                    kind: Some(CompletionItemKind::MODULE),
                    ..CompletionItem::default()
                })
                .collect()
        }
    }
}

fn qa_load_path_completion_items(
    state: &LspState,
    script_path: &Path,
    source: &str,
    offset: usize,
) -> Vec<CompletionItem> {
    let prefix = qa_load_path_prefix(source, offset);
    let script_dir = script_path.parent().unwrap_or_else(|| Path::new("."));
    state
        .snapshot
        .project
        .files
        .values()
        .filter(|file| file.kind == ProjectFileKind::AbideSource)
        .map(|file| relative_load_label(script_dir, &file.path))
        .filter(|label| {
            prefix
                .as_ref()
                .is_none_or(|prefix| label.starts_with(prefix))
        })
        .map(|label| CompletionItem {
            label,
            kind: Some(CompletionItemKind::FILE),
            ..CompletionItem::default()
        })
        .collect()
}

fn qa_load_path_prefix(source: &str, offset: usize) -> Option<String> {
    let line = current_line_prefix(source, offset);
    let quote = line.find('"')?;
    Some(line[quote + 1..].to_owned())
}

fn relative_load_label(base: &Path, path: &Path) -> String {
    let relative = path.strip_prefix(base).ok().unwrap_or(path);
    relative
        .to_string_lossy()
        .replace(std::path::MAIN_SEPARATOR, "/")
}

fn loaded_qa_flow_model(script_path: &Path, source: &str) -> Option<FlowModel> {
    let paths = qa_load_paths(script_path, source);
    if paths.is_empty() {
        return None;
    }
    build_flow_model_from_paths(&paths).ok()
}

fn loaded_qa_workspace_index(
    state: &mut LspState,
    script_path: &Path,
    source: &str,
    overlay_source: Option<&str>,
) -> Option<WorkspaceIndex> {
    let mut workspace =
        CompilerWorkspace::with_root_dir(state.snapshot.project.root().to_path_buf());
    for path in qa_load_paths(script_path, source) {
        let source = snapshot_source_for_path(&state.snapshot, &path)?;
        workspace.set_file_source(path, source);
    }
    if let Some(source) = overlay_source {
        workspace.set_file_source("__qa_overlay.ab", source.to_owned());
    }
    build_workspace_index(&mut workspace).ok()
}

fn snapshot_source_for_path(snapshot: &ProjectSnapshot, path: &Path) -> Option<String> {
    if let Some(file_id) = snapshot.file_id(path) {
        return snapshot
            .source_text(file_id)
            .map(|source| source.as_ref().to_owned());
    }
    std::fs::read_to_string(path).ok()
}

fn qa_load_paths(script_path: &Path, source: &str) -> Vec<PathBuf> {
    let script_dir = script_path.parent().unwrap_or_else(|| Path::new("."));
    let mut paths = Vec::new();
    for line in source.lines() {
        let Some(path) = qa_load_path_from_line(line) else {
            continue;
        };
        let resolved = resolve_qa_load_path(script_dir, path);
        if resolved.is_dir() {
            collect_abide_files(&resolved, &mut paths);
        } else if resolved.exists() {
            paths.push(resolved);
        }
    }
    paths
}

fn qa_load_path_from_line(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    let rest = trimmed.strip_prefix("load")?.trim_start();
    let rest = rest.strip_prefix('"')?;
    let end = rest.find('"').unwrap_or(rest.len());
    Some(&rest[..end])
}

fn resolve_qa_load_path(script_dir: &Path, path: &str) -> PathBuf {
    let path = Path::new(path);
    if path.is_absolute() {
        path.to_owned()
    } else {
        script_dir.join(path)
    }
}

fn collect_abide_files(dir: &Path, paths: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries = entries
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if matches!(
            path.extension().and_then(std::ffi::OsStr::to_str),
            Some("ab" | "abi" | "abp")
        ) {
            paths.push(path);
        } else if path.is_dir() {
            collect_abide_files(&path, paths);
        }
    }
}

fn build_flow_model_from_paths(paths: &[PathBuf]) -> std::result::Result<FlowModel, Vec<String>> {
    let (mut env, load_errors, _all_paths) = abide::loader::load_files(paths);
    if !load_errors.is_empty() || !env.include_load_errors.is_empty() {
        return Err(Vec::new());
    }
    if paths.len() > 1 {
        env.module_name = None;
    }
    let (result, elab_errors) = abide::elab::elaborate_env(env);
    if elab_errors
        .iter()
        .any(|error| !matches!(error.severity, abide::elab::error::Severity::Warning))
    {
        return Err(Vec::new());
    }
    let (ir_program, lower_diagnostics) = abide::ir::lower(&result);
    if lower_diagnostics.has_errors() {
        return Err(Vec::new());
    }
    Ok(abide::qa::extract::extract(&ir_program))
}

fn current_line_prefix(source: &str, offset: usize) -> &str {
    let prefix = &source[..offset.min(source.len())];
    prefix.rsplit('\n').next().unwrap_or(prefix)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QACompletionContext {
    Command,
    Query,
    LoadPath,
    None,
}

fn qa_completion_context(source: &str, offset: usize) -> QACompletionContext {
    match classify_qa_cursor(source, offset) {
        QaCursorContext::Command => QACompletionContext::Command,
        QaCursorContext::Query => QACompletionContext::Query,
        QaCursorContext::LoadPath => QACompletionContext::LoadPath,
        QaCursorContext::EmbeddedAbide(_) | QaCursorContext::None => QACompletionContext::None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KeywordCompletionContext {
    General,
    Contract,
}

fn keyword_completion_context(source: &str, offset: usize) -> KeywordCompletionContext {
    if matches!(
        classify_abide_cursor(source, offset),
        AbideCursorContext::FunctionContract
            | AbideCursorContext::ActionContract
            | AbideCursorContext::CommandContract
            | AbideCursorContext::ProcContract
    ) {
        KeywordCompletionContext::Contract
    } else {
        KeywordCompletionContext::General
    }
}

const GENERAL_KEYWORD_COMPLETIONS: &[&str] = &[
    "module",
    "include",
    "as",
    "use",
    "const",
    "fn",
    "type",
    "enum",
    "struct",
    "entity",
    "interface",
    "extern",
    "system",
    "implements",
    "dep",
    "action",
    "command",
    "query",
    "store",
    "activate",
    "return",
    "needs",
    "fair",
    "strong",
    "stutter",
    "when",
    "may",
    "else",
    "where",
    "choose",
    "for",
    "create",
    "program",
    "proc",
    "pred",
    "prop",
    "verify",
    "assert",
    "invariant",
    "show",
    "theorem",
    "lemma",
    "axiom",
    "scene",
    "given",
    "match",
    "if",
    "let",
    "one",
    "assume",
    "then",
    "requires",
    "ensures",
    "decreases",
    "var",
    "while",
    "all",
    "exists",
    "some",
    "no",
    "lone",
    "always",
    "eventually",
    "historically",
    "once",
    "previously",
    "since",
    "until",
    "true",
    "false",
    "not",
    "and",
    "or",
    "implies",
    "in",
    "sorry",
    "todo",
    "by",
    "mut",
    "derived",
    "fsm",
    "under",
    "saw",
    "sum",
    "product",
    "min",
    "max",
    "count",
];

fn keyword_completions(
    context: CompletionContext,
    keyword_context: KeywordCompletionContext,
) -> Vec<CompletionItem> {
    let keywords: &[&str] = match context {
        CompletionContext::General => GENERAL_KEYWORD_COMPLETIONS,
        CompletionContext::AfterAt
        | CompletionContext::AfterDot
        | CompletionContext::AfterScope => &[],
    };
    keywords
        .iter()
        .map(|keyword| CompletionItem {
            label: (*keyword).to_owned(),
            kind: Some(CompletionItemKind::KEYWORD),
            sort_text: Some(keyword_sort_text(keyword, keyword_context)),
            ..CompletionItem::default()
        })
        .collect()
}

fn keyword_sort_text(keyword: &str, context: KeywordCompletionContext) -> String {
    let priority = match (context, keyword) {
        (KeywordCompletionContext::Contract, "requires") => "00",
        (KeywordCompletionContext::Contract, "ensures") => "01",
        (KeywordCompletionContext::Contract, "decreases") => "02",
        (KeywordCompletionContext::General, "requires" | "ensures" | "decreases") => "40",
        _ => "20",
    };
    format!("{priority}_{keyword}")
}

/// Translates an LSP (line, character) [`Position`] to a byte offset
/// into `source`.
///
/// LSP characters are UTF-16 code units in spec but most clients emit
/// UTF-8 code units; we follow the source verbatim using
/// [`str::char_indices`], which matches the rest of the compiler's
/// span model. Returns `None` when the position is past EOF.
fn position_to_offset(source: &str, position: Position) -> Option<usize> {
    let mut line = 0_u32;
    let mut offset = 0_usize;
    for segment in source.split_inclusive('\n') {
        if line == position.line {
            let character = usize::try_from(position.character).ok()?;
            let mut chars = segment.char_indices();
            return Some(
                chars
                    .nth(character)
                    .map_or(offset + segment.trim_end_matches('\n').len(), |(idx, _)| {
                        offset + idx
                    }),
            );
        }
        offset += segment.len();
        line += 1;
    }
    if line == position.line {
        Some(offset)
    } else {
        None
    }
}

/// Maps an Abide byte-offset span into an LSP [`Range`] by resolving
/// each endpoint with [`offset_to_position`].
fn range_from_span(source: &str, span: abide::span::Span) -> Option<Range> {
    Some(Range {
        start: offset_to_position(source, span.start)?,
        end: offset_to_position(source, span.end)?,
    })
}

/// Inverse of [`position_to_offset`]: walks `source` counting
/// newlines to recover the (line, column) coordinates of `offset`.
fn offset_to_position(source: &str, offset: usize) -> Option<Position> {
    if offset > source.len() {
        return None;
    }
    let mut line = 0_u32;
    let mut line_start = 0_usize;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
        }
    }
    let character = source[line_start..offset].chars().count();
    Some(Position::new(line, u32::try_from(character).ok()?))
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let (service, socket) = LspService::new(|client| Backend {
        client,
        state: Arc::new(Mutex::new(LspState::new(
            std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
        ))),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn only_code_action<'a>(actions: &'a [CodeActionOrCommand], title: &str) -> &'a CodeAction {
        let matches = actions
            .iter()
            .filter_map(|action| match action {
                CodeActionOrCommand::CodeAction(action) if action.title == title => Some(action),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            matches.len(),
            1,
            "expected exactly one `{title}` code action: {actions:#?}"
        );
        matches[0]
    }

    #[test]
    fn project_discovery_classifies_supported_files_under_root() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        std::fs::create_dir_all(root.join("src/nested")).expect("create dirs");
        std::fs::write(root.join("src/model.ab"), "module Commerce\n").expect("write ab");
        std::fs::write(root.join("src/body.abi"), "module Commerce\n").expect("write abi");
        std::fs::write(root.join("src/proof.abp"), "module Commerce\n").expect("write abp");
        std::fs::write(root.join("src/checks.qa"), "ask entities\n").expect("write qa");
        std::fs::write(root.join("src/nested/readme.md"), "# ignore\n").expect("write md");

        let project = ProjectModel::discover(root).expect("discover project");

        assert_eq!(project.root(), root);
        assert_eq!(
            project
                .files
                .get(&normalize_path_lexical(&root.join("src/model.ab")))
                .map(|file| file.kind),
            Some(ProjectFileKind::AbideSource)
        );
        assert_eq!(
            project
                .files
                .get(&normalize_path_lexical(&root.join("src/body.abi")))
                .map(|file| file.kind),
            Some(ProjectFileKind::AbideSource)
        );
        assert_eq!(
            project
                .files
                .get(&normalize_path_lexical(&root.join("src/proof.abp")))
                .map(|file| file.kind),
            Some(ProjectFileKind::AbideSource)
        );
        assert_eq!(
            project
                .files
                .get(&normalize_path_lexical(&root.join("src/checks.qa")))
                .map(|file| file.kind),
            Some(ProjectFileKind::QaScript)
        );
        assert_eq!(
            ProjectFileKind::for_path(root.join("src/nested/readme.md").as_path()),
            ProjectFileKind::Unsupported
        );
        assert!(!project
            .files
            .contains_key(&normalize_path_lexical(&root.join("../outside.ab"))));

        let files = project.files().collect::<Vec<_>>();
        assert_eq!(
            files
                .iter()
                .filter(|file| file.kind == ProjectFileKind::AbideSource)
                .count(),
            3
        );
        assert_eq!(
            files
                .iter()
                .filter(|file| file.kind == ProjectFileKind::QaScript)
                .count(),
            1
        );
    }

    #[test]
    fn lsp_state_discovers_project_files_but_keeps_qa_out_of_abide_indexing() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        std::fs::write(root.join("model.ab"), "entity Ticket { }\n").expect("write model");
        std::fs::write(root.join("queries.qa"), "load \"model.ab\"\nask entities\n")
            .expect("write qa");

        let mut state = LspState::new(root);

        assert_eq!(
            state.snapshot.file_kind(root.join("model.ab")),
            Some(ProjectFileKind::AbideSource)
        );
        assert_eq!(
            state.snapshot.file_kind(root.join("queries.qa")),
            Some(ProjectFileKind::QaScript)
        );
        assert!(state.snapshot.file_id(root.join("model.ab")).is_some());
        assert!(
            state.snapshot.file_id(root.join("queries.qa")).is_none(),
            "QA scripts should be known to the LSP project but not loaded into Abide-only indexing"
        );

        let index = state.snapshot.workspace_index().expect("workspace index");
        assert!(index
            .symbols_named("Ticket")
            .iter()
            .any(|symbol| symbol.kind == IdeSymbolKind::Entity));
        assert!(
            index
                .occurrences
                .iter()
                .all(|occurrence| occurrence.name != "load"),
            "QA source should not be indexed as Abide symbols: {index:#?}"
        );
    }

    #[test]
    fn lsp_state_records_open_unsupported_documents_without_indexing_them() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        let path = root.join("notes.txt");
        let uri = Url::from_file_path(&path).expect("file uri");
        let mut state = LspState::new(root);

        let file_id = state.upsert_open_document(&uri, 1, "not abide".to_owned());

        assert!(file_id.is_some());
        assert_eq!(
            state.snapshot.file_kind(&path),
            Some(ProjectFileKind::Unsupported)
        );
        assert!(state.snapshot.file_id(&path).is_some());
        let index = state.snapshot.workspace_index().expect("workspace index");
        assert!(
            index.occurrences.is_empty(),
            "unsupported documents may be tracked as open buffers but should not be indexed as Abide symbols"
        );
    }

    #[test]
    fn project_snapshot_reuses_parse_until_open_buffer_update() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        let path = root.join("model.ab");
        std::fs::write(&path, "entity Ticket { }\n").expect("write model");
        let uri = Url::from_file_path(&path).expect("file uri");
        let mut snapshot = ProjectSnapshot::discover(root).expect("snapshot");
        let file_id = snapshot.file_id(&path).expect("file id");

        let first = snapshot.parse(file_id).expect("first parse");
        let second = snapshot.parse(file_id).expect("second parse");
        assert!(
            Arc::ptr_eq(&first, &second),
            "unchanged parse queries should reuse the snapshot cache"
        );

        snapshot.upsert_open_document(&uri, 1, "entity Invoice { }\n".to_owned());
        let third = snapshot.parse(file_id).expect("updated parse");

        assert!(
            !Arc::ptr_eq(&first, &third),
            "open-buffer updates should invalidate cached parse results"
        );
        assert!(third.source.contains("Invoice"));
    }

    #[test]
    fn project_snapshot_reuses_diagnostics_until_open_buffer_update() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        let path = root.join("broken.ab");
        std::fs::write(&path, "entity Broken {\n  status:\n}\n").expect("write broken source");
        let uri = Url::from_file_path(&path).expect("file uri");
        let mut snapshot = ProjectSnapshot::discover(root).expect("snapshot");
        let file_id = snapshot.file_id(&path).expect("file id");

        let first = snapshot.diagnostics(file_id).expect("first diagnostics");
        let second = snapshot.diagnostics(file_id).expect("second diagnostics");
        assert!(
            Arc::ptr_eq(&first, &second),
            "unchanged diagnostics queries should reuse the snapshot cache"
        );
        assert!(
            !first.is_empty(),
            "broken source should produce diagnostics before the edit"
        );

        snapshot.upsert_open_document(&uri, 1, "entity Fixed { }\n".to_owned());
        let third = snapshot.diagnostics(file_id).expect("updated diagnostics");

        assert!(
            !Arc::ptr_eq(&first, &third),
            "open-buffer updates should invalidate cached diagnostics"
        );
        assert!(
            third.is_empty(),
            "fixed source should clear cached diagnostics: {third:#?}"
        );
    }

    #[test]
    fn project_snapshot_qa_diagnostics_include_embedded_abide_blocks() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        let qa_path = root.join("query.qa");
        let source = "ask entities\nabide {\n  entity Broken {\n    status: MissingType\n  }\n}\n";
        let mut snapshot = ProjectSnapshot::empty(root);
        let file_id = snapshot.set_file_source(&qa_path, source);

        let diagnostics = snapshot.diagnostics(file_id).expect("qa diagnostics");

        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("MissingType")),
            "snapshot QA diagnostics should include embedded Abide diagnostics: {diagnostics:#?}"
        );
    }

    #[test]
    fn project_snapshot_qa_diagnostics_recompute_after_loaded_abide_update() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        let model_path = root.join("model.ab");
        let qa_path = root.join("query.qa");
        std::fs::write(&model_path, "module Model\nentity Ticket { }\n").expect("write model");
        let qa_source = "load \"model.ab\"\nask terminal Ticket.status\n";
        std::fs::write(&qa_path, qa_source).expect("write qa");
        let model_uri = Url::from_file_path(&model_path).expect("model uri");
        let mut snapshot = ProjectSnapshot::discover(root).expect("snapshot");
        let qa_file_id = snapshot.set_file_source(&qa_path, qa_source);

        let before = snapshot
            .diagnostics(qa_file_id)
            .expect("initial qa diagnostics");
        assert!(
            before
                .iter()
                .any(|diagnostic| diagnostic.message.contains("Ticket.status")),
            "initial loaded model should not contain graphable Ticket.status: {before:#?}"
        );

        snapshot.upsert_open_document(
            &model_uri,
            1,
            "module Model\n\
             enum TicketStatus = Open | Closed\n\
             entity Ticket { status: TicketStatus = @Open }\n"
                .to_owned(),
        );
        let after = snapshot
            .diagnostics(qa_file_id)
            .expect("updated qa diagnostics");

        assert!(
            after.is_empty(),
            "QA diagnostics should be recomputed from loaded open-buffer sources: {after:#?}"
        );
    }

    #[test]
    fn project_snapshot_reuses_workspace_index_until_abide_source_update() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        let path = root.join("model.ab");
        std::fs::write(&path, "entity Ticket { }\n").expect("write model");
        let uri = Url::from_file_path(&path).expect("file uri");
        let mut snapshot = ProjectSnapshot::discover(root).expect("snapshot");

        let first = snapshot.workspace_index().expect("first index");
        let second = snapshot.workspace_index().expect("second index");
        assert!(
            Arc::ptr_eq(&first, &second),
            "unchanged workspace index queries should reuse the snapshot cache"
        );
        assert!(first
            .symbols_named("Ticket")
            .iter()
            .any(|symbol| symbol.kind == IdeSymbolKind::Entity));

        snapshot.upsert_open_document(&uri, 1, "entity Invoice { }\n".to_owned());
        let third = snapshot.workspace_index().expect("updated index");

        assert!(
            !Arc::ptr_eq(&first, &third),
            "Abide source updates should invalidate the workspace index"
        );
        assert!(third
            .symbols_named("Invoice")
            .iter()
            .any(|symbol| symbol.kind == IdeSymbolKind::Entity));
    }

    #[test]
    fn offset_position_roundtrip() {
        let source = "line1\nalpha beta\n";
        let offset = position_to_offset(source, Position::new(1, 3)).expect("offset");
        assert_eq!(
            offset_to_position(source, offset),
            Some(Position::new(1, 3))
        );
        assert_eq!(
            position_to_offset(source, Position::new(2, 0)),
            Some(source.len())
        );
        assert_eq!(position_to_offset(source, Position::new(3, 0)), None);
        assert_eq!(
            offset_to_position(source, source.len()),
            Some(Position::new(2, 0))
        );
        assert_eq!(offset_to_position(source, source.len() + 1), None);

        let final_line = "a\nbc";
        assert_eq!(position_to_offset(final_line, Position::new(1, 2)), Some(4));
        assert_eq!(offset_to_position(final_line, 4), Some(Position::new(1, 2)));
    }

    #[test]
    fn rejects_stale_document_versions() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/example.ab").expect("uri");
        let file_id = state
            .snapshot
            .set_file_source("/tmp/example.ab", "system S { }");
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 3,
            },
        );

        assert!(!state.should_accept_document_version(&uri, 2));
        assert!(!state.should_accept_document_version(&uri, 3));
        assert!(state.should_accept_document_version(&uri, 4));
        assert_eq!(state.document_version(&uri), Some(3));
        assert_eq!(
            state.document_version(&Url::parse("file:///tmp/missing.ab").expect("uri")),
            None
        );
    }

    #[test]
    fn published_diagnostics_track_other_roots_only() {
        let mut state = LspState::new(PathBuf::from("."));
        let root_a = state
            .snapshot
            .set_file_source("/tmp/a.ab", "system A { }".to_owned());
        let root_b = state
            .snapshot
            .set_file_source("/tmp/b.ab", "system B { }".to_owned());
        let shared_uri = Url::parse("file:///tmp/shared.ab").expect("uri");
        let other_uri = Url::parse("file:///tmp/other.ab").expect("uri");

        state
            .published_by_root
            .insert(root_a, HashSet::from([shared_uri.clone()]));
        state.published_by_root.insert(
            root_b,
            HashSet::from([shared_uri.clone(), other_uri.clone()]),
        );

        assert!(state.uri_published_elsewhere(root_a, &shared_uri));
        assert!(state.uri_published_elsewhere(root_b, &shared_uri));
        assert!(!state.uri_published_elsewhere(root_b, &other_uri));
        assert!(!state.uri_published_elsewhere(root_a, &Url::parse("file:///tmp/new.ab").unwrap()));
    }

    #[test]
    fn stale_diagnostics_clear_only_when_no_other_root_publishes_uri() {
        let mut state = LspState::new(PathBuf::from("."));
        let root_a = state
            .snapshot
            .set_file_source("/tmp/a.ab", "system A { }".to_owned());
        let root_b = state
            .snapshot
            .set_file_source("/tmp/b.ab", "system B { }".to_owned());
        let stale_uri = Url::parse("file:///tmp/stale.ab").expect("uri");
        let shared_uri = Url::parse("file:///tmp/shared.ab").expect("uri");

        state.published_by_root.insert(
            root_a,
            HashSet::from([stale_uri.clone(), shared_uri.clone()]),
        );
        state
            .published_by_root
            .insert(root_b, HashSet::from([shared_uri.clone()]));

        let (_, stale_uris, _, log_error) = collect_diagnostics_for_root(&mut state, root_a);

        assert_eq!(log_error, None);
        assert_eq!(stale_uris, vec![stale_uri]);
        assert!(!stale_uris.contains(&shared_uri));
    }

    #[test]
    fn lsp_diagnostics_include_related_information() {
        let mut workspace = CompilerWorkspace::with_root_dir(PathBuf::from("/tmp"));
        let path = "/tmp/related.ab";
        let file_id = workspace.set_file_source(path, "entity Account { }");
        let diagnostic = Diagnostic::error("duplicate name")
            .in_file(path)
            .with_span((0..6).into())
            .with_related(
                "previous definition",
                Some((7..14).into()),
                Some(path.to_owned()),
            );

        let (_, lsp_diagnostic) =
            diagnostic_to_lsp(&workspace, file_id, &diagnostic).expect("lsp diagnostic");
        let related = lsp_diagnostic
            .related_information
            .expect("related information");

        assert_eq!(related.len(), 1);
        assert_eq!(related[0].message, "previous definition");
        assert_eq!(related[0].location.uri, Url::from_file_path(path).unwrap());
        assert_eq!(related[0].location.range.start, Position::new(0, 7));
        assert_eq!(related[0].location.range.end, Position::new(0, 14));
    }

    #[test]
    fn lsp_diagnostics_without_spans_use_zero_width_start_range() {
        let mut workspace = CompilerWorkspace::with_root_dir(PathBuf::from("/tmp"));
        let path = "/tmp/no_span.ab";
        let file_id = workspace.set_file_source(path, "system S { }");
        let diagnostic = Diagnostic::warning("workspace note").in_file(path);

        let (_, lsp_diagnostic) =
            diagnostic_to_lsp(&workspace, file_id, &diagnostic).expect("lsp diagnostic");

        assert_eq!(
            lsp_diagnostic.range,
            Range::new(Position::new(0, 0), Position::new(0, 0))
        );
    }

    #[test]
    fn definition_locations_map_symbols_to_file_uris_and_ranges() {
        let mut workspace = CompilerWorkspace::with_root_dir(PathBuf::from("/tmp"));
        let path = "/tmp/definitions.ab";
        let file_id = workspace.set_file_source(path, "entity Account { }\n");
        let index = build_workspace_index(&mut workspace).expect("workspace index");

        let locations = definition_locations(&workspace, &index, "Account");

        assert_eq!(locations.len(), 1);
        assert_eq!(locations[0].uri, Url::from_file_path(path).unwrap());
        assert_eq!(locations[0].range.start, Position::new(0, 7));
        assert_eq!(locations[0].range.end, Position::new(0, 14));

        let location =
            location_for_span(&workspace, file_id, (7..14).into()).expect("span location");
        assert_eq!(location, locations[0]);
        let (uri, range) =
            uri_and_range_for_span(&workspace, file_id, (7..14).into()).expect("uri and range");
        assert_eq!(uri, locations[0].uri);
        assert_eq!(range, locations[0].range);
    }

    #[test]
    fn navigation_rename_and_references_resolve_imported_symbols_semantically() {
        let mut state = LspState::new(PathBuf::from("."));
        let inventory_path = "/tmp/inventory_nav.ab";
        let billing_path = "/tmp/billing_nav.ab";
        let storefront_path = "/tmp/storefront_nav.ab";
        state.snapshot.set_file_source(
            inventory_path,
            "module Inventory\n\
             entity StockItem { sku: int }\n",
        );
        state.snapshot.set_file_source(
            billing_path,
            "module Billing\n\
             entity StockItem { invoice_id: int }\n",
        );
        let storefront_source = "module Storefront\n\
             use Inventory::StockItem\n\
             entity Cart { item: StockItem }\n";
        let storefront_id = state
            .snapshot
            .set_file_source(storefront_path, storefront_source);
        let source = state
            .snapshot
            .source_text(storefront_id)
            .expect("storefront source");
        let type_use_offset = source.rfind("StockItem").expect("type use");
        let occurrence = state
            .snapshot
            .identifier_at(storefront_id, type_use_offset)
            .expect("identifier lookup")
            .expect("identifier occurrence");
        let index = state.snapshot.workspace_index().expect("workspace index");

        let symbol = resolve_occurrence_symbol(&state.snapshot, &index, &occurrence)
            .expect("resolved symbol");
        assert_eq!(
            state
                .snapshot
                .workspace
                .path(symbol.file_id)
                .and_then(Path::to_str),
            Some(inventory_path),
            "type use should resolve to the imported Inventory declaration"
        );

        let billing_uri = Url::from_file_path(billing_path).expect("billing uri");
        let storefront_uri = Url::from_file_path(storefront_path).expect("storefront uri");
        let inventory_uri = Url::from_file_path(inventory_path).expect("inventory uri");

        let references = reference_locations_for_symbol(&state.snapshot, &index, &symbol, true);
        assert_eq!(
            references
                .iter()
                .filter(|location| location.uri == inventory_uri)
                .count(),
            1
        );
        assert_eq!(
            references
                .iter()
                .filter(|location| location.uri == storefront_uri)
                .count(),
            2
        );
        assert!(
            references
                .iter()
                .all(|location| location.uri != billing_uri),
            "semantic references should not include same-named Billing symbols: {references:#?}"
        );

        let references_without_declaration =
            reference_locations_for_symbol(&state.snapshot, &index, &symbol, false);
        assert_eq!(references_without_declaration.len(), 2);
        assert!(references_without_declaration
            .iter()
            .all(|location| location.uri == storefront_uri));

        let changes = rename_changes_for_symbol(&state.snapshot, &index, &symbol, "InventoryItem");
        assert_eq!(
            changes.get(&inventory_uri).map(Vec::len),
            Some(1),
            "rename should include the declaration"
        );
        assert_eq!(
            changes.get(&storefront_uri).map(Vec::len),
            Some(2),
            "rename should include the import and type use"
        );
        assert!(
            !changes.contains_key(&billing_uri),
            "rename should not edit unrelated same-name symbols"
        );
    }

    #[test]
    fn completion_items_preserve_symbol_kind_and_detail() {
        let mut workspace = CompilerWorkspace::with_root_dir(PathBuf::from("/tmp"));
        let file_id = workspace.set_file_source("/tmp/completions.ab", "fn total(): int { 0 }");
        let symbol = IdeSymbol {
            name: "total".to_owned(),
            kind: IdeSymbolKind::Function,
            file_id,
            span: (3..8).into(),
            detail: "fn total(): int".to_owned(),
            module: None,
            owner: None,
            visibility: abide::ide::IdeVisibility::Public,
        };

        let item = completion_item_for_symbol(&symbol);

        assert_eq!(item.label, "total");
        assert_eq!(item.kind, Some(CompletionItemKind::FUNCTION));
        assert_eq!(item.detail, Some("fn total(): int".to_owned()));
    }

    #[test]
    fn server_capabilities_advertise_document_features_and_qa_command() {
        let capabilities = server_capabilities();

        let sync = capabilities
            .text_document_sync
            .expect("text document sync capability");
        let TextDocumentSyncCapability::Options(sync) = sync else {
            panic!("expected sync options");
        };
        assert_eq!(sync.open_close, Some(true));
        assert_eq!(sync.change, Some(TextDocumentSyncKind::FULL));
        assert_eq!(
            sync.save,
            Some(TextDocumentSyncSaveOptions::Supported(true))
        );
        assert!(matches!(
            capabilities.hover_provider,
            Some(HoverProviderCapability::Simple(true))
        ));
        assert_eq!(capabilities.definition_provider, Some(OneOf::Left(true)));
        assert_eq!(capabilities.references_provider, Some(OneOf::Left(true)));
        assert_eq!(capabilities.rename_provider, Some(OneOf::Left(true)));
        assert!(matches!(
            capabilities.code_action_provider,
            Some(CodeActionProviderCapability::Options(_))
        ));

        let completion = capabilities
            .completion_provider
            .expect("completion capability");
        assert_eq!(completion.resolve_provider, Some(false));
        assert_eq!(
            completion.trigger_characters,
            Some(vec![".".to_owned(), "@".to_owned(), ":".to_owned()])
        );

        let commands = capabilities
            .execute_command_provider
            .expect("execute command capability")
            .commands;
        assert_eq!(commands, vec![QA_RUN_SCRIPT_COMMAND.to_owned()]);
    }

    #[test]
    fn lsp_code_actions_create_missing_qa_load_target() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/missing_load_action.qa").expect("uri");
        let source = "load \"missing.ab\"\nask entities\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/missing_load_action.qa", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );
        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);
        assert!(log_error.is_none(), "{log_error:?}");
        let diagnostic = diagnostics
            .get(&uri)
            .and_then(|diagnostics| diagnostics.first())
            .cloned()
            .expect("missing load diagnostic");

        let actions = code_actions_for_document(&state, &uri, &[diagnostic])
            .expect("missing load code actions");

        let action = only_code_action(&actions, "Create missing load target `missing.ab`");
        assert_eq!(action.kind, Some(CodeActionKind::QUICKFIX));
        let edit = action.edit.as_ref().expect("workspace edit");
        let document_changes = edit.document_changes.as_ref().expect("document changes");
        let DocumentChanges::Operations(operations) = document_changes else {
            panic!("expected create-file operation, got {document_changes:#?}");
        };
        assert!(operations.iter().any(|operation| {
            matches!(
                operation,
                DocumentChangeOperation::Op(ResourceOp::Create(CreateFile { uri, .. }))
                    if uri == &Url::parse("file:///tmp/missing.ab").expect("target uri")
            )
        }));
    }

    #[test]
    fn lsp_code_actions_close_unclosed_qa_abide_blocks() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/unclosed_block_action.qa").expect("uri");
        let source = "ask entities\nabide {\n  entity Ticket {\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/unclosed_block_action.qa", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );
        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);
        assert!(log_error.is_none(), "{log_error:?}");
        let diagnostic = diagnostics
            .get(&uri)
            .and_then(|diagnostics| diagnostics.first())
            .cloned()
            .expect("unclosed block diagnostic");

        let actions = code_actions_for_document(&state, &uri, &[diagnostic])
            .expect("unclosed block code actions");

        let action = only_code_action(&actions, "Close QA abide block");
        let edit = action.edit.as_ref().expect("workspace edit");
        let changes = edit.changes.as_ref().expect("text changes");
        let edits = changes.get(&uri).expect("uri edits");
        assert_eq!(edits.len(), 1);
        assert_eq!(
            edits[0].range,
            Range::new(Position::new(3, 0), Position::new(3, 0))
        );
        assert_eq!(edits[0].new_text, "}\n");
    }

    #[test]
    fn lsp_code_actions_remove_removed_field_keyword_in_abide_sources() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/field_keyword_action.ab").expect("uri");
        let source = "entity Ticket { field status: int }\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/field_keyword_action.ab", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );
        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);
        assert!(log_error.is_none(), "{log_error:?}");
        let diagnostic = diagnostics
            .get(&uri)
            .and_then(|diagnostics| diagnostics.first())
            .cloned()
            .expect("field keyword diagnostic");

        let actions = code_actions_for_document(&state, &uri, &[diagnostic])
            .expect("field keyword code actions");

        let action = only_code_action(&actions, "Remove removed `field` keyword");
        let edit = action.edit.as_ref().expect("workspace edit");
        let changes = edit.changes.as_ref().expect("text changes");
        let edits = changes.get(&uri).expect("uri edits");
        assert_eq!(edits.len(), 1);
        assert_eq!(
            edits[0].range,
            Range::new(Position::new(0, 16), Position::new(0, 22))
        );
        assert!(edits[0].new_text.is_empty());
    }

    #[test]
    fn editor_verification_config_uses_policy_timeout_for_lsp_checks() {
        let policy = EditorVerificationPolicy {
            trigger: EditorVerificationTrigger::OnChange,
            debounce_ms: 123,
            timeout_ms: 4567,
        };

        let config = verify_config_for_editor_policy(policy);

        assert_eq!(config.overall_timeout_ms, 4567);
        assert_eq!(config.induction_timeout_ms, 4567);
    }

    #[test]
    fn editor_verification_policy_parses_initialization_options() {
        let options = serde_json::json!({
            "abide": {
                "verification": {
                    "mode": "save",
                    "debounceMs": 750,
                    "timeoutMs": 1250
                }
            }
        });

        let policy = EditorVerificationPolicy::from_initialization_options(Some(&options));

        assert_eq!(policy.trigger, EditorVerificationTrigger::OnSave);
        assert_eq!(policy.debounce_ms, 750);
        assert_eq!(policy.timeout_ms, 1250);
        assert!(!policy.should_schedule_on_change());
        assert!(policy.should_schedule_on_save());
        assert!(policy.should_run_automatically());
    }

    #[test]
    fn editor_verification_policy_supports_disabled_and_manual_modes() {
        let disabled = EditorVerificationPolicy::from_initialization_options(Some(
            &serde_json::json!({ "abide": { "verification": { "mode": "disabled" } } }),
        ));
        assert_eq!(disabled.trigger, EditorVerificationTrigger::Disabled);
        assert!(!disabled.should_schedule_on_change());
        assert!(!disabled.should_schedule_on_save());

        let disabled_by_flag = EditorVerificationPolicy::from_initialization_options(Some(
            &serde_json::json!({ "verification": { "enabled": false } }),
        ));
        assert_eq!(
            disabled_by_flag.trigger,
            EditorVerificationTrigger::Disabled
        );
        assert!(!disabled_by_flag.should_run_automatically());

        let manual = EditorVerificationPolicy::from_initialization_options(Some(
            &serde_json::json!({ "abide": { "verification": { "mode": "manual" } } }),
        ));
        assert_eq!(manual.trigger, EditorVerificationTrigger::Manual);
        assert!(!manual.should_schedule_on_change());
        assert!(!manual.should_schedule_on_save());
        assert!(!manual.should_run_automatically());
    }

    #[test]
    fn keyword_completions_include_contract_keywords() {
        let items = keyword_completions(
            CompletionContext::General,
            KeywordCompletionContext::General,
        );
        let labels = items
            .iter()
            .map(|item| item.label.clone())
            .collect::<Vec<_>>();

        assert!(labels.contains(&"requires".to_owned()));
        assert!(labels.contains(&"ensures".to_owned()));
        assert!(labels.contains(&"decreases".to_owned()));
        assert!(items
            .iter()
            .all(|item| item.kind == Some(CompletionItemKind::KEYWORD)));
    }

    #[test]
    fn keyword_context_uses_real_word_boundaries() {
        assert_eq!(
            keyword_completion_context("fn bounded", "fn bounded".len()),
            KeywordCompletionContext::Contract
        );
        assert_eq!(
            keyword_completion_context("fn_helper", "fn_helper".len()),
            KeywordCompletionContext::General
        );
        assert_eq!(
            keyword_completion_context("fn2", "fn2".len()),
            KeywordCompletionContext::General
        );
    }

    #[test]
    fn keyword_completions_rank_requires_first_in_contract_context() {
        let source = "fn bounded(x: int): int\n  req";
        let context = keyword_completion_context(source, source.len());
        let items = keyword_completions(CompletionContext::General, context);
        let requires = items
            .iter()
            .find(|item| item.label == "requires")
            .expect("requires completion");
        let module = items
            .iter()
            .find(|item| item.label == "module")
            .expect("module completion");

        assert_eq!(context, KeywordCompletionContext::Contract);
        assert!(requires.sort_text < module.sort_text);
        assert_eq!(
            keyword_sort_text("requires", KeywordCompletionContext::Contract),
            "00_requires"
        );
        assert_eq!(
            keyword_sort_text("ensures", KeywordCompletionContext::Contract),
            "01_ensures"
        );
        assert_eq!(
            keyword_sort_text("decreases", KeywordCompletionContext::Contract),
            "02_decreases"
        );
    }

    #[test]
    fn keyword_completions_keep_contract_keywords_lower_in_general_context() {
        let source = "req";
        let context = keyword_completion_context(source, source.len());
        let items = keyword_completions(CompletionContext::General, context);
        let requires = items
            .iter()
            .find(|item| item.label == "requires")
            .expect("requires completion");
        let module = items
            .iter()
            .find(|item| item.label == "module")
            .expect("module completion");

        assert_eq!(context, KeywordCompletionContext::General);
        assert!(requires.sort_text > module.sort_text);
        assert_eq!(
            keyword_sort_text("requires", KeywordCompletionContext::General),
            "40_requires"
        );
    }

    #[test]
    fn keyword_completion_context_does_not_promote_inside_body() {
        let source = "fn bounded(x: int): int {\n  req";

        assert_eq!(
            keyword_completion_context(source, source.len()),
            KeywordCompletionContext::General
        );
    }

    #[test]
    fn lsp_completion_uses_qa_commands_for_qa_documents() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/commands.qa").expect("uri");
        let file_id = state
            .snapshot
            .set_file_source("/tmp/commands.qa", "ver".to_owned());
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(0, 3))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"verify".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"module".to_owned()),
            "QA completions should not include Abide keywords: {labels:#?}"
        );
    }

    #[test]
    fn lsp_completion_uses_qa_query_subcommands_for_qa_documents() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/query.qa").expect("uri");
        let file_id = state
            .snapshot
            .set_file_source("/tmp/query.qa", "ask fs".to_owned());
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(0, 6))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"fsms".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"fn".to_owned()),
            "QA subcommand completions should not include Abide keywords: {labels:#?}"
        );
        assert_eq!(
            qa_completion_context("load fs", "load fs".len()),
            QACompletionContext::LoadPath
        );
        assert_eq!(
            qa_completion_context("ask fs extra", "ask fs extra".len()),
            QACompletionContext::None
        );
    }

    #[test]
    fn qa_completion_items_are_keyword_items() {
        let items = qa_completion_items("ver", 3);
        let verify = items
            .iter()
            .find(|item| item.label == "verify")
            .expect("verify completion");

        assert_eq!(verify.kind, Some(CompletionItemKind::KEYWORD));
    }

    #[test]
    fn lsp_qa_completion_suggests_project_load_paths() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        std::fs::write(root.join("model.ab"), "module Model\nentity Ticket { }\n")
            .expect("write model");
        std::fs::write(root.join("other.qa"), "ask entities\n").expect("write qa");

        let mut state = LspState::new(root);
        let qa_path = root.join("query.qa");
        let uri = Url::from_file_path(&qa_path).expect("file uri");
        let source = "load \"mo";
        let file_id = state.snapshot.set_file_source(&qa_path, source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(0, 8))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"model.ab".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"other.qa".to_owned()),
            "QA load path completions should suggest loadable Abide sources only: {labels:#?}"
        );
    }

    #[test]
    fn lsp_qa_completion_suggests_loaded_model_references() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        std::fs::write(
            root.join("model.ab"),
            "module Commerce\n\
             enum TicketStatus = Open | Closed\n\
             entity Ticket { status: TicketStatus = @Open total: int }\n\
             system Support { }\n",
        )
        .expect("write model");

        let mut state = LspState::new(root);
        let qa_path = root.join("query.qa");
        let uri = Url::from_file_path(&qa_path).expect("file uri");
        let source = "load \"model.ab\"\nask terminal \nask deadlock ";
        let file_id = state.snapshot.set_file_source(&qa_path, source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let field_items =
            completion_items_for_open_document(&mut state, &uri, Position::new(1, 13))
                .expect("field completion items");
        let field_labels = field_items
            .into_iter()
            .map(|item| item.label)
            .collect::<Vec<_>>();
        assert!(
            field_labels.contains(&"Ticket.status".to_owned()),
            "{field_labels:#?}"
        );
        assert!(
            !field_labels.contains(&"Ticket.total".to_owned()),
            "graphable target completions should suppress non-graphable fields: {field_labels:#?}"
        );

        let system_items =
            completion_items_for_open_document(&mut state, &uri, Position::new(2, 13))
                .expect("system completion items");
        let system_labels = system_items
            .into_iter()
            .map(|item| item.label)
            .collect::<Vec<_>>();
        assert!(
            system_labels.contains(&"Support".to_owned()),
            "{system_labels:#?}"
        );
    }

    #[test]
    fn lsp_qa_embedded_abide_completion_uses_loaded_context_without_project_leaks() {
        let dir = tempfile::tempdir().expect("temp project");
        let root = dir.path();
        std::fs::write(
            root.join("loaded.ab"),
            "module Loaded\n\
             enum LoadedStatus = Ready | Done\n",
        )
        .expect("write loaded");
        std::fs::write(
            root.join("unloaded.ab"),
            "module Unloaded\n\
             enum UnloadedStatus = Hidden\n",
        )
        .expect("write unloaded");

        let mut state = LspState::new(root);
        let qa_path = root.join("query.qa");
        let uri = Url::from_file_path(&qa_path).expect("file uri");
        let source = "load \"loaded.ab\"\nabide {\n  entity Local { status: \n}\n";
        let file_id = state.snapshot.set_file_source(&qa_path, source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(2, 25))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"LoadedStatus".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"UnloadedStatus".to_owned()),
            "embedded QA Abide completions should be scoped to loaded specs: {labels:#?}"
        );
    }

    #[test]
    fn lsp_completion_uses_abide_keywords_inside_embedded_qa_blocks() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/embedded_completion.qa").expect("uri");
        let source = "ask entities\nabide {\n  ent\n}\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/embedded_completion.qa", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(2, 5))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(
            labels.contains(&"entity".to_owned()),
            "embedded Abide completions should include Abide keywords: {labels:#?}"
        );
        assert!(
            !labels.contains(&"ask".to_owned()),
            "embedded Abide completions should not include QA commands: {labels:#?}"
        );
    }

    #[test]
    fn embedded_abide_block_lookup_respects_body_boundaries() {
        let source = "ask entities\nabide {\n  entity Account { }\n}\nask systems\n";
        let inside_offset = source.find("entity").expect("entity offset");
        let block = embedded_abide_block_at(source, inside_offset).expect("embedded block");

        assert!(inside_offset >= block.body_span.start);
        assert!(inside_offset <= block.body_span.end);
        assert!(embedded_abide_block_at(source, block.body_span.start - 1).is_none());
        assert!(embedded_abide_block_at(source, block.body_span.end + 1).is_none());
    }

    #[test]
    fn lsp_completion_offers_interface_names_from_workspace_index() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/interface_completion.ab").expect("uri");
        let source = "module InterfaceCompletion\n\n\
             interface PaymentProcessor {\n\
               command authorize(amount: int) -> string\n\
             }\n\n\
             system LocalGateway implements PaymentProcessor {\n\
             }\n\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/interface_completion.ab", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let completion_line = 8;
        let completion_column = u32::try_from(
            source
                .lines()
                .nth(completion_line)
                .expect("completion line")
                .len(),
        )
        .expect("completion column fits in u32");
        let items = completion_items_for_open_document(
            &mut state,
            &uri,
            Position::new(
                u32::try_from(completion_line).expect("completion line fits in u32"),
                completion_column,
            ),
        )
        .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(
            labels.contains(&"PaymentProcessor".to_owned()),
            "interface completions should come from indexed declarations: {labels:#?}"
        );
    }

    #[test]
    fn lsp_completion_uses_visible_imports_for_general_abide_context() {
        let mut state = LspState::new(PathBuf::from("."));
        state.snapshot.set_file_source(
            "/tmp/inventory.ab",
            "module Inventory\n\
             enum StockStatus = InStock | Backorder\n\
             entity StockItem { sku: int }\n",
        );
        let uri = Url::parse("file:///tmp/storefront.ab").expect("uri");
        let source = "module Storefront\n\
             use Inventory::StockItem\n\
             entity Cart { item: StockItem }\n\
             ";
        let file_id = state.snapshot.set_file_source("/tmp/storefront.ab", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(3, 13))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(
            labels.contains(&"StockItem".to_owned()),
            "explicit import should be visible: {labels:#?}"
        );
        assert!(
            !labels.contains(&"StockStatus".to_owned()),
            "unimported module symbols should not appear in general completions: {labels:#?}"
        );
        assert!(
            labels.contains(&"Cart".to_owned()),
            "local declarations should remain visible: {labels:#?}"
        );
    }

    #[test]
    fn lsp_completion_filters_members_after_dot() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/member_completion.ab").expect("uri");
        let source = "module MemberCompletion\n\
             entity Order { status: int action submit() { true } }\n\
             entity Customer { name: int }\n\
             verify member_probe {\n\
               assert Order.\n\
             }\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/member_completion.ab", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(4, 27))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"status".to_owned()), "{labels:#?}");
        assert!(labels.contains(&"submit".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"name".to_owned()),
            "member completions should use the owner before dot: {labels:#?}"
        );
    }

    #[test]
    fn lsp_completion_filters_variants_after_at() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/variant_completion.ab").expect("uri");
        let source = "module VariantCompletion\n\
             enum OrderStatus = Pending | Paid\n\
             entity Order { status: OrderStatus }\n\
             verify variant_probe {\n\
               assert @\n\
             }\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/variant_completion.ab", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(4, 22))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"Pending".to_owned()), "{labels:#?}");
        assert!(labels.contains(&"Paid".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"Order".to_owned()),
            "variant completions should suppress non-variant symbols: {labels:#?}"
        );
    }

    #[test]
    fn lsp_completion_filters_exports_after_scope_resolution() {
        let mut state = LspState::new(PathBuf::from("."));
        state.snapshot.set_file_source(
            "/tmp/inventory_scope.ab",
            "module Inventory\n\
             enum StockStatus = InStock | Backorder\n\
             entity StockItem { sku: int }\n",
        );
        let uri = Url::parse("file:///tmp/scope_completion.ab").expect("uri");
        let source = "module Storefront\n\
             verify scope_probe {\n\
               assert Inventory::\n\
             }\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/scope_completion.ab", source);
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let items = completion_items_for_open_document(&mut state, &uri, Position::new(2, 32))
            .expect("completion items");
        let labels = items.into_iter().map(|item| item.label).collect::<Vec<_>>();

        assert!(labels.contains(&"StockStatus".to_owned()), "{labels:#?}");
        assert!(labels.contains(&"StockItem".to_owned()), "{labels:#?}");
        assert!(
            !labels.contains(&"Storefront".to_owned()),
            "scope completions should not fall back to global workspace symbols: {labels:#?}"
        );
    }

    #[test]
    fn lsp_qa_run_command_uses_open_document_source() {
        let root = std::env::temp_dir().join(format!("abide-lsp-qa-run-{}", std::process::id()));
        std::fs::create_dir_all(&root).expect("create temp root");
        std::fs::write(
            root.join("model.ab"),
            "module QALspRun\n\
             enum TicketStatus = Open | Closed\n\
             entity Ticket {\n\
               status: TicketStatus = @Open\n\
             }\n",
        )
        .expect("write model");

        let qa_path = root.join("query.qa");
        let uri = Url::from_file_path(&qa_path).expect("file uri");
        let source = "load \"model.ab\"\nassert terminal Ticket.status\n";
        let mut state = LspState::new(root);
        let file_id = state.snapshot.set_file_source(&qa_path, source.to_owned());
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 1,
            },
        );

        let result = run_qa_script_for_uri(&state, &uri).expect("run QA command");

        assert_eq!(result["passed"], 1);
        assert_eq!(result["failed"], 0);
        assert_eq!(result["executed"], 1);
    }

    #[test]
    fn lsp_diagnostics_include_function_contract_failures() {
        let mut state = LspState::new(PathBuf::from("."));
        let file_id = state.snapshot.set_file_source(
            "/tmp/fn_lsp.ab",
            "module FnLsp\n\n\
             fn bad_ensures(x: int): int\n  ensures result > x\n{\n  x\n}\n\n\
             fn positive(x: int): int\n  requires x > 0\n{\n  x\n}\n\n\
             fn caller_bad(x: int): int\n  ensures result == positive(x)\n{\n  positive(x)\n}\n",
        );

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let mut codes = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .filter_map(|diagnostic| diagnostic.code.as_ref())
            .filter_map(|code| match code {
                NumberOrString::String(code) => Some(code.clone()),
                NumberOrString::Number(_) => None,
            })
            .collect::<Vec<_>>();
        codes.sort();

        assert!(
            codes.contains(&"abide::verify::fn_ensures_failed".to_owned()),
            "expected failing ensures diagnostic: {codes:#?}"
        );
        assert!(
            codes.contains(&"abide::verify::fn_precondition_failed".to_owned()),
            "expected call-site requires diagnostic: {codes:#?}"
        );
    }

    #[test]
    fn lsp_diagnostics_do_not_lower_valid_qa_as_abide_source() {
        let mut state = LspState::new(PathBuf::from("."));
        let file_id = state
            .snapshot
            .set_file_source("/tmp/valid.qa", "ask entities\n");

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        assert!(
            diagnostics.values().all(Vec::is_empty),
            "valid QA should not produce Abide source diagnostics: {diagnostics:#?}"
        );
    }

    #[test]
    fn lsp_diagnostics_publish_qa_parse_errors_for_qa_documents() {
        let mut state = LspState::new(PathBuf::from("."));
        let file_id = state
            .snapshot
            .set_file_source("/tmp/bad.qa", "query entities\n");

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let all = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .collect::<Vec<_>>();
        assert_eq!(all.len(), 1, "expected one QA parse diagnostic: {all:#?}");

        let diagnostic = all[0];
        assert_eq!(
            diagnostic.code,
            Some(NumberOrString::String(
                "abide::qa::parse::expected".to_owned()
            ))
        );
        assert_eq!(diagnostic.range.start, Position::new(0, 0));
        assert_eq!(diagnostic.range.end, Position::new(0, 5));
        assert!(
            diagnostic.message.contains("expected 'ask'"),
            "unexpected diagnostic message: {}",
            diagnostic.message
        );
    }

    #[test]
    fn lsp_diagnostics_publish_missing_qa_load_targets() {
        let mut state = LspState::new(PathBuf::from("."));
        let file_id = state.snapshot.set_file_source(
            "/tmp/missing_load.qa",
            "load \"missing.ab\"\nask entities\n",
        );

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let all = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .collect::<Vec<_>>();
        assert_eq!(
            all.len(),
            1,
            "expected one missing load diagnostic: {all:#?}"
        );

        let diagnostic = all[0];
        assert_eq!(
            diagnostic.code,
            Some(NumberOrString::String(
                "abide::qa::semantic::missing_load".to_owned()
            ))
        );
        assert_eq!(diagnostic.range.start, Position::new(0, 6));
        assert_eq!(diagnostic.range.end, Position::new(0, 16));
    }

    #[test]
    fn lsp_diagnostics_map_embedded_qa_abide_blocks_to_qa_source() {
        let mut state = LspState::new(PathBuf::from("."));
        let source = "ask entities\nabide {\n  entity Broken {\n    status: MissingType\n  }\n}\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/embedded_diagnostic.qa", source);

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let all = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .collect::<Vec<_>>();
        assert!(
            !all.is_empty(),
            "expected embedded Abide diagnostic mapped into QA source"
        );
        assert!(
            all.iter()
                .any(|diagnostic| diagnostic.range.start == Position::new(1, 7)),
            "expected spanless embedded diagnostic to anchor inside the Abide block: {all:#?}"
        );
    }

    #[test]
    fn lsp_diagnostics_map_embedded_qa_abide_parse_spans_to_qa_source() {
        let mut state = LspState::new(PathBuf::from("."));
        let source = "ask entities\nabide {\n  entity Broken {\n    status:\n  }\n}\n";
        let file_id = state
            .snapshot
            .set_file_source("/tmp/embedded_parse_diagnostic.qa", source);

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let all = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .collect::<Vec<_>>();
        assert!(
            all.iter().any(|diagnostic| {
                diagnostic.code == Some(NumberOrString::String("abide::parse::expected".to_owned()))
                    && diagnostic.range.start == Position::new(4, 2)
            }),
            "expected embedded Abide parse diagnostic mapped into QA source: {all:#?}"
        );
    }

    #[test]
    fn lsp_diagnostics_publish_unknown_qa_query_references() {
        let root =
            std::env::temp_dir().join(format!("abide-lsp-qa-validation-{}", std::process::id()));
        std::fs::create_dir_all(&root).expect("create temp root");
        let spec_path = root.join("model.ab");
        std::fs::write(
            &spec_path,
            "module QALsp\n\
             enum TicketStatus = Open | Closed\n\
             entity Ticket {\n\
               status: TicketStatus = @Open\n\
             }\n",
        )
        .expect("write spec");

        let qa_path = root.join("query.qa");
        let source = "load \"model.ab\"\nask terminal Missing.status\n";
        let mut state = LspState::new(root);
        let file_id = state.snapshot.set_file_source(&qa_path, source.to_owned());

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let all = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .collect::<Vec<_>>();
        assert_eq!(
            all.len(),
            1,
            "expected one unknown query reference diagnostic: {all:#?}"
        );

        let diagnostic = all[0];
        assert_eq!(
            diagnostic.code,
            Some(NumberOrString::String(
                "abide::qa::semantic::unknown_reference".to_owned()
            ))
        );
        assert_eq!(diagnostic.range.start, Position::new(1, 13));
        assert_eq!(diagnostic.range.end, Position::new(1, 27));
    }

    #[test]
    fn lsp_diagnostics_treat_hypothetical_fixture_as_qa_source() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let qa_path = root
            .join("..")
            .join("abide")
            .join("tests")
            .join("fixtures")
            .join("test_hypothetical.qa");
        let source = std::fs::read_to_string(&qa_path).expect("fixture source");
        let mut state = LspState::new(root);
        let file_id = state.snapshot.set_file_source(&qa_path, source);

        let (diagnostics, _stale, _versions, log_error) =
            collect_diagnostics_for_root(&mut state, file_id);

        assert!(log_error.is_none(), "{log_error:?}");
        let all = diagnostics
            .values()
            .flat_map(|diagnostics| diagnostics.iter())
            .collect::<Vec<_>>();
        assert!(
            all.iter().all(|diagnostic| !diagnostic
                .message
                .contains("expected top-level declaration")),
            "QA fixture should not be parsed as Abide source: {all:#?}"
        );
        assert!(
            all.iter().all(|diagnostic| {
                !(diagnostic.message.contains("unresolved name")
                    && diagnostic.message.contains("Closed"))
            }),
            "embedded block should see the loaded base spec context: {all:#?}"
        );
    }
}
