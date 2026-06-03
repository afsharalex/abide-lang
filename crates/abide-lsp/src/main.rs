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

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use abide::diagnostic::{Diagnostic, DiagnosticSeverity};
use abide::ide::{
    build_workspace_index, completion_context, identifier_at, CompletionContext, IdeSymbol,
    IdeSymbolKind,
};
use abide::workspace::{CompilerWorkspace, FileId};
use tokio::sync::Mutex;
use tower_lsp::jsonrpc::Result;
#[allow(clippy::wildcard_imports)]
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

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
        matches!(
            self.trigger,
            EditorVerificationTrigger::OnChange | EditorVerificationTrigger::OnSave
        )
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum EditorVerificationStatus {
    Verifying,
    Verified,
    Failed,
    Admitted,
    Disabled,
    TimedOut,
    Cancelled,
    Stale,
}

impl EditorVerificationStatus {
    fn code(self) -> &'static str {
        match self {
            Self::Verifying => "abide.lsp.verification.verifying",
            Self::Verified => "abide.lsp.verification.verified",
            Self::Failed => "abide.lsp.verification.failed",
            Self::Admitted => "abide.lsp.verification.admitted",
            Self::Disabled => "abide.lsp.verification.disabled",
            Self::TimedOut => "abide.lsp.verification.timeout",
            Self::Cancelled => "abide.lsp.verification.cancelled",
            Self::Stale => "abide.lsp.verification.stale",
        }
    }

    fn message(self) -> &'static str {
        match self {
            Self::Verifying => "Abide verification is running",
            Self::Verified => "Abide verification passed",
            Self::Failed => "Abide verification found failures",
            Self::Admitted => "Abide verification has admitted obligations",
            Self::Disabled => "Abide editor verification is disabled",
            Self::TimedOut => "Abide verification timed out",
            Self::Cancelled => "Abide verification was cancelled",
            Self::Stale => "Abide verification result is stale",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EditorVerificationRequest {
    root_file_id: FileId,
    root_uri: Url,
    version: i32,
    generation: u64,
}

/// Per-server-instance state shared behind a `tokio::Mutex`.
///
/// Holds the compiler workspace (source for every file the LSP has
/// touched), the set of buffers the editor currently has open, and a
/// publication ledger so we can clear stale diagnostics when files drop
/// out of the result set.
struct LspState {
    workspace: CompilerWorkspace,
    documents: HashMap<Url, OpenDocument>,
    /// For each root file we elaborate, the URIs we last published
    /// diagnostics to. Needed because a single elaboration may touch
    /// many files, and when a fix removes errors from one of them we
    /// must explicitly republish empty diagnostics for that URI.
    published_by_root: HashMap<FileId, HashSet<Url>>,
    verification_policy: EditorVerificationPolicy,
    verification_generations: HashMap<FileId, u64>,
}

impl LspState {
    fn new(root_dir: PathBuf) -> Self {
        Self::new_with_policy(root_dir, EditorVerificationPolicy::default())
    }

    fn new_with_policy(root_dir: PathBuf, verification_policy: EditorVerificationPolicy) -> Self {
        Self {
            workspace: CompilerWorkspace::with_root_dir(root_dir),
            documents: HashMap::new(),
            published_by_root: HashMap::new(),
            verification_policy,
            verification_generations: HashMap::new(),
        }
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

    fn begin_verification_request(
        &mut self,
        root_file_id: FileId,
    ) -> Option<EditorVerificationRequest> {
        let root_uri = Url::from_file_path(self.workspace.path(root_file_id)?).ok()?;
        let version = self.document_version(&root_uri)?;
        let generation = self
            .verification_generations
            .entry(root_file_id)
            .and_modify(|generation| *generation += 1)
            .or_insert(1);
        Some(EditorVerificationRequest {
            root_file_id,
            root_uri,
            version,
            generation: *generation,
        })
    }

    fn should_publish_verification_result(&self, request: &EditorVerificationRequest) -> bool {
        self.verification_policy.trigger != EditorVerificationTrigger::Disabled
            && self
                .verification_generations
                .get(&request.root_file_id)
                .is_some_and(|generation| *generation == request.generation)
            && self.documents.get(&request.root_uri).is_some_and(|doc| {
                doc.file_id == request.root_file_id && doc.version == request.version
            })
    }
}

/// LSP request handler. All async methods serialize through the
/// `state` mutex.
struct Backend {
    client: Client,
    state: Arc<Mutex<LspState>>,
}

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
            capabilities: ServerCapabilities {
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
                    trigger_characters: Some(vec![".".to_owned(), "@".to_owned()]),
                    ..CompletionOptions::default()
                }),
                ..ServerCapabilities::default()
            },
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
                    let _ = state.workspace.update_file_source(file_id, source);
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
        let state = self.state.lock().await;
        let Some(doc) = state.documents.get(&uri) else {
            return Ok(None);
        };
        let Some(source) = state.workspace.source_text(doc.file_id) else {
            return Ok(None);
        };
        let mut state = state;
        let Ok(index) = build_workspace_index(&mut state.workspace) else {
            return Ok(None);
        };
        let Some(offset) = position_to_offset(source.as_ref(), position) else {
            return Ok(None);
        };
        let context = completion_context(source.as_ref(), offset);
        let mut items = keyword_completions(context);
        items.extend(
            index
                .completion_symbols(context)
                .into_iter()
                .map(completion_item_for_symbol),
        );
        Ok(Some(CompletionResponse::Array(items)))
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
        let Some((name, _)) = self.identifier_name_at(&uri, position).await else {
            return Ok(None);
        };

        let mut state = self.state.lock().await;
        let Ok(index) = build_workspace_index(&mut state.workspace) else {
            return Ok(None);
        };
        let locations = definition_locations(&state.workspace, &index, &name);
        if locations.is_empty() {
            Ok(None)
        } else {
            Ok(Some(GotoDefinitionResponse::Array(locations)))
        }
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some((name, _)) = self.identifier_name_at(&uri, position).await else {
            return Ok(None);
        };

        let mut state = self.state.lock().await;
        let Ok(index) = build_workspace_index(&mut state.workspace) else {
            return Ok(None);
        };
        if index.symbols_named(&name).is_empty() {
            return Ok(None);
        }

        let mut locations = Vec::new();
        for occurrence in &index.occurrences {
            if occurrence.name == name {
                if let Some(location) =
                    location_for_span(&state.workspace, occurrence.file_id, occurrence.span)
                {
                    locations.push(location);
                }
            }
        }
        if !params.context.include_declaration {
            let definitions = definition_locations(&state.workspace, &index, &name);
            locations.retain(|loc| !definitions.contains(loc));
        }
        Ok(Some(locations))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some((name, _)) = self.identifier_name_at(&uri, position).await else {
            return Ok(None);
        };

        let mut state = self.state.lock().await;
        let Ok(index) = build_workspace_index(&mut state.workspace) else {
            return Ok(None);
        };
        if index.symbols_named(&name).is_empty() {
            return Ok(None);
        }

        let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
        for occurrence in &index.occurrences {
            if occurrence.name == name {
                if let Some((uri, range)) =
                    uri_and_range_for_span(&state.workspace, occurrence.file_id, occurrence.span)
                {
                    changes.entry(uri).or_default().push(TextEdit {
                        range,
                        new_text: params.new_name.clone(),
                    });
                }
            }
        }
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
        let path = uri.to_file_path().ok()?;
        let mut state = self.state.lock().await;
        if !state.should_accept_document_version(uri, version) {
            return None;
        }
        let existing_file_id = state.documents.get(uri).map(|doc| doc.file_id);
        let file_id = if let Some(file_id) = existing_file_id {
            let _ = state.workspace.update_file_source(file_id, text);
            file_id
        } else {
            state.workspace.set_file_source(path, text)
        };
        state
            .documents
            .insert(uri.clone(), OpenDocument { file_id, version });
        Some(file_id)
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

    async fn identifier_name_at(&self, uri: &Url, position: Position) -> Option<(String, FileId)> {
        let mut state = self.state.lock().await;
        let file_id = state.documents.get(uri)?.file_id;
        let source = state.workspace.source_text(file_id)?;
        let offset = position_to_offset(source.as_ref(), position)?;
        let occurrence = identifier_at(&mut state.workspace, file_id, offset).ok()??;
        Some((occurrence.name, file_id))
    }

    async fn symbol_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<(IdeSymbol, Range)> {
        let mut state = self.state.lock().await;
        let file_id = state.documents.get(uri)?.file_id;
        let source = state.workspace.source_text(file_id)?;
        let offset = position_to_offset(source.as_ref(), position)?;
        let occurrence = identifier_at(&mut state.workspace, file_id, offset).ok()??;
        let index = build_workspace_index(&mut state.workspace).ok()?;
        let mut matches = index.symbols_named(&occurrence.name);
        matches.sort_by_key(|symbol| {
            (
                usize::from(symbol.file_id != file_id),
                symbol.kind.sort_rank(),
            )
        });
        let symbol = matches.into_iter().next()?.clone();
        let range = range_from_span(
            state.workspace.source_text(symbol.file_id)?.as_ref(),
            symbol.span,
        )?;
        Some((symbol, range))
    }
}

fn collect_diagnostics_for_root(
    state: &mut LspState,
    root_file_id: FileId,
) -> (
    HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>,
    Vec<Url>,
    HashMap<Url, Option<i32>>,
    Option<String>,
) {
    let mut grouped: HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>> = HashMap::new();
    let mut current = HashSet::new();
    let mut log_error = None;

    match state.workspace.lower(root_file_id) {
        Ok(lowered) => {
            for diagnostic in &lowered.diagnostics {
                collect_lsp_diagnostic(state, root_file_id, diagnostic, &mut current, &mut grouped);
            }

            if state.verification_policy.should_run_automatically() {
                let mut config = abide::verify::VerifyConfig::default();
                config.overall_timeout_ms = state.verification_policy.timeout_ms;
                config.induction_timeout_ms = state.verification_policy.timeout_ms;
                let results =
                    abide::verify::verify_function_contracts_only(&lowered.ir_program, &config);
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
        }
        Err(error) => {
            log_error = Some(format!("failed to refresh diagnostics: {error:?}"));
        }
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

fn collect_lsp_diagnostic(
    state: &LspState,
    root_file_id: FileId,
    diagnostic: &Diagnostic,
    current: &mut HashSet<Url>,
    grouped: &mut HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>,
) {
    let Some((uri, lsp_diagnostic)) = diagnostic_to_lsp(&state.workspace, root_file_id, diagnostic)
    else {
        return;
    };
    current.insert(uri.clone());
    grouped.entry(uri).or_default().push(lsp_diagnostic);
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
        .unwrap_or_else(default_range);

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

fn keyword_completions(context: CompletionContext) -> Vec<CompletionItem> {
    let keywords: &[&str] = match context {
        CompletionContext::General => &[
            "module",
            "include",
            "use",
            "const",
            "fn",
            "type",
            "enum",
            "struct",
            "entity",
            "system",
            "program",
            "proc",
            "pred",
            "prop",
            "verify",
            "theorem",
            "lemma",
            "axiom",
            "scene",
            "match",
            "if",
            "let",
            "var",
            "while",
            "all",
            "exists",
            "always",
            "eventually",
            "historically",
            "once",
            "previously",
            "since",
            "until",
            "true",
            "false",
        ],
        CompletionContext::AfterAt | CompletionContext::AfterDot => &[],
    };
    keywords
        .iter()
        .map(|keyword| CompletionItem {
            label: (*keyword).to_owned(),
            kind: Some(CompletionItemKind::KEYWORD),
            ..CompletionItem::default()
        })
        .collect()
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
        Some(
            offset
                + usize::try_from(position.character)
                    .ok()?
                    .min(source[offset..].len()),
        )
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

fn default_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(0, 0))
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

    #[test]
    fn offset_position_roundtrip() {
        let source = "line1\nalpha beta\n";
        let offset = position_to_offset(source, Position::new(1, 3)).expect("offset");
        assert_eq!(
            offset_to_position(source, offset),
            Some(Position::new(1, 3))
        );
    }

    #[test]
    fn rejects_stale_document_versions() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/example.ab").expect("uri");
        let file_id = state
            .workspace
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
    }

    #[test]
    fn editor_verification_policy_supports_disabled_and_manual_modes() {
        let disabled = EditorVerificationPolicy::from_initialization_options(Some(
            &serde_json::json!({ "abide": { "verification": { "mode": "disabled" } } }),
        ));
        assert_eq!(disabled.trigger, EditorVerificationTrigger::Disabled);
        assert!(!disabled.should_schedule_on_change());
        assert!(!disabled.should_schedule_on_save());
        assert_eq!(
            EditorVerificationStatus::Disabled.code(),
            "abide.lsp.verification.disabled"
        );
        assert_eq!(
            EditorVerificationStatus::TimedOut.message(),
            "Abide verification timed out"
        );

        let disabled_by_flag = EditorVerificationPolicy::from_initialization_options(Some(
            &serde_json::json!({ "verification": { "enabled": false } }),
        ));
        assert_eq!(
            disabled_by_flag.trigger,
            EditorVerificationTrigger::Disabled
        );

        let manual = EditorVerificationPolicy::from_initialization_options(Some(
            &serde_json::json!({ "abide": { "verification": { "mode": "manual" } } }),
        ));
        assert_eq!(manual.trigger, EditorVerificationTrigger::Manual);
        assert!(!manual.should_schedule_on_change());
        assert!(!manual.should_schedule_on_save());
    }

    #[test]
    fn verification_request_version_guard_rejects_stale_results() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/example.ab").expect("uri");
        let file_id = state
            .workspace
            .set_file_source("/tmp/example.ab", "fn f(): int { 0 }");
        state.documents.insert(
            uri.clone(),
            OpenDocument {
                file_id,
                version: 3,
            },
        );

        let request = state
            .begin_verification_request(file_id)
            .expect("verification request");
        assert!(state.should_publish_verification_result(&request));

        state.documents.insert(
            uri,
            OpenDocument {
                file_id,
                version: 4,
            },
        );

        assert!(!state.should_publish_verification_result(&request));
    }

    #[test]
    fn lsp_diagnostics_include_function_contract_failures() {
        let mut state = LspState::new(PathBuf::from("."));
        let file_id = state.workspace.set_file_source(
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
}
