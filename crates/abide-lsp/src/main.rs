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
use abide::qa::complete::{qa_command_candidates, qa_query_subcommand_candidates};
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
    workspace: CompilerWorkspace,
    documents: HashMap<Url, OpenDocument>,
    /// For each root file we elaborate, the URIs we last published
    /// diagnostics to. Needed because a single elaboration may touch
    /// many files, and when a fix removes errors from one of them we
    /// must explicitly republish empty diagnostics for that URI.
    published_by_root: HashMap<FileId, HashSet<Url>>,
    verification_policy: EditorVerificationPolicy,
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
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec![QA_RUN_SCRIPT_COMMAND.to_owned()],
                    ..ExecuteCommandOptions::default()
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
        let mut state = self.state.lock().await;
        Ok(
            completion_items_for_open_document(&mut state, &uri, position)
                .map(CompletionResponse::Array),
        )
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

fn collect_diagnostics_for_root(state: &mut LspState, root_file_id: FileId) -> DiagnosticsForRoot {
    let mut grouped: LspDiagnosticMap = HashMap::new();
    let mut current = HashSet::new();
    let mut log_error = None;

    if state
        .workspace
        .path(root_file_id)
        .is_some_and(is_qa_document_path)
    {
        collect_qa_diagnostics_for_root(state, root_file_id, &mut current, &mut grouped);
    } else {
        match state.workspace.lower(root_file_id) {
            Ok(lowered) => {
                for diagnostic in &lowered.diagnostics {
                    collect_lsp_diagnostic(
                        state,
                        root_file_id,
                        diagnostic,
                        &mut current,
                        &mut grouped,
                    );
                }

                if state.verification_policy.should_run_automatically() {
                    let config = abide::verify::VerifyConfig {
                        overall_timeout_ms: state.verification_policy.timeout_ms,
                        induction_timeout_ms: state.verification_policy.timeout_ms,
                        ..abide::verify::VerifyConfig::default()
                    };
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
    state: &LspState,
    root_file_id: FileId,
    current: &mut HashSet<Url>,
    grouped: &mut HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>,
) {
    let Some(source) = state.workspace.source_text(root_file_id) else {
        return;
    };
    let Some(path) = state.workspace.path(root_file_id) else {
        return;
    };

    for diagnostic in abide::qa::validate::validate_qa_source(path, source.as_ref()) {
        collect_lsp_diagnostic(state, root_file_id, &diagnostic, current, grouped);
    }

    collect_embedded_abide_diagnostics_for_root(
        state,
        root_file_id,
        source.as_ref(),
        path,
        current,
        grouped,
    );
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
    let Some((uri, lsp_diagnostic)) = diagnostic_to_lsp(&state.workspace, root_file_id, diagnostic)
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
            .workspace
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

fn collect_embedded_abide_diagnostics_for_root(
    state: &LspState,
    root_file_id: FileId,
    source: &str,
    path: &Path,
    current: &mut HashSet<Url>,
    grouped: &mut HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>>,
) {
    for diagnostic in abide::qa::validate::validate_embedded_abide_blocks(path, source) {
        collect_lsp_diagnostic(state, root_file_id, &diagnostic, current, grouped);
    }
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
    let source = state.workspace.source_text(file_id)?;
    let offset = position_to_offset(source.as_ref(), position)?;
    let path = state.workspace.path(file_id)?;

    if is_qa_document_path(path) {
        if let Some(block) = embedded_abide_block_at(source.as_ref(), offset) {
            return Some(abide_completion_items_for_source(
                state,
                &block.body,
                offset.saturating_sub(block.body_span.start),
            ));
        }
        return Some(qa_completion_items(source.as_ref(), offset));
    }

    Some(abide_completion_items_for_source(
        state,
        source.as_ref(),
        offset,
    ))
}

fn embedded_abide_block_at(
    source: &str,
    offset: usize,
) -> Option<abide::qa::parse::QAEmbeddedAbideBlock> {
    abide::qa::parse::embedded_abide_blocks(source)
        .ok()?
        .into_iter()
        .find(|block| offset >= block.body_span.start && offset <= block.body_span.end)
}

fn abide_completion_items_for_source(
    state: &mut LspState,
    source: &str,
    offset: usize,
) -> Vec<CompletionItem> {
    let context = completion_context(source, offset);
    let keyword_context = keyword_completion_context(source, offset);
    let mut items = keyword_completions(context, keyword_context);
    if let Ok(index) = build_workspace_index(&mut state.workspace) {
        items.extend(
            index
                .completion_symbols(context)
                .into_iter()
                .map(completion_item_for_symbol),
        );
    }
    items
}

fn qa_completion_items(source: &str, offset: usize) -> Vec<CompletionItem> {
    let candidates = match qa_completion_context(source, offset) {
        QACompletionContext::Command => qa_command_candidates(),
        QACompletionContext::Query => qa_query_subcommand_candidates(),
        QACompletionContext::None => Vec::new(),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QACompletionContext {
    Command,
    Query,
    None,
}

fn qa_completion_context(source: &str, offset: usize) -> QACompletionContext {
    let line = current_line_prefix(source, offset);
    let token_count = line.split_whitespace().count();
    if token_count <= 1 {
        return QACompletionContext::Command;
    }

    let first = line.split_whitespace().next().unwrap_or_default();
    if matches!(first, "ask" | "explain" | "assert") && token_count == 2 {
        QACompletionContext::Query
    } else {
        QACompletionContext::None
    }
}

fn current_line_prefix(source: &str, offset: usize) -> &str {
    let prefix = &source[..offset.min(source.len())];
    prefix.rsplit('\n').next().unwrap_or(prefix)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KeywordCompletionContext {
    General,
    Contract,
}

fn keyword_completion_context(source: &str, offset: usize) -> KeywordCompletionContext {
    let prefix = &source[..offset.min(source.len())];
    let since_last_boundary = prefix
        .rsplit(['{', '}'])
        .next()
        .unwrap_or(prefix)
        .trim_start();
    if starts_with_any_keyword(since_last_boundary, &["fn", "action", "command", "proc"]) {
        KeywordCompletionContext::Contract
    } else {
        KeywordCompletionContext::General
    }
}

fn starts_with_any_keyword(text: &str, keywords: &[&str]) -> bool {
    keywords.iter().any(|keyword| {
        text.strip_prefix(keyword)
            .is_some_and(|rest| rest.chars().next().is_none_or(is_word_boundary))
    })
}

fn is_word_boundary(ch: char) -> bool {
    !(ch == '_' || ch.is_ascii_alphanumeric())
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
        CompletionContext::AfterAt | CompletionContext::AfterDot => &[],
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
    fn keyword_completions_include_contract_keywords() {
        let labels = keyword_completions(
            CompletionContext::General,
            KeywordCompletionContext::General,
        )
        .into_iter()
        .map(|item| item.label)
        .collect::<Vec<_>>();

        assert!(labels.contains(&"requires".to_owned()));
        assert!(labels.contains(&"ensures".to_owned()));
        assert!(labels.contains(&"decreases".to_owned()));
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
        let file_id = state.workspace.set_file_source("/tmp/commands.qa", "ver");
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
        let file_id = state.workspace.set_file_source("/tmp/query.qa", "ask fs");
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
    }

    #[test]
    fn lsp_completion_uses_abide_keywords_inside_embedded_qa_blocks() {
        let mut state = LspState::new(PathBuf::from("."));
        let uri = Url::parse("file:///tmp/embedded_completion.qa").expect("uri");
        let source = "ask entities\nabide {\n  ent\n}\n";
        let file_id = state
            .workspace
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
        let file_id = state.workspace.set_file_source(&qa_path, source);
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

    #[test]
    fn lsp_diagnostics_do_not_lower_valid_qa_as_abide_source() {
        let mut state = LspState::new(PathBuf::from("."));
        let file_id = state
            .workspace
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
            .workspace
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
        let file_id = state.workspace.set_file_source(
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
            .workspace
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
            .workspace
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
        let file_id = state.workspace.set_file_source(&qa_path, source);

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
        let file_id = state.workspace.set_file_source(&qa_path, source);

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
