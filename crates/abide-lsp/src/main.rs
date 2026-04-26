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

#[derive(Debug)]
struct OpenDocument {
    file_id: FileId,
    version: i32,
}

struct LspState {
    workspace: CompilerWorkspace,
    documents: HashMap<Url, OpenDocument>,
    published_by_root: HashMap<FileId, HashSet<Url>>,
}

impl LspState {
    fn new(root_dir: PathBuf) -> Self {
        Self {
            workspace: CompilerWorkspace::with_root_dir(root_dir),
            documents: HashMap::new(),
            published_by_root: HashMap::new(),
        }
    }

    fn should_accept_document_version(&self, uri: &Url, version: i32) -> bool {
        self.documents
            .get(uri)
            .is_none_or(|doc| version > doc.version)
    }

    fn document_version(&self, uri: &Url) -> Option<i32> {
        self.documents.get(uri).map(|doc| doc.version)
    }

    fn uri_published_elsewhere(&self, root_file_id: FileId, uri: &Url) -> bool {
        self.published_by_root
            .iter()
            .any(|(other_root, uris)| *other_root != root_file_id && uris.contains(uri))
    }
}

struct Backend {
    client: Client,
    state: Arc<Mutex<LspState>>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        let root_dir = params
            .root_uri
            .and_then(|uri| uri.to_file_path().ok())
            .or_else(|| std::env::current_dir().ok())
            .unwrap_or_else(|| PathBuf::from("."));
        *self.state.lock().await = LspState::new(root_dir);

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

    async fn refresh_diagnostics(&self, root_file_id: FileId) {
        let (publish, stale, versions, log_error) = {
            let mut state = self.state.lock().await;
            let mut grouped: HashMap<Url, Vec<tower_lsp::lsp_types::Diagnostic>> = HashMap::new();
            let mut current = HashSet::new();
            let mut log_error = None;

            match state.workspace.elaborate(root_file_id) {
                Ok(elaborated) => {
                    for diagnostic in &elaborated.diagnostics {
                        let Some((uri, lsp_diagnostic)) =
                            diagnostic_to_lsp(&state.workspace, root_file_id, diagnostic)
                        else {
                            continue;
                        };
                        current.insert(uri.clone());
                        grouped.entry(uri).or_default().push(lsp_diagnostic);
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
            | IdeSymbolKind::Function
            | IdeSymbolKind::Step => CompletionItemKind::FUNCTION,
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

fn range_from_span(source: &str, span: abide::span::Span) -> Option<Range> {
    Some(Range {
        start: offset_to_position(source, span.start)?,
        end: offset_to_position(source, span.end)?,
    })
}

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
}
