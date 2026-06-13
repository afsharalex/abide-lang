//! IDE primitives shared by `abide-lsp`, `abide explain`, and the
//! REPL. Provides a flattened symbol index over a workspace plus
//! offset-keyed lookup (identifier-at, completion-context) routines.

use std::collections::BTreeSet;
use std::path::Path;

use crate::ast::{
    EntityItem, InterfaceItem, ProcItem, Program, SystemItem, TopDecl, TypeVariant, UseDecl,
    UseItem, VerifyDecl, Visibility,
};
use crate::driver;
use crate::span::Span;
use crate::workspace::{CompilerWorkspace, FileId};

/// Kind label for a symbol exposed to the IDE.
///
/// Used by the LSP to map symbols to `lsp_types::CompletionItemKind`
/// and to disambiguate entries with the same name. [`Self::sort_rank`]
/// orders completion results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IdeSymbolKind {
    Module,
    Type,
    Variant,
    Record,
    Alias,
    Newtype,
    Entity,
    Interface,
    Field,
    Action,
    System,
    Program,
    Proc,
    Command,
    Query,
    Pred,
    Prop,
    Verify,
    Theorem,
    Lemma,
    Scene,
    Axiom,
    Const,
    Function,
    Invariant,
    Derived,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IdeVisibility {
    Public,
    Private,
}

impl From<Visibility> for IdeVisibility {
    fn from(value: Visibility) -> Self {
        match value {
            Visibility::Public => Self::Public,
            Visibility::Private => Self::Private,
        }
    }
}

impl IdeSymbolKind {
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Module => "module",
            Self::Type => "type",
            Self::Variant => "variant",
            Self::Record => "record",
            Self::Alias => "alias",
            Self::Newtype => "newtype",
            Self::Entity => "entity",
            Self::Interface => "interface",
            Self::Field => "field",
            Self::Action => "action",
            Self::System => "system",
            Self::Program => "program",
            Self::Proc => "proc",
            Self::Command => "command",
            Self::Query => "query",
            Self::Pred => "pred",
            Self::Prop => "prop",
            Self::Verify => "verify",
            Self::Theorem => "theorem",
            Self::Lemma => "lemma",
            Self::Scene => "scene",
            Self::Axiom => "axiom",
            Self::Const => "const",
            Self::Function => "fn",
            Self::Invariant => "invariant",
            Self::Derived => "derived",
        }
    }

    #[must_use]
    pub fn sort_rank(self) -> u8 {
        match self {
            Self::Command => 0,
            Self::Query => 1,
            Self::Function => 2,
            Self::Pred => 3,
            Self::Type | Self::Record | Self::Alias | Self::Newtype => 4,
            Self::Entity => 5,
            Self::Interface | Self::System | Self::Program | Self::Proc => 6,
            Self::Field | Self::Action | Self::Derived | Self::Invariant => 7,
            Self::Const => 8,
            Self::Prop | Self::Verify | Self::Theorem | Self::Lemma | Self::Scene | Self::Axiom => {
                9
            }
            Self::Variant => 9,
            Self::Module => 10,
        }
    }
}

/// Cursor position context for completion. This is the small
/// LSP-facing projection of [`AbideCursorContext`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionContext {
    /// No special trigger character — show all keywords and top-level
    /// symbols.
    General,
    /// Cursor immediately after `@` — show enum constructors.
    AfterAt,
    /// Cursor immediately after `.` — show field/member names.
    AfterDot,
    /// Cursor immediately after `::` — show scope/module members.
    AfterScope,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbideCursorContext {
    TopLevel,
    ModuleDecl,
    UseDecl,
    IncludePath,
    EntityBody { name: Option<String> },
    SystemBody { name: Option<String> },
    InterfaceBody { name: Option<String> },
    ProgramBody { name: Option<String> },
    FunctionContract,
    FunctionBody { name: Option<String> },
    ActionContract,
    ActionBody { name: Option<String> },
    CommandContract,
    CommandBody { name: Option<String> },
    ProcContract,
    ProcBody { name: Option<String> },
    AfterAt,
    AfterDot,
    AfterScope,
    General,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QaCursorContext {
    Command,
    Query,
    LoadPath,
    EmbeddedAbide(AbideCursorContext),
    None,
}

/// One indexed symbol — a name with a declaration site, kind, and
/// human-readable `detail` (used as the LSP hover body).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdeSymbol {
    pub name: String,
    pub kind: IdeSymbolKind,
    pub file_id: FileId,
    pub span: Span,
    pub detail: String,
    pub module: Option<String>,
    pub owner: Option<String>,
    pub visibility: IdeVisibility,
}

/// One occurrence of a name in source text. Multiple occurrences may
/// reference the same [`IdeSymbol`]; the LSP uses these for
/// `references` and `rename`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdeOccurrence {
    pub name: String,
    pub file_id: FileId,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdeImportKind {
    Glob,
    Single { name: String, alias: Option<String> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdeImport {
    pub file_id: FileId,
    pub module: String,
    pub kind: IdeImportKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdeInclude {
    pub file_id: FileId,
    pub path: String,
    pub span: Span,
}

/// Flat per-workspace index of symbols and their textual occurrences.
/// Rebuilt eagerly each request — there is no incremental layer
/// (latency is dominated by parsing, not indexing).
#[derive(Debug, Clone, Default)]
pub struct WorkspaceIndex {
    pub symbols: Vec<IdeSymbol>,
    pub occurrences: Vec<IdeOccurrence>,
    pub imports: Vec<IdeImport>,
    pub includes: Vec<IdeInclude>,
    pub file_modules: Vec<(FileId, Option<String>)>,
}

impl WorkspaceIndex {
    /// Returns every indexed symbol named `name`, ordered by
    /// [`IdeSymbolKind::sort_rank`] so highest-priority kinds come first.
    #[must_use]
    pub fn symbols_named(&self, name: &str) -> Vec<&IdeSymbol> {
        let mut matches: Vec<_> = self
            .symbols
            .iter()
            .filter(|symbol| symbol.name == name)
            .collect();
        matches.sort_by_key(|symbol| symbol.kind.sort_rank());
        matches
    }

    /// Returns the subset of indexed symbols offered as completions in
    /// the given [`CompletionContext`].
    #[must_use]
    pub fn completion_symbols(&self, context: CompletionContext) -> Vec<&IdeSymbol> {
        self.symbols
            .iter()
            .filter(|symbol| match context {
                CompletionContext::General => matches!(
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
                ),
                CompletionContext::AfterAt => symbol.kind == IdeSymbolKind::Variant,
                CompletionContext::AfterDot => matches!(
                    symbol.kind,
                    IdeSymbolKind::Field
                        | IdeSymbolKind::Action
                        | IdeSymbolKind::Command
                        | IdeSymbolKind::Query
                        | IdeSymbolKind::Derived
                ),
                CompletionContext::AfterScope => false,
            })
            .collect()
    }

    #[must_use]
    pub fn symbols_in_module(&self, module: &str, name: &str) -> Vec<&IdeSymbol> {
        let mut matches = self
            .symbols
            .iter()
            .filter(|symbol| symbol.module.as_deref() == Some(module) && symbol.name == name)
            .collect::<Vec<_>>();
        matches.sort_by_key(|symbol| symbol.kind.sort_rank());
        matches
    }

    #[must_use]
    pub fn module_exports(&self, module: &str) -> Vec<&IdeSymbol> {
        let mut exports = self
            .symbols
            .iter()
            .filter(|symbol| {
                symbol.module.as_deref() == Some(module)
                    && symbol.owner.is_none()
                    && symbol.kind != IdeSymbolKind::Module
            })
            .collect::<Vec<_>>();
        exports.sort_by_key(|symbol| (symbol.kind.sort_rank(), symbol.name.as_str()));
        exports
    }

    #[must_use]
    pub fn members_by_owner(&self, owner: &str) -> Vec<&IdeSymbol> {
        let mut members = self
            .symbols
            .iter()
            .filter(|symbol| {
                symbol.owner.as_deref() == Some(owner)
                    && matches!(
                        symbol.kind,
                        IdeSymbolKind::Field
                            | IdeSymbolKind::Action
                            | IdeSymbolKind::Command
                            | IdeSymbolKind::Query
                            | IdeSymbolKind::Derived
                            | IdeSymbolKind::Invariant
                            | IdeSymbolKind::Proc
                    )
            })
            .collect::<Vec<_>>();
        members.sort_by_key(|symbol| (symbol.kind.sort_rank(), symbol.name.as_str()));
        members
    }

    #[must_use]
    pub fn enum_variants_by_type(&self, type_name: &str) -> Vec<&IdeSymbol> {
        let mut variants = self
            .symbols
            .iter()
            .filter(|symbol| {
                symbol.owner.as_deref() == Some(type_name) && symbol.kind == IdeSymbolKind::Variant
            })
            .collect::<Vec<_>>();
        variants.sort_by_key(|symbol| symbol.name.as_str());
        variants
    }

    #[must_use]
    pub fn visible_symbols(&self, file_id: FileId, _offset: usize) -> Vec<IdeSymbol> {
        let current_module = self
            .file_modules
            .iter()
            .find(|(candidate, _)| *candidate == file_id)
            .and_then(|(_, module)| module.as_deref());
        let mut visible = Vec::new();

        visible.extend(
            self.symbols
                .iter()
                .filter(|symbol| {
                    symbol.owner.is_none()
                        && symbol.kind != IdeSymbolKind::Module
                        && symbol.module.as_deref() == current_module
                })
                .cloned(),
        );

        for import in self
            .imports
            .iter()
            .filter(|import| import.file_id == file_id)
        {
            match &import.kind {
                IdeImportKind::Glob => {
                    visible.extend(self.module_exports(&import.module).into_iter().cloned());
                }
                IdeImportKind::Single { name, alias } => {
                    if let Some(symbol) = self
                        .module_exports(&import.module)
                        .into_iter()
                        .find(|symbol| symbol.name == *name)
                    {
                        let mut imported = symbol.clone();
                        if let Some(alias) = alias {
                            imported.name.clone_from(alias);
                        }
                        visible.push(imported);
                    }
                }
            }
        }

        dedup_symbol_clones(&mut visible);
        visible.sort_by_key(|symbol| (symbol.kind.sort_rank(), symbol.name.clone()));
        visible
    }

    #[must_use]
    pub fn references_named(&self, name: &str) -> Vec<&IdeOccurrence> {
        self.occurrences
            .iter()
            .filter(|occurrence| occurrence.name == name)
            .collect()
    }
}

/// Classifies the trigger character immediately before `offset` in
/// `source`, returning the relevant [`CompletionContext`].
#[must_use]
pub fn completion_context(source: &str, offset: usize) -> CompletionContext {
    match classify_abide_cursor(source, offset) {
        AbideCursorContext::AfterAt => CompletionContext::AfterAt,
        AbideCursorContext::AfterDot => CompletionContext::AfterDot,
        AbideCursorContext::AfterScope => CompletionContext::AfterScope,
        _ => CompletionContext::General,
    }
}

#[must_use]
pub fn classify_abide_cursor(source: &str, offset: usize) -> AbideCursorContext {
    let offset = clamp_to_char_boundary(source, offset);
    let prefix = &source[..offset];
    let trimmed_prefix = prefix.trim_end_matches(char::is_whitespace);
    if trimmed_prefix.ends_with("::") {
        return AbideCursorContext::AfterScope;
    }
    match trimmed_prefix.chars().last() {
        Some('@') => return AbideCursorContext::AfterAt,
        Some('.') => return AbideCursorContext::AfterDot,
        _ => {}
    }

    let line = current_line_prefix(source, offset).trim_start();
    if starts_with_keyword(line, "include") {
        return AbideCursorContext::IncludePath;
    }
    if starts_with_keyword(line, "module") {
        return AbideCursorContext::ModuleDecl;
    }
    if starts_with_keyword(line, "use") {
        return AbideCursorContext::UseDecl;
    }

    if let Some(context) = pending_contract_context(prefix) {
        return context;
    }

    if let Some(frame) = block_frames(source, offset).last() {
        return frame.body_context();
    }

    if block_depth(source, offset) == 0 {
        AbideCursorContext::TopLevel
    } else {
        AbideCursorContext::General
    }
}

#[must_use]
pub fn classify_qa_cursor(source: &str, offset: usize) -> QaCursorContext {
    let offset = clamp_to_char_boundary(source, offset);
    if let Ok(blocks) = crate::qa::parse::embedded_abide_blocks(source) {
        if let Some(block) = blocks
            .into_iter()
            .find(|block| offset >= block.body_span.start && offset <= block.body_span.end)
        {
            let body_offset = offset.saturating_sub(block.body_span.start);
            return QaCursorContext::EmbeddedAbide(classify_abide_cursor(&block.body, body_offset));
        }
    }

    let line = current_line_prefix(source, offset);
    let token_count = line.split_whitespace().count();
    let first = line.split_whitespace().next().unwrap_or_default();
    if starts_with_keyword(line.trim_start(), "load") && token_count <= 2 {
        return QaCursorContext::LoadPath;
    }
    if token_count <= 1 {
        return QaCursorContext::Command;
    }
    if matches!(first, "ask" | "explain" | "assert") && token_count == 2 {
        QaCursorContext::Query
    } else {
        QaCursorContext::None
    }
}

fn current_line_prefix(source: &str, offset: usize) -> &str {
    let prefix = &source[..clamp_to_char_boundary(source, offset)];
    prefix.rsplit('\n').next().unwrap_or(prefix)
}

fn clamp_to_char_boundary(source: &str, offset: usize) -> usize {
    let mut boundary = offset.min(source.len());
    while !source.is_char_boundary(boundary) {
        boundary = boundary
            .checked_sub(1)
            .expect("byte offset 0 is always a UTF-8 boundary");
    }
    boundary
}

fn starts_with_keyword(text: &str, keyword: &str) -> bool {
    text.strip_prefix(keyword)
        .is_some_and(|rest| rest.chars().next().is_none_or(is_word_boundary))
}

fn is_word_boundary(ch: char) -> bool {
    !(ch == '_' || ch.is_ascii_alphanumeric())
}

fn pending_contract_context(prefix: &str) -> Option<AbideCursorContext> {
    let since_last_boundary = prefix.rsplit(['{', '}']).next().unwrap_or(prefix);
    match last_callable_decl_keyword(since_last_boundary)?.as_str() {
        "fn" => Some(AbideCursorContext::FunctionContract),
        "action" => Some(AbideCursorContext::ActionContract),
        "command" => Some(AbideCursorContext::CommandContract),
        "proc" => Some(AbideCursorContext::ProcContract),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BlockFrame {
    kind: BlockKind,
    name: Option<String>,
}

impl BlockFrame {
    fn body_context(&self) -> AbideCursorContext {
        match self.kind {
            BlockKind::Entity => AbideCursorContext::EntityBody {
                name: self.name.clone(),
            },
            BlockKind::System => AbideCursorContext::SystemBody {
                name: self.name.clone(),
            },
            BlockKind::Interface => AbideCursorContext::InterfaceBody {
                name: self.name.clone(),
            },
            BlockKind::Program => AbideCursorContext::ProgramBody {
                name: self.name.clone(),
            },
            BlockKind::Function => AbideCursorContext::FunctionBody {
                name: self.name.clone(),
            },
            BlockKind::Action => AbideCursorContext::ActionBody {
                name: self.name.clone(),
            },
            BlockKind::Command => AbideCursorContext::CommandBody {
                name: self.name.clone(),
            },
            BlockKind::Proc => AbideCursorContext::ProcBody {
                name: self.name.clone(),
            },
            BlockKind::Other => AbideCursorContext::General,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockKind {
    Entity,
    System,
    Interface,
    Program,
    Function,
    Action,
    Command,
    Proc,
    Other,
}

fn block_frames(source: &str, offset: usize) -> Vec<BlockFrame> {
    let offset = clamp_to_char_boundary(source, offset);
    let mut frames = Vec::new();
    let mut segment_start = 0;
    let mut in_string = false;
    let mut escaped = false;
    for (index, ch) in source
        .char_indices()
        .take_while(|(index, _)| *index < offset)
    {
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '{' => {
                frames.push(block_frame_from_header(&source[segment_start..index]));
                segment_start = index.saturating_add(ch.len_utf8());
            }
            '}' => {
                frames.pop();
                segment_start = index.saturating_add(ch.len_utf8());
            }
            _ => {}
        }
    }
    frames
}

fn block_depth(source: &str, offset: usize) -> usize {
    block_frames(source, offset).len()
}

fn block_frame_from_header(header: &str) -> BlockFrame {
    let words = words(header);
    let Some(keyword_index) = words
        .iter()
        .rposition(|word| declaration_block_kind(word).is_some())
    else {
        return BlockFrame {
            kind: BlockKind::Other,
            name: None,
        };
    };
    BlockFrame {
        kind: declaration_block_kind(&words[keyword_index]).unwrap_or(BlockKind::Other),
        name: words.get(keyword_index + 1).cloned(),
    }
}

fn declaration_block_kind(word: &str) -> Option<BlockKind> {
    match word {
        "entity" => Some(BlockKind::Entity),
        "system" => Some(BlockKind::System),
        "interface" => Some(BlockKind::Interface),
        "program" => Some(BlockKind::Program),
        "fn" => Some(BlockKind::Function),
        "action" => Some(BlockKind::Action),
        "command" => Some(BlockKind::Command),
        "proc" => Some(BlockKind::Proc),
        _ => None,
    }
}

fn last_callable_decl_keyword(text: &str) -> Option<String> {
    let words = words(text);
    let keyword_index = words
        .iter()
        .rposition(|word| matches!(word.as_str(), "fn" | "action" | "command" | "proc"))?;
    words.get(keyword_index + 1)?;
    Some(words[keyword_index].clone())
}

fn words(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut current = String::new();
    for ch in text.chars() {
        if ch == '_' || ch.is_ascii_alphanumeric() {
            current.push(ch);
        } else if !current.is_empty() {
            out.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}

/// Rebuilds the full workspace index from scratch by walking every
/// known file's parsed program and token stream.
pub fn build_workspace_index(workspace: &mut CompilerWorkspace) -> miette::Result<WorkspaceIndex> {
    let mut index = WorkspaceIndex::default();
    for (file_id, path) in workspace.known_files() {
        if !is_abide_source_path(&path) {
            continue;
        }
        let Some(source) = workspace.source_text(file_id) else {
            continue;
        };
        let Ok(parse) = workspace.parse(file_id) else {
            continue;
        };
        let Ok(tokens) = driver::lex_source(source.as_ref()) else {
            continue;
        };
        let module = module_name(&parse.program);
        index.file_modules.push((file_id, module.clone()));
        collect_program_imports_and_includes(&mut index, file_id, &parse.program);
        index
            .occurrences
            .extend(name_occurrences_from_tokens(file_id, &tokens));
        collect_program_symbols(
            &mut index.symbols,
            file_id,
            source.as_ref(),
            &parse.program,
            &tokens,
            module.as_deref(),
        );
    }
    dedup_symbols(&mut index.symbols);
    dedup_occurrences(&mut index.occurrences);
    Ok(index)
}

fn is_abide_source_path(path: &Path) -> bool {
    path.extension()
        .and_then(std::ffi::OsStr::to_str)
        .is_some_and(|extension| matches!(extension, "ab" | "abi" | "abp"))
}

/// Returns the [`IdeOccurrence`] under `offset` in `file_id`, or
/// `None` if the offset is not on an identifier.
pub fn identifier_at(
    workspace: &mut CompilerWorkspace,
    file_id: FileId,
    offset: usize,
) -> miette::Result<Option<IdeOccurrence>> {
    let source = workspace
        .source_text(file_id)
        .ok_or_else(|| miette::miette!("unknown file id {:?}", file_id))?;
    let Ok(tokens) = driver::lex_source(source.as_ref()) else {
        return Ok(None);
    };
    Ok(tokens.into_iter().find_map(|(token, span)| match token {
        crate::lex::Token::Name(name) if span.start <= offset && offset <= span.end => {
            Some(IdeOccurrence {
                name,
                file_id,
                span,
            })
        }
        _ => None,
    }))
}

fn dedup_symbols(symbols: &mut Vec<IdeSymbol>) {
    let mut seen = BTreeSet::new();
    symbols.retain(|symbol| {
        seen.insert((
            symbol.file_id,
            symbol.span.start,
            symbol.span.end,
            symbol.kind.sort_rank(),
            symbol.name.clone(),
        ))
    });
}

fn dedup_occurrences(occurrences: &mut Vec<IdeOccurrence>) {
    let mut seen = BTreeSet::new();
    occurrences.retain(|occurrence| {
        seen.insert((
            occurrence.file_id,
            occurrence.span.start,
            occurrence.span.end,
            occurrence.name.clone(),
        ))
    });
}

fn dedup_symbol_clones(symbols: &mut Vec<IdeSymbol>) {
    let mut seen = BTreeSet::new();
    symbols.retain(|symbol| {
        seen.insert((
            symbol.name.clone(),
            symbol.kind.sort_rank(),
            symbol.file_id,
            symbol.span.start,
            symbol.span.end,
        ))
    });
}

fn name_occurrences_from_tokens(
    file_id: FileId,
    tokens: &[(crate::lex::Token, Span)],
) -> Vec<IdeOccurrence> {
    tokens
        .iter()
        .filter_map(|(token, span)| match token {
            crate::lex::Token::Name(name) => Some(IdeOccurrence {
                name: name.clone(),
                file_id,
                span: *span,
            }),
            _ => None,
        })
        .collect()
}

fn collect_program_symbols(
    out: &mut Vec<IdeSymbol>,
    file_id: FileId,
    source: &str,
    program: &Program,
    tokens: &[(crate::lex::Token, Span)],
    module: Option<&str>,
) {
    SymbolCollector {
        out,
        file_id,
        source,
        tokens,
        module,
    }
    .collect_program(program);
}

fn module_name(program: &Program) -> Option<String> {
    program.decls.iter().find_map(|decl| match decl {
        TopDecl::Module(module) => Some(module.name.clone()),
        _ => None,
    })
}

fn collect_program_imports_and_includes(
    index: &mut WorkspaceIndex,
    file_id: FileId,
    program: &Program,
) {
    for decl in &program.decls {
        match decl {
            TopDecl::Include(include) => index.includes.push(IdeInclude {
                file_id,
                path: include.path.clone(),
                span: include.span,
            }),
            TopDecl::Use(use_decl) => collect_use_decl(&mut index.imports, file_id, use_decl),
            _ => {}
        }
    }
}

fn collect_use_decl(imports: &mut Vec<IdeImport>, file_id: FileId, use_decl: &UseDecl) {
    match use_decl {
        UseDecl::All { module, span } => imports.push(IdeImport {
            file_id,
            module: module.clone(),
            kind: IdeImportKind::Glob,
            span: *span,
        }),
        UseDecl::Single { module, name, span } => imports.push(IdeImport {
            file_id,
            module: module.clone(),
            kind: IdeImportKind::Single {
                name: name.clone(),
                alias: None,
            },
            span: *span,
        }),
        UseDecl::Alias {
            module,
            name,
            alias,
            span,
        } => imports.push(IdeImport {
            file_id,
            module: module.clone(),
            kind: IdeImportKind::Single {
                name: name.clone(),
                alias: Some(alias.clone()),
            },
            span: *span,
        }),
        UseDecl::Items {
            module,
            items,
            span,
        } => {
            for item in items {
                match item {
                    UseItem::Name { name, .. } => imports.push(IdeImport {
                        file_id,
                        module: module.clone(),
                        kind: IdeImportKind::Single {
                            name: name.clone(),
                            alias: None,
                        },
                        span: *span,
                    }),
                    UseItem::Alias { name, alias, .. } => imports.push(IdeImport {
                        file_id,
                        module: module.clone(),
                        kind: IdeImportKind::Single {
                            name: name.clone(),
                            alias: Some(alias.clone()),
                        },
                        span: *span,
                    }),
                }
            }
        }
    }
}

struct SymbolCollector<'a> {
    out: &'a mut Vec<IdeSymbol>,
    file_id: FileId,
    source: &'a str,
    tokens: &'a [(crate::lex::Token, Span)],
    module: Option<&'a str>,
}

impl SymbolCollector<'_> {
    fn collect_program(&mut self, program: &Program) {
        for decl in &program.decls {
            self.collect_top_decl(decl);
        }
    }

    fn collect_top_decl(&mut self, decl: &TopDecl) {
        match decl {
            TopDecl::Module(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::Module),
            TopDecl::Const(decl) => {
                self.visible_top(decl.span, &decl.name, IdeSymbolKind::Const, decl.visibility);
            }
            TopDecl::Fn(decl) => {
                self.visible_top(
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Function,
                    decl.visibility,
                );
            }
            TopDecl::Type(decl) => self.collect_type_decl(decl),
            TopDecl::Record(decl) => {
                self.visible_top(
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Record,
                    decl.visibility,
                );
                for field in &decl.fields {
                    self.symbol_with(
                        field.span,
                        &field.name,
                        IdeSymbolKind::Field,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
            }
            TopDecl::Alias(decl) => {
                self.visible_top(decl.span, &decl.name, IdeSymbolKind::Alias, decl.visibility);
            }
            TopDecl::Newtype(decl) => {
                self.visible_top(
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Newtype,
                    decl.visibility,
                );
            }
            TopDecl::Entity(decl) => self.collect_entity_decl(decl),
            TopDecl::Interface(decl) => self.collect_interface_decl(decl),
            TopDecl::Extern(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::System),
            TopDecl::System(decl) => self.collect_system_decl(decl),
            TopDecl::Proc(decl) => self.collect_proc_decl(decl),
            TopDecl::Program(decl) => self.collect_program_decl(decl),
            TopDecl::Pred(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::Pred),
            TopDecl::Prop(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::Prop),
            TopDecl::Verify(VerifyDecl { name, span, .. }) => {
                self.public_top(*span, name, IdeSymbolKind::Verify);
            }
            TopDecl::Theorem(decl) => {
                self.public_top(decl.span, &decl.name, IdeSymbolKind::Theorem);
            }
            TopDecl::Lemma(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::Lemma),
            TopDecl::Scene(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::Scene),
            TopDecl::Axiom(decl) => self.public_top(decl.span, &decl.name, IdeSymbolKind::Axiom),
            TopDecl::Include(_) | TopDecl::Use(_) | TopDecl::Under(_) | TopDecl::Error(_) => {}
        }
    }

    fn public_top(&mut self, span: Span, name: &str, kind: IdeSymbolKind) {
        self.symbol_with(span, name, kind, None, IdeVisibility::Public);
    }

    fn visible_top(&mut self, span: Span, name: &str, kind: IdeSymbolKind, visibility: Visibility) {
        self.symbol_with(span, name, kind, None, visibility.into());
    }

    fn collect_type_decl(&mut self, decl: &crate::ast::TypeDecl) {
        let visibility = decl.visibility.into();
        self.symbol_with(decl.span, &decl.name, IdeSymbolKind::Type, None, visibility);
        for variant in &decl.variants {
            match variant {
                TypeVariant::Simple { name, span }
                | TypeVariant::Tuple { name, span, .. }
                | TypeVariant::Record { name, span, .. }
                | TypeVariant::Param { name, span, .. } => {
                    self.symbol_with(
                        *span,
                        name,
                        IdeSymbolKind::Variant,
                        Some(&decl.name),
                        visibility,
                    );
                }
            }
        }
    }

    fn collect_entity_decl(&mut self, decl: &crate::ast::EntityDecl) {
        self.symbol_with(
            decl.span,
            &decl.name,
            IdeSymbolKind::Entity,
            None,
            decl.visibility.into(),
        );
        for item in &decl.items {
            match item {
                EntityItem::Field(field) => {
                    self.symbol_with(
                        field.span,
                        &field.name,
                        IdeSymbolKind::Field,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
                EntityItem::Action(action) => {
                    self.symbol_with(
                        action.span,
                        &action.name,
                        IdeSymbolKind::Action,
                        Some(&decl.name),
                        IdeVisibility::Public,
                    );
                }
                EntityItem::Derived(derived) => {
                    self.symbol_with(
                        derived.span,
                        &derived.name,
                        IdeSymbolKind::Derived,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
                EntityItem::Invariant(invariant) => {
                    self.symbol_with(
                        invariant.span,
                        &invariant.name,
                        IdeSymbolKind::Invariant,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
                EntityItem::Fsm(fsm) => self.symbol_with(
                    fsm.span,
                    &fsm.field,
                    IdeSymbolKind::Invariant,
                    Some(&decl.name),
                    IdeVisibility::Private,
                ),
                EntityItem::Error(_) => {}
            }
        }
    }

    fn collect_interface_decl(&mut self, decl: &crate::ast::InterfaceDecl) {
        self.symbol_with(
            decl.span,
            &decl.name,
            IdeSymbolKind::Interface,
            None,
            IdeVisibility::Public,
        );
        for item in &decl.items {
            match item {
                InterfaceItem::Command(command) => {
                    self.symbol_with(
                        command.span,
                        &command.name,
                        IdeSymbolKind::Command,
                        Some(&decl.name),
                        IdeVisibility::Public,
                    );
                }
                InterfaceItem::QuerySig(query) => {
                    self.symbol_with(
                        query.span,
                        &query.name,
                        IdeSymbolKind::Query,
                        Some(&decl.name),
                        IdeVisibility::Public,
                    );
                }
                InterfaceItem::Error(_) => {}
            }
        }
    }

    fn collect_system_decl(&mut self, decl: &crate::ast::SystemDecl) {
        self.symbol_with(
            decl.span,
            &decl.name,
            IdeSymbolKind::System,
            None,
            IdeVisibility::Public,
        );
        for item in &decl.items {
            match item {
                SystemItem::Field(field) => {
                    self.symbol_with(
                        field.span,
                        &field.name,
                        IdeSymbolKind::Field,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
                SystemItem::Dep(_) => {}
                SystemItem::Command(command) => {
                    self.symbol_with(
                        command.span,
                        &command.name,
                        IdeSymbolKind::Command,
                        Some(&decl.name),
                        IdeVisibility::Public,
                    );
                }
                SystemItem::Action(action) => {
                    self.symbol_with(
                        action.span,
                        &action.name,
                        IdeSymbolKind::Action,
                        Some(&decl.name),
                        IdeVisibility::Public,
                    );
                }
                SystemItem::Query(query) => {
                    self.symbol_with(
                        query.span,
                        &query.name,
                        IdeSymbolKind::Query,
                        Some(&decl.name),
                        IdeVisibility::Public,
                    );
                }
                SystemItem::Pred(pred) => self.symbol_with(
                    pred.span,
                    &pred.name,
                    IdeSymbolKind::Pred,
                    Some(&decl.name),
                    IdeVisibility::Private,
                ),
                SystemItem::Proc(proc_decl) => {
                    self.collect_proc_decl_with_owner(proc_decl, &decl.name);
                }
                SystemItem::Derived(derived) => {
                    self.symbol_with(
                        derived.span,
                        &derived.name,
                        IdeSymbolKind::Derived,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
                SystemItem::Invariant(invariant) => {
                    self.symbol_with(
                        invariant.span,
                        &invariant.name,
                        IdeSymbolKind::Invariant,
                        Some(&decl.name),
                        IdeVisibility::Private,
                    );
                }
                SystemItem::Fsm(fsm) => self.symbol_with(
                    fsm.span,
                    &fsm.field,
                    IdeSymbolKind::Invariant,
                    Some(&decl.name),
                    IdeVisibility::Private,
                ),
                SystemItem::Error(_) => {}
            }
        }
    }

    fn collect_proc_decl(&mut self, decl: &crate::ast::ProcDecl) {
        self.symbol_with(
            decl.span,
            &decl.name,
            IdeSymbolKind::Proc,
            None,
            IdeVisibility::Public,
        );
        self.collect_proc_nodes(&decl.items);
    }

    fn collect_proc_nodes(&mut self, items: &[ProcItem]) {
        for proc_item in items {
            if let ProcItem::Node { name, span, .. } = proc_item {
                self.symbol_with(
                    *span,
                    name,
                    IdeSymbolKind::Proc,
                    None,
                    IdeVisibility::Private,
                );
            }
        }
    }

    fn collect_program_decl(&mut self, decl: &crate::ast::ProgramDecl) {
        self.symbol_with(
            decl.span,
            &decl.name,
            IdeSymbolKind::Program,
            None,
            IdeVisibility::Public,
        );
        for item in &decl.items {
            if let crate::ast::ProgramItem::Proc(proc_decl) = item {
                self.collect_proc_decl_with_owner(proc_decl, &decl.name);
            }
        }
    }

    fn collect_proc_decl_with_owner(&mut self, decl: &crate::ast::ProcDecl, owner: &str) {
        self.symbol_with(
            decl.span,
            &decl.name,
            IdeSymbolKind::Proc,
            Some(owner),
            IdeVisibility::Public,
        );
        for proc_item in &decl.items {
            if let ProcItem::Node { name, span, .. } = proc_item {
                self.symbol_with(
                    *span,
                    name,
                    IdeSymbolKind::Proc,
                    Some(&decl.name),
                    IdeVisibility::Private,
                );
            }
        }
    }

    fn symbol_with(
        &mut self,
        span: Span,
        name: &str,
        kind: IdeSymbolKind,
        owner: Option<&str>,
        visibility: IdeVisibility,
    ) {
        if let Some(name_span) = find_name_span(self.tokens, span, name) {
            self.out.push(IdeSymbol {
                name: name.to_owned(),
                kind,
                file_id: self.file_id,
                span: name_span,
                detail: symbol_detail(kind, name, self.source, span),
                module: self.module.map(str::to_owned),
                owner: owner.map(str::to_owned),
                visibility,
            });
        }
    }
}

fn find_name_span(tokens: &[(crate::lex::Token, Span)], within: Span, name: &str) -> Option<Span> {
    tokens.iter().find_map(|(token, span)| match token {
        crate::lex::Token::Name(token_name)
            if token_name == name && span.start >= within.start && span.end <= within.end =>
        {
            Some(*span)
        }
        _ => None,
    })
}

fn symbol_detail(kind: IdeSymbolKind, name: &str, source: &str, span: Span) -> String {
    let snippet = source.get(span.start..).map_or(String::new(), |rest| {
        rest.lines()
            .next()
            .unwrap_or_default()
            .chars()
            .take(120)
            .collect::<String>()
            .trim()
            .to_owned()
    });
    if snippet.is_empty() {
        format!("{} {}", kind.label(), name)
    } else {
        snippet
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_symbol(
        name: &str,
        kind: IdeSymbolKind,
        file_id: FileId,
        module: Option<&str>,
        owner: Option<&str>,
    ) -> IdeSymbol {
        IdeSymbol {
            name: name.to_owned(),
            kind,
            file_id,
            span: Span { start: 0, end: 0 },
            detail: format!("{} {name}", kind.label()),
            module: module.map(str::to_owned),
            owner: owner.map(str::to_owned),
            visibility: IdeVisibility::Private,
        }
    }

    fn symbol_names(symbols: Vec<&IdeSymbol>) -> Vec<&str> {
        symbols
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect()
    }

    fn owned_symbol_names(symbols: Vec<IdeSymbol>) -> Vec<String> {
        symbols.into_iter().map(|symbol| symbol.name).collect()
    }

    #[test]
    fn completion_context_detects_trigger_characters() {
        assert_eq!(completion_context("@Pen", 1), CompletionContext::AfterAt);
        assert_eq!(completion_context("order.", 6), CompletionContext::AfterDot);
        assert_eq!(
            completion_context("OrderStatus::", "OrderStatus::".len()),
            CompletionContext::AfterScope
        );
        assert_eq!(
            completion_context("entity Order", 6),
            CompletionContext::General
        );
    }

    #[test]
    fn cursor_context_classifies_representative_abide_positions() {
        assert_eq!(
            classify_abide_cursor("module Commerce", "module Commerce".len()),
            AbideCursorContext::ModuleDecl
        );
        assert_eq!(
            classify_abide_cursor("use Inventory", "use Inventory".len()),
            AbideCursorContext::UseDecl
        );
        assert_eq!(
            classify_abide_cursor("include \"inventory", "include \"inventory".len()),
            AbideCursorContext::IncludePath
        );
        assert_eq!(
            classify_abide_cursor("entity Ord", "entity Ord".len()),
            AbideCursorContext::TopLevel
        );
        assert_eq!(
            classify_abide_cursor("status == @", "status == @".len()),
            AbideCursorContext::AfterAt
        );
        assert_eq!(
            classify_abide_cursor("order.", "order.".len()),
            AbideCursorContext::AfterDot
        );
        assert_eq!(
            classify_abide_cursor("OrderStatus::", "OrderStatus::".len()),
            AbideCursorContext::AfterScope
        );
    }

    #[test]
    fn cursor_context_classifies_multiline_blocks_contracts_and_bodies() {
        let entity = "entity Order {\n  status: int\n  ";
        assert_eq!(
            classify_abide_cursor(entity, entity.len()),
            AbideCursorContext::EntityBody {
                name: Some("Order".to_owned())
            }
        );

        let system = "system Storefront {\n  command ";
        assert_eq!(
            classify_abide_cursor(system, system.len()),
            AbideCursorContext::SystemBody {
                name: Some("Storefront".to_owned())
            }
        );

        let interface = "interface PaymentProcessor {\n  command ";
        assert_eq!(
            classify_abide_cursor(interface, interface.len()),
            AbideCursorContext::InterfaceBody {
                name: Some("PaymentProcessor".to_owned())
            }
        );

        let program = "program Publishing {\n  proc ";
        assert_eq!(
            classify_abide_cursor(program, program.len()),
            AbideCursorContext::ProgramBody {
                name: Some("Publishing".to_owned())
            }
        );

        let fn_contract = "fn total(x: int): int\n  req";
        assert_eq!(
            classify_abide_cursor(fn_contract, fn_contract.len()),
            AbideCursorContext::FunctionContract
        );

        let fn_body = "fn total(x: int): int {\n  x";
        assert_eq!(
            classify_abide_cursor(fn_body, fn_body.len()),
            AbideCursorContext::FunctionBody {
                name: Some("total".to_owned())
            }
        );

        let action_contract = "entity Order {\n  action submit()\n    req";
        assert_eq!(
            classify_abide_cursor(action_contract, action_contract.len()),
            AbideCursorContext::ActionContract
        );

        let action_body = "entity Order {\n  action submit() {\n    status'";
        assert_eq!(
            classify_abide_cursor(action_body, action_body.len()),
            AbideCursorContext::ActionBody {
                name: Some("submit".to_owned())
            }
        );

        let command_contract = "system Storefront {\n  command checkout()\n    req";
        assert_eq!(
            classify_abide_cursor(command_contract, command_contract.len()),
            AbideCursorContext::CommandContract
        );

        let command_body = "system Storefront {\n  command checkout() {\n    true";
        assert_eq!(
            classify_abide_cursor(command_body, command_body.len()),
            AbideCursorContext::CommandBody {
                name: Some("checkout".to_owned())
            }
        );

        let proc_contract = "program Publishing {\n  proc release()\n    req";
        assert_eq!(
            classify_abide_cursor(proc_contract, proc_contract.len()),
            AbideCursorContext::ProcContract
        );

        let proc_body = "program Publishing {\n  proc release() {\n    submit";
        assert_eq!(
            classify_abide_cursor(proc_body, proc_body.len()),
            AbideCursorContext::ProcBody {
                name: Some("release".to_owned())
            }
        );
    }

    #[test]
    fn cursor_context_classifies_qa_commands_queries_loads_and_embedded_abide() {
        assert_eq!(
            classify_qa_cursor("ver", "ver".len()),
            QaCursorContext::Command
        );
        assert_eq!(
            classify_qa_cursor("ask ent", "ask ent".len()),
            QaCursorContext::Query
        );
        assert_eq!(
            classify_qa_cursor("load \"models", "load \"models".len()),
            QaCursorContext::LoadPath
        );
        assert_eq!(
            classify_qa_cursor("load \"models\" extra", "load \"models\" extra".len()),
            QaCursorContext::None
        );
        assert_eq!(
            classify_qa_cursor("ask entities extra", "ask entities extra".len()),
            QaCursorContext::None
        );

        let qa_source = "ask entities\nabide {\n  entity Ticket {\n    status: int\n  }\n}\n";
        assert_eq!(classify_qa_cursor(qa_source, 0), QaCursorContext::Command);
        assert_eq!(
            classify_qa_cursor(qa_source, qa_source.len()),
            QaCursorContext::Command
        );
        let embedded_offset = qa_source.find("status").expect("status offset");
        assert_eq!(
            classify_qa_cursor(qa_source, embedded_offset),
            QaCursorContext::EmbeddedAbide(AbideCursorContext::EntityBody {
                name: Some("Ticket".to_owned())
            })
        );
    }

    #[test]
    fn cursor_helpers_handle_utf8_boundaries_keywords_and_nested_blocks() {
        assert_eq!(clamp_to_char_boundary("éx", 1), 0);
        assert_eq!(clamp_to_char_boundary("aéz", 2), 1);
        assert!(!is_word_boundary('_'));
        assert!(!is_word_boundary('a'));
        assert!(is_word_boundary(' '));
        assert!(starts_with_keyword("module Commerce", "module"));
        assert!(!starts_with_keyword("module_name Commerce", "module"));
        assert!(!starts_with_keyword("moduleName Commerce", "module"));

        let opening = "entity Order {";
        let opening_brace = opening.find('{').expect("brace");
        assert_eq!(block_depth(opening, opening_brace), 0);
        assert_eq!(block_depth(opening, opening.len()), 1);

        let string_brace = "entity Order {\n  note: string = \"{\"";
        assert_eq!(block_depth(string_brace, string_brace.len()), 1);

        let escaped_quote_and_brace =
            "entity Order {\n  note: string = \"\\\" brace { still string\"\n}";
        assert_eq!(
            block_depth(escaped_quote_and_brace, escaped_quote_and_brace.len()),
            0
        );

        let non_decl_nested = "entity Order {\n  if ready {";
        assert_eq!(
            classify_abide_cursor(non_decl_nested, non_decl_nested.len()),
            AbideCursorContext::General
        );

        let non_decl_after_close = "entity Order {\n  action submit() { true }\n  if ready {";
        assert_eq!(
            classify_abide_cursor(non_decl_after_close, non_decl_after_close.len()),
            AbideCursorContext::General
        );

        let closed_nested = "entity Order {\n  action submit() { true }\n  status";
        assert_eq!(
            classify_abide_cursor(closed_nested, closed_nested.len()),
            AbideCursorContext::EntityBody {
                name: Some("Order".to_owned())
            }
        );
    }

    #[test]
    fn workspace_index_collects_top_level_and_member_symbols() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let root_id = workspace.set_file_source(
            "spec.ab",
            "enum Status = Pending | Done\nentity Order { status: Status action submit() { true } }\nsystem Billing { command charge() query ready() = true }",
        );

        let index = build_workspace_index(&mut workspace).expect("index");
        assert!(index
            .symbols_named("Status")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Type));
        assert!(index
            .symbols_named("Pending")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Variant));
        assert!(index
            .symbols_named("Order")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Entity));
        assert!(index
            .symbols_named("status")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Field));
        assert!(index
            .symbols_named("submit")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Action));
        assert!(index
            .symbols_named("charge")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Command));
        assert!(index
            .symbols_named("ready")
            .iter()
            .any(|s| s.kind == IdeSymbolKind::Query));
        assert!(identifier_at(&mut workspace, root_id, 6)
            .expect("identifier")
            .is_some());
    }

    #[test]
    fn workspace_index_collects_includes_interfaces_procs_programs_and_details() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        workspace.set_file_source(
            "spec.ab",
            "include \"shared.ab\"\n\
             interface PaymentProcessor {\n\
               command authorize(order_id: identity, amount: int) -> string\n\
             }\n\
             proc release(editorial: Editorial) {\n\
               submit = editorial.submit_pending()\n\
             }\n\
             program Publishing {\n\
               proc fulfill(billing: Billing) {\n\
                 charge = billing.charge()\n\
               }\n\
             }\n",
        );

        let index = build_workspace_index(&mut workspace).expect("index");

        assert_eq!(index.includes.len(), 1, "{:#?}", index.includes);
        assert_eq!(index.includes[0].path, "shared.ab");

        assert!(index
            .symbols_named("PaymentProcessor")
            .iter()
            .any(|symbol| symbol.kind == IdeSymbolKind::Interface));
        assert!(index.symbols_named("authorize").iter().any(|symbol| {
            symbol.kind == IdeSymbolKind::Command
                && symbol.owner.as_deref() == Some("PaymentProcessor")
        }));

        assert!(
            index
                .symbols_named("release")
                .iter()
                .any(|symbol| symbol.kind == IdeSymbolKind::Proc && symbol.owner.is_none()),
            "{index:#?}"
        );
        assert!(
            index
                .symbols_named("submit")
                .iter()
                .any(|symbol| symbol.kind == IdeSymbolKind::Proc && symbol.owner.is_none()),
            "{index:#?}"
        );

        assert!(index
            .symbols_named("Publishing")
            .iter()
            .any(|symbol| symbol.kind == IdeSymbolKind::Program));
        assert!(index.symbols_named("fulfill").iter().any(|symbol| {
            symbol.kind == IdeSymbolKind::Proc && symbol.owner.as_deref() == Some("Publishing")
        }));
        assert!(index.symbols_named("charge").iter().any(|symbol| {
            symbol.kind == IdeSymbolKind::Proc && symbol.owner.as_deref() == Some("fulfill")
        }));

        let detail = index
            .symbols_named("PaymentProcessor")
            .into_iter()
            .find(|symbol| symbol.kind == IdeSymbolKind::Interface)
            .map(|symbol| symbol.detail.as_str())
            .expect("interface symbol detail");
        assert_eq!(detail, "interface PaymentProcessor {");
    }

    #[test]
    fn workspace_index_skips_qa_sources() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        workspace.set_file_source(
            "query.qa",
            "load \"model.ab\"\nassert terminal Ticket.status\n",
        );

        let index = build_workspace_index(&mut workspace).expect("index");

        assert!(
            index
                .occurrences
                .iter()
                .all(|occurrence| occurrence.name != "load"),
            "QA source should not be lexed as Abide IDE input: {index:#?}"
        );
    }

    #[test]
    fn workspace_index_queries_modules_exports_imports_members_and_variants() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        workspace.set_file_source(
            "inventory.ab",
            "module Inventory\n\
             enum StockStatus = InStock | Backorder\n\
             entity StockItem { sku: int action reserve() { true } }\n\
             fn internal_discount(): int { 0 }\n",
        );
        let storefront_id = workspace.set_file_source(
            "storefront.ab",
            "module Storefront\n\
             use Inventory::*\n\
             use Inventory::StockItem as Item\n\
             entity Cart { item: Item }\n",
        );

        let index = build_workspace_index(&mut workspace).expect("index");

        let export_names = index
            .module_exports("Inventory")
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();
        assert!(export_names.contains(&"StockStatus"), "{export_names:#?}");
        assert!(export_names.contains(&"StockItem"), "{export_names:#?}");
        assert!(
            export_names.contains(&"internal_discount"),
            "current resolver treats all module declarations as importable: {export_names:#?}"
        );

        let member_names = index
            .members_by_owner("StockItem")
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();
        assert!(member_names.contains(&"sku"), "{member_names:#?}");
        assert!(member_names.contains(&"reserve"), "{member_names:#?}");

        let variant_names = index
            .enum_variants_by_type("StockStatus")
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();
        assert!(variant_names.contains(&"InStock"), "{variant_names:#?}");
        assert!(variant_names.contains(&"Backorder"), "{variant_names:#?}");

        let visible_names = index
            .visible_symbols(storefront_id, usize::MAX)
            .into_iter()
            .map(|symbol| symbol.name)
            .collect::<Vec<_>>();
        assert!(
            visible_names.contains(&"StockStatus".to_owned()),
            "{visible_names:#?}"
        );
        assert!(
            visible_names.contains(&"Item".to_owned()),
            "aliased import should be visible by alias: {visible_names:#?}"
        );
        assert!(
            visible_names.contains(&"Cart".to_owned()),
            "local private declarations should remain visible in their file: {visible_names:#?}"
        );
        assert!(
            visible_names.contains(&"internal_discount".to_owned()),
            "wildcard imports should mirror current resolver visibility: {visible_names:#?}"
        );
    }

    #[test]
    fn workspace_index_completion_symbols_are_context_filtered() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let file_id = workspace.set_file_source("spec.ab", "");
        let index = WorkspaceIndex {
            symbols: vec![
                test_symbol(
                    "Status",
                    IdeSymbolKind::Type,
                    file_id,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "InStock",
                    IdeSymbolKind::Variant,
                    file_id,
                    Some("Inventory"),
                    Some("Status"),
                ),
                test_symbol(
                    "Archived",
                    IdeSymbolKind::Variant,
                    file_id,
                    Some("Inventory"),
                    Some("OtherStatus"),
                ),
                test_symbol(
                    "status_code",
                    IdeSymbolKind::Field,
                    file_id,
                    Some("Inventory"),
                    Some("Status"),
                ),
                test_symbol(
                    "sku",
                    IdeSymbolKind::Field,
                    file_id,
                    Some("Inventory"),
                    Some("StockItem"),
                ),
                test_symbol(
                    "Inventory",
                    IdeSymbolKind::Module,
                    file_id,
                    Some("Inventory"),
                    None,
                ),
            ],
            ..WorkspaceIndex::default()
        };

        let general = index
            .completion_symbols(CompletionContext::General)
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(general, vec!["Status"]);

        let after_at = index
            .completion_symbols(CompletionContext::AfterAt)
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(after_at, vec!["InStock", "Archived"]);

        let after_dot = index
            .completion_symbols(CompletionContext::AfterDot)
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(after_dot, vec!["status_code", "sku"]);

        assert!(index
            .completion_symbols(CompletionContext::AfterScope)
            .is_empty());

        assert_eq!(
            symbol_names(index.enum_variants_by_type("Status")),
            vec!["InStock"]
        );
    }

    #[test]
    fn workspace_index_module_exports_exclude_members_modules_and_other_modules() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let file_id = workspace.set_file_source("spec.ab", "");
        let index = WorkspaceIndex {
            symbols: vec![
                test_symbol(
                    "Inventory",
                    IdeSymbolKind::Module,
                    file_id,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "StockItem",
                    IdeSymbolKind::Entity,
                    file_id,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "discount",
                    IdeSymbolKind::Function,
                    file_id,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "sku",
                    IdeSymbolKind::Field,
                    file_id,
                    Some("Inventory"),
                    Some("StockItem"),
                ),
                test_symbol(
                    "Cart",
                    IdeSymbolKind::Entity,
                    file_id,
                    Some("Storefront"),
                    None,
                ),
            ],
            ..WorkspaceIndex::default()
        };

        let exports = index
            .module_exports("Inventory")
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();

        assert_eq!(exports, vec!["discount", "StockItem"]);
    }

    #[test]
    fn workspace_index_members_by_owner_excludes_top_level_and_other_owners() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let file_id = workspace.set_file_source("spec.ab", "");
        let index = WorkspaceIndex {
            symbols: vec![
                test_symbol(
                    "sku",
                    IdeSymbolKind::Field,
                    file_id,
                    Some("Inventory"),
                    Some("StockItem"),
                ),
                test_symbol(
                    "reserve",
                    IdeSymbolKind::Action,
                    file_id,
                    Some("Inventory"),
                    Some("StockItem"),
                ),
                test_symbol(
                    "cart_sku",
                    IdeSymbolKind::Field,
                    file_id,
                    Some("Storefront"),
                    Some("Cart"),
                ),
                test_symbol(
                    "top_command",
                    IdeSymbolKind::Command,
                    file_id,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "not_a_member_kind",
                    IdeSymbolKind::Entity,
                    file_id,
                    Some("Inventory"),
                    Some("StockItem"),
                ),
            ],
            ..WorkspaceIndex::default()
        };

        let members = index
            .members_by_owner("StockItem")
            .into_iter()
            .map(|symbol| symbol.name.as_str())
            .collect::<Vec<_>>();

        assert_eq!(members, vec!["reserve", "sku"]);
    }

    #[test]
    fn workspace_index_visible_symbols_respects_module_owner_and_import_file() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let current_file = workspace.set_file_source("storefront.ab", "");
        let other_file = workspace.set_file_source("other.ab", "");
        let imported_file = workspace.set_file_source("inventory.ab", "");
        let index = WorkspaceIndex {
            symbols: vec![
                test_symbol(
                    "Cart",
                    IdeSymbolKind::Entity,
                    current_file,
                    Some("Storefront"),
                    None,
                ),
                test_symbol(
                    "cart_id",
                    IdeSymbolKind::Field,
                    current_file,
                    Some("Storefront"),
                    Some("Cart"),
                ),
                test_symbol(
                    "Storefront",
                    IdeSymbolKind::Module,
                    current_file,
                    Some("Storefront"),
                    None,
                ),
                test_symbol(
                    "OtherLocal",
                    IdeSymbolKind::Entity,
                    other_file,
                    Some("Other"),
                    None,
                ),
                test_symbol(
                    "StockItem",
                    IdeSymbolKind::Entity,
                    imported_file,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "StockAudit",
                    IdeSymbolKind::Entity,
                    imported_file,
                    Some("Inventory"),
                    None,
                ),
                test_symbol(
                    "Warehouse",
                    IdeSymbolKind::Entity,
                    imported_file,
                    Some("Warehouse"),
                    None,
                ),
            ],
            imports: vec![
                IdeImport {
                    file_id: current_file,
                    module: "Inventory".to_owned(),
                    kind: IdeImportKind::Single {
                        name: "StockItem".to_owned(),
                        alias: None,
                    },
                    span: Span { start: 0, end: 0 },
                },
                IdeImport {
                    file_id: other_file,
                    module: "Warehouse".to_owned(),
                    kind: IdeImportKind::Glob,
                    span: Span { start: 0, end: 0 },
                },
            ],
            file_modules: vec![
                (current_file, Some("Storefront".to_owned())),
                (other_file, Some("Other".to_owned())),
                (imported_file, Some("Inventory".to_owned())),
            ],
            ..WorkspaceIndex::default()
        };

        assert_eq!(
            owned_symbol_names(index.visible_symbols(current_file, usize::MAX)),
            vec!["Cart".to_owned(), "StockItem".to_owned()]
        );
    }

    #[test]
    fn identifier_lookup_and_dedup_helpers_use_exact_identity() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        let file_id = workspace.set_file_source("spec.ab", "alpha  beta");
        assert_eq!(
            identifier_at(&mut workspace, file_id, 0)
                .expect("identifier lookup")
                .map(|occurrence| occurrence.name),
            Some("alpha".to_owned())
        );
        assert_eq!(
            identifier_at(&mut workspace, file_id, 6).expect("identifier lookup"),
            None
        );
        assert_eq!(
            identifier_at(&mut workspace, file_id, 8)
                .expect("identifier lookup")
                .map(|occurrence| occurrence.name),
            Some("beta".to_owned())
        );

        let duplicate = test_symbol("alpha", IdeSymbolKind::Function, file_id, None, None);
        let same_name_different_span = IdeSymbol {
            span: Span { start: 2, end: 7 },
            ..duplicate.clone()
        };
        let mut symbols = vec![
            duplicate.clone(),
            duplicate.clone(),
            same_name_different_span.clone(),
        ];
        dedup_symbols(&mut symbols);
        assert_eq!(symbols.len(), 2, "{symbols:#?}");

        let mut cloned_symbols = vec![
            duplicate.clone(),
            duplicate,
            same_name_different_span.clone(),
            same_name_different_span,
        ];
        dedup_symbol_clones(&mut cloned_symbols);
        assert_eq!(cloned_symbols.len(), 2, "{cloned_symbols:#?}");

        let occurrence = IdeOccurrence {
            name: "alpha".to_owned(),
            file_id,
            span: Span { start: 0, end: 5 },
        };
        let mut occurrences = vec![occurrence.clone(), occurrence];
        dedup_occurrences(&mut occurrences);
        assert_eq!(occurrences.len(), 1, "{occurrences:#?}");
    }

    #[test]
    fn name_span_and_symbol_detail_are_scoped_to_decl_span() {
        let source = "fn first(): int { 0 }\nfn second(): int { 1 }\n";
        let tokens = driver::lex_source(source).expect("tokens");
        let second_decl_start = source.find("fn second").expect("second declaration");
        let second_start = source.find("second").expect("second fn");
        let second_end = source[second_start..]
            .find('\n')
            .map_or(source.len(), |offset| second_start + offset);
        let second_span = Span {
            start: second_decl_start,
            end: second_end,
        };

        let name_span = find_name_span(&tokens, second_span, "second").expect("second name span");
        assert_eq!(name_span.start, second_start);
        assert_eq!(name_span.end, second_start + "second".len());
        assert_eq!(
            symbol_detail(IdeSymbolKind::Function, "second", source, second_span),
            "fn second(): int { 1 }"
        );

        let interface_source =
            "interface PaymentProcessor {\n  command authorize(order_id: identity) -> string\n}\n";
        let interface_tokens = driver::lex_source(interface_source).expect("tokens");
        let command_start = interface_source
            .find("command authorize")
            .expect("command declaration");
        let command_end = interface_source[command_start..]
            .find('\n')
            .map_or(interface_source.len(), |offset| command_start + offset);
        let command_span = Span {
            start: command_start,
            end: command_end,
        };
        let authorize_start = interface_source.find("authorize").expect("authorize name");
        let authorize_span =
            find_name_span(&interface_tokens, command_span, "authorize").expect("authorize span");
        assert_eq!(authorize_span.start, authorize_start);
        assert_eq!(authorize_span.end, authorize_start + "authorize".len());

        let identity_start = interface_source.find("identity").expect("identity name");
        let identity_span =
            find_name_span(&interface_tokens, command_span, "identity").expect("identity span");
        assert_eq!(identity_span.start, identity_start);
        assert_eq!(identity_span.end, identity_start + "identity".len());
    }

    #[test]
    fn workspace_index_queries_module_qualified_definitions_and_references() {
        let mut workspace = CompilerWorkspace::with_root_dir("/tmp");
        workspace.set_file_source(
            "inventory.ab",
            "module Inventory\n\
             entity StockItem { sku: int }\n",
        );
        workspace.set_file_source(
            "storefront.ab",
            "module Storefront\n\
             use Inventory::StockItem\n\
             entity Cart { item: StockItem }\n",
        );

        let index = build_workspace_index(&mut workspace).expect("index");

        let definitions = index.symbols_in_module("Inventory", "StockItem");
        assert_eq!(definitions.len(), 1, "{definitions:#?}");
        assert_eq!(definitions[0].kind, IdeSymbolKind::Entity);

        let references = index.references_named("StockItem");
        assert!(
            references.len() >= 3,
            "expected declaration, import, and type-use references: {references:#?}"
        );
        assert!(references
            .iter()
            .all(|occurrence| occurrence.name == "StockItem"));
    }
}
