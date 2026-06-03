//! IDE primitives shared by `abide-lsp`, `abide explain`, and the
//! REPL. Provides a flattened symbol index over a workspace plus
//! offset-keyed lookup (identifier-at, completion-context) routines.

use std::collections::BTreeSet;
use std::path::Path;

use crate::ast::{
    EntityItem, InterfaceItem, ProcItem, Program, SystemItem, TopDecl, TypeVariant, VerifyDecl,
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

/// Cursor position context for completion. Determined by looking at
/// the character just before the cursor: `@` opens enum-constructor
/// completion, `.` opens field/member completion, anything else falls
/// through to general completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionContext {
    /// No special trigger character — show all keywords and top-level
    /// symbols.
    General,
    /// Cursor immediately after `@` — show enum constructors.
    AfterAt,
    /// Cursor immediately after `.` — show field/member names.
    AfterDot,
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

/// Flat per-workspace index of symbols and their textual occurrences.
/// Rebuilt eagerly each request — there is no incremental layer
/// (latency is dominated by parsing, not indexing).
#[derive(Debug, Clone, Default)]
pub struct WorkspaceIndex {
    pub symbols: Vec<IdeSymbol>,
    pub occurrences: Vec<IdeOccurrence>,
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
            })
            .collect()
    }
}

/// Classifies the trigger character immediately before `offset` in
/// `source`, returning the relevant [`CompletionContext`].
#[must_use]
pub fn completion_context(source: &str, offset: usize) -> CompletionContext {
    let prefix = &source[..offset.min(source.len())];
    let trimmed = prefix.trim_end_matches(char::is_whitespace);
    match trimmed.chars().last() {
        Some('@') => CompletionContext::AfterAt,
        Some('.') => CompletionContext::AfterDot,
        _ => CompletionContext::General,
    }
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
        index
            .occurrences
            .extend(name_occurrences_from_tokens(file_id, &tokens));
        collect_program_symbols(
            &mut index.symbols,
            file_id,
            source.as_ref(),
            &parse.program,
            &tokens,
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
) {
    SymbolCollector {
        out,
        file_id,
        source,
        tokens,
    }
    .collect_program(program);
}

struct SymbolCollector<'a> {
    out: &'a mut Vec<IdeSymbol>,
    file_id: FileId,
    source: &'a str,
    tokens: &'a [(crate::lex::Token, Span)],
}

impl SymbolCollector<'_> {
    fn collect_program(&mut self, program: &Program) {
        for decl in &program.decls {
            self.collect_top_decl(decl);
        }
    }

    fn collect_top_decl(&mut self, decl: &TopDecl) {
        match decl {
            TopDecl::Module(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Module),
            TopDecl::Const(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Const),
            TopDecl::Fn(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Function),
            TopDecl::Type(decl) => self.collect_type_decl(decl),
            TopDecl::Record(decl) => {
                self.symbol(decl.span, &decl.name, IdeSymbolKind::Record);
                for field in &decl.fields {
                    self.symbol(field.span, &field.name, IdeSymbolKind::Field);
                }
            }
            TopDecl::Alias(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Alias),
            TopDecl::Newtype(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Newtype),
            TopDecl::Entity(decl) => self.collect_entity_decl(decl),
            TopDecl::Interface(decl) => self.collect_interface_decl(decl),
            TopDecl::Extern(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::System),
            TopDecl::System(decl) => self.collect_system_decl(decl),
            TopDecl::Proc(decl) => self.collect_proc_decl(decl),
            TopDecl::Program(decl) => self.collect_program_decl(decl),
            TopDecl::Pred(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Pred),
            TopDecl::Prop(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Prop),
            TopDecl::Verify(VerifyDecl { name, span, .. }) => {
                self.symbol(*span, name, IdeSymbolKind::Verify);
            }
            TopDecl::Theorem(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Theorem),
            TopDecl::Lemma(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Lemma),
            TopDecl::Scene(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Scene),
            TopDecl::Axiom(decl) => self.symbol(decl.span, &decl.name, IdeSymbolKind::Axiom),
            TopDecl::Include(_) | TopDecl::Use(_) | TopDecl::Under(_) | TopDecl::Error(_) => {}
        }
    }

    fn collect_type_decl(&mut self, decl: &crate::ast::TypeDecl) {
        self.symbol(decl.span, &decl.name, IdeSymbolKind::Type);
        for variant in &decl.variants {
            match variant {
                TypeVariant::Simple { name, span }
                | TypeVariant::Tuple { name, span, .. }
                | TypeVariant::Record { name, span, .. }
                | TypeVariant::Param { name, span, .. } => {
                    self.symbol(*span, name, IdeSymbolKind::Variant);
                }
            }
        }
    }

    fn collect_entity_decl(&mut self, decl: &crate::ast::EntityDecl) {
        self.symbol(decl.span, &decl.name, IdeSymbolKind::Entity);
        for item in &decl.items {
            match item {
                EntityItem::Field(field) => {
                    self.symbol(field.span, &field.name, IdeSymbolKind::Field);
                }
                EntityItem::Action(action) => {
                    self.symbol(action.span, &action.name, IdeSymbolKind::Action);
                }
                EntityItem::Derived(derived) => {
                    self.symbol(derived.span, &derived.name, IdeSymbolKind::Derived);
                }
                EntityItem::Invariant(invariant) => {
                    self.symbol(invariant.span, &invariant.name, IdeSymbolKind::Invariant);
                }
                EntityItem::Fsm(fsm) => self.symbol(fsm.span, &fsm.field, IdeSymbolKind::Invariant),
                EntityItem::Error(_) => {}
            }
        }
    }

    fn collect_interface_decl(&mut self, decl: &crate::ast::InterfaceDecl) {
        self.symbol(decl.span, &decl.name, IdeSymbolKind::Interface);
        for item in &decl.items {
            match item {
                InterfaceItem::Command(command) => {
                    self.symbol(command.span, &command.name, IdeSymbolKind::Command);
                }
                InterfaceItem::QuerySig(query) => {
                    self.symbol(query.span, &query.name, IdeSymbolKind::Query);
                }
                InterfaceItem::Error(_) => {}
            }
        }
    }

    fn collect_system_decl(&mut self, decl: &crate::ast::SystemDecl) {
        self.symbol(decl.span, &decl.name, IdeSymbolKind::System);
        for item in &decl.items {
            match item {
                SystemItem::Field(field) => {
                    self.symbol(field.span, &field.name, IdeSymbolKind::Field);
                }
                SystemItem::Dep(_) => {}
                SystemItem::Command(command) => {
                    self.symbol(command.span, &command.name, IdeSymbolKind::Command);
                }
                SystemItem::Action(action) => {
                    self.symbol(action.span, &action.name, IdeSymbolKind::Action);
                }
                SystemItem::Query(query) => {
                    self.symbol(query.span, &query.name, IdeSymbolKind::Query);
                }
                SystemItem::Pred(pred) => self.symbol(pred.span, &pred.name, IdeSymbolKind::Pred),
                SystemItem::Derived(derived) => {
                    self.symbol(derived.span, &derived.name, IdeSymbolKind::Derived);
                }
                SystemItem::Invariant(invariant) => {
                    self.symbol(invariant.span, &invariant.name, IdeSymbolKind::Invariant);
                }
                SystemItem::Fsm(fsm) => self.symbol(fsm.span, &fsm.field, IdeSymbolKind::Invariant),
                SystemItem::Error(_) => {}
            }
        }
    }

    fn collect_proc_decl(&mut self, decl: &crate::ast::ProcDecl) {
        self.symbol(decl.span, &decl.name, IdeSymbolKind::Proc);
        self.collect_proc_nodes(&decl.items);
    }

    fn collect_proc_nodes(&mut self, items: &[ProcItem]) {
        for proc_item in items {
            if let ProcItem::Node { name, span, .. } = proc_item {
                self.symbol(*span, name, IdeSymbolKind::Proc);
            }
        }
    }

    fn collect_program_decl(&mut self, decl: &crate::ast::ProgramDecl) {
        self.symbol(decl.span, &decl.name, IdeSymbolKind::Program);
        for item in &decl.items {
            if let crate::ast::ProgramItem::Proc(proc_decl) = item {
                self.collect_proc_decl(proc_decl);
            }
        }
    }

    fn symbol(&mut self, span: Span, name: &str, kind: IdeSymbolKind) {
        push_symbol(
            self.out,
            self.file_id,
            self.source,
            self.tokens,
            span,
            name,
            kind,
        );
    }
}

fn push_symbol(
    out: &mut Vec<IdeSymbol>,
    file_id: FileId,
    source: &str,
    tokens: &[(crate::lex::Token, Span)],
    span: Span,
    name: &str,
    kind: IdeSymbolKind,
) {
    if let Some(name_span) = find_name_span(tokens, span, name) {
        out.push(IdeSymbol {
            name: name.to_owned(),
            kind,
            file_id,
            span: name_span,
            detail: symbol_detail(kind, name, source, span),
        });
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

    #[test]
    fn completion_context_detects_trigger_characters() {
        assert_eq!(completion_context("@Pen", 1), CompletionContext::AfterAt);
        assert_eq!(completion_context("order.", 6), CompletionContext::AfterDot);
        assert_eq!(
            completion_context("entity Order", 6),
            CompletionContext::General
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
}
