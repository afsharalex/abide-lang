use std::collections::BTreeSet;

use crate::ast::{
    EntityItem, InterfaceItem, ProcItem, Program, SystemItem, TopDecl, TypeVariant, VerifyDecl,
};
use crate::driver;
use crate::span::Span;
use crate::workspace::{CompilerWorkspace, FileId};

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
    Step,
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
            Self::Step => "step",
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
            Self::Field | Self::Action | Self::Derived | Self::Invariant | Self::Step => 7,
            Self::Const => 8,
            Self::Prop | Self::Verify | Self::Theorem | Self::Lemma | Self::Scene | Self::Axiom => {
                9
            }
            Self::Variant => 9,
            Self::Module => 10,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionContext {
    General,
    AfterAt,
    AfterDot,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdeSymbol {
    pub name: String,
    pub kind: IdeSymbolKind,
    pub file_id: FileId,
    pub span: Span,
    pub detail: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdeOccurrence {
    pub name: String,
    pub file_id: FileId,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct WorkspaceIndex {
    pub symbols: Vec<IdeSymbol>,
    pub occurrences: Vec<IdeOccurrence>,
}

impl WorkspaceIndex {
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

pub fn build_workspace_index(workspace: &mut CompilerWorkspace) -> miette::Result<WorkspaceIndex> {
    let mut index = WorkspaceIndex::default();
    for (file_id, _) in workspace.known_files() {
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
    for decl in &program.decls {
        match decl {
            TopDecl::Module(module) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                module.span,
                &module.name,
                IdeSymbolKind::Module,
            ),
            TopDecl::Const(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Const,
            ),
            TopDecl::Fn(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Function,
            ),
            TopDecl::Type(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Type,
                );
                for variant in &decl.variants {
                    match variant {
                        TypeVariant::Simple { name, span }
                        | TypeVariant::Tuple { name, span, .. }
                        | TypeVariant::Record { name, span, .. }
                        | TypeVariant::Param { name, span, .. } => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                *span,
                                name,
                                IdeSymbolKind::Variant,
                            );
                        }
                    }
                }
            }
            TopDecl::Record(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Record,
                );
                for field in &decl.fields {
                    push_symbol(
                        out,
                        file_id,
                        source,
                        tokens,
                        field.span,
                        &field.name,
                        IdeSymbolKind::Field,
                    );
                }
            }
            TopDecl::Alias(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Alias,
            ),
            TopDecl::Newtype(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Newtype,
            ),
            TopDecl::Entity(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Entity,
                );
                for item in &decl.items {
                    match item {
                        EntityItem::Field(field) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                field.span,
                                &field.name,
                                IdeSymbolKind::Field,
                            );
                        }
                        EntityItem::Action(action) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                action.span,
                                &action.name,
                                IdeSymbolKind::Action,
                            );
                        }
                        EntityItem::Derived(derived) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                derived.span,
                                &derived.name,
                                IdeSymbolKind::Derived,
                            );
                        }
                        EntityItem::Invariant(invariant) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                invariant.span,
                                &invariant.name,
                                IdeSymbolKind::Invariant,
                            );
                        }
                        EntityItem::Fsm(fsm) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                fsm.span,
                                &fsm.field,
                                IdeSymbolKind::Invariant,
                            );
                        }
                        EntityItem::Error(_) => {}
                    }
                }
            }
            TopDecl::Interface(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Interface,
                );
                for item in &decl.items {
                    match item {
                        InterfaceItem::Command(command) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                command.span,
                                &command.name,
                                IdeSymbolKind::Command,
                            );
                        }
                        InterfaceItem::QuerySig(query) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                query.span,
                                &query.name,
                                IdeSymbolKind::Query,
                            );
                        }
                        InterfaceItem::Error(_) => {}
                    }
                }
            }
            TopDecl::Extern(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::System,
                );
            }
            TopDecl::System(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::System,
                );
                for item in &decl.items {
                    match item {
                        SystemItem::Field(field) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                field.span,
                                &field.name,
                                IdeSymbolKind::Field,
                            );
                        }
                        SystemItem::Dep(_) => {}
                        SystemItem::Command(command) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                command.span,
                                &command.name,
                                IdeSymbolKind::Command,
                            );
                        }
                        SystemItem::Step(step) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                step.span,
                                &step.name,
                                IdeSymbolKind::Step,
                            );
                        }
                        SystemItem::Query(query) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                query.span,
                                &query.name,
                                IdeSymbolKind::Query,
                            );
                        }
                        SystemItem::Pred(pred) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                pred.span,
                                &pred.name,
                                IdeSymbolKind::Pred,
                            );
                        }
                        SystemItem::Derived(derived) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                derived.span,
                                &derived.name,
                                IdeSymbolKind::Derived,
                            );
                        }
                        SystemItem::Invariant(invariant) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                invariant.span,
                                &invariant.name,
                                IdeSymbolKind::Invariant,
                            );
                        }
                        SystemItem::Fsm(fsm) => {
                            push_symbol(
                                out,
                                file_id,
                                source,
                                tokens,
                                fsm.span,
                                &fsm.field,
                                IdeSymbolKind::Invariant,
                            );
                        }
                        SystemItem::Error(_) => {}
                    }
                }
            }
            TopDecl::Proc(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Proc,
                );
                for proc_item in &decl.items {
                    if let ProcItem::Node { name, span, .. } = proc_item {
                        push_symbol(
                            out,
                            file_id,
                            source,
                            tokens,
                            *span,
                            name,
                            IdeSymbolKind::Proc,
                        );
                    }
                }
            }
            TopDecl::Program(decl) => {
                push_symbol(
                    out,
                    file_id,
                    source,
                    tokens,
                    decl.span,
                    &decl.name,
                    IdeSymbolKind::Program,
                );
                for item in &decl.items {
                    if let crate::ast::ProgramItem::Proc(proc_decl) = item {
                        push_symbol(
                            out,
                            file_id,
                            source,
                            tokens,
                            proc_decl.span,
                            &proc_decl.name,
                            IdeSymbolKind::Proc,
                        );
                        for proc_item in &proc_decl.items {
                            if let ProcItem::Node { name, span, .. } = proc_item {
                                push_symbol(
                                    out,
                                    file_id,
                                    source,
                                    tokens,
                                    *span,
                                    name,
                                    IdeSymbolKind::Proc,
                                );
                            }
                        }
                    }
                }
            }
            TopDecl::Pred(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Pred,
            ),
            TopDecl::Prop(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Prop,
            ),
            TopDecl::Verify(VerifyDecl { name, span, .. }) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                *span,
                name,
                IdeSymbolKind::Verify,
            ),
            TopDecl::Theorem(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Theorem,
            ),
            TopDecl::Lemma(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Lemma,
            ),
            TopDecl::Scene(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Scene,
            ),
            TopDecl::Axiom(decl) => push_symbol(
                out,
                file_id,
                source,
                tokens,
                decl.span,
                &decl.name,
                IdeSymbolKind::Axiom,
            ),
            TopDecl::Include(_) | TopDecl::Use(_) | TopDecl::Under(_) | TopDecl::Error(_) => {}
        }
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
}
