//! Static validation for QA scripts.
//!
//! This layer is intentionally lighter than the QA runner: it resolves
//! `load` statements, builds the structural [`FlowModel`], and checks
//! query references against that model. It does not execute assertions,
//! verification, simulation, exploration, or artifact commands.

use std::path::{Path, PathBuf};

use abide_syntax::diagnostic::Diagnostic;
use abide_syntax::span::Span;

use super::ast::{QAStatement, Query, TemporalTarget};
use super::extract;
use super::model::FlowModel;
use super::parse::{embedded_abide_blocks, parse_qa, parse_statement, QAEmbeddedAbideBlock};
use crate::{elab, ir, loader};

pub const QA_SEMANTIC_MISSING_LOAD: &str = "abide::qa::semantic::missing_load";
pub const QA_SEMANTIC_INVALID_LOAD: &str = "abide::qa::semantic::invalid_load";
pub const QA_SEMANTIC_UNKNOWN_REFERENCE: &str = "abide::qa::semantic::unknown_reference";

#[derive(Debug, Clone)]
struct LocatedStatement {
    statement: QAStatement,
    tokens: Vec<LocatedToken>,
}

#[derive(Debug, Clone)]
struct LocatedToken {
    text: String,
    span: Span,
}

#[derive(Debug, Clone)]
enum BaseEnv {
    NoLoads,
    Loaded(Box<elab::env::Env>),
    Invalid,
}

/// Validate one QA script source as it would be seen from `script_path`.
#[must_use]
pub fn validate_qa_source(script_path: &Path, source: &str) -> Vec<Diagnostic> {
    let script_file = script_path.display().to_string();
    let statements = match parse_qa(source) {
        Ok(_) => located_statements(source),
        Err(error) => return vec![error.to_diagnostic().in_file(script_file)],
    };

    let mut diagnostics = Vec::new();
    let mut load_paths = Vec::new();
    let mut load_spans = Vec::new();
    let script_dir = script_path.parent().unwrap_or_else(|| Path::new("."));

    for located in &statements {
        let QAStatement::Load(path) = &located.statement else {
            continue;
        };
        let Some(span) = load_path_span(located) else {
            continue;
        };
        let resolved = resolve_load_path(script_dir, path);
        load_spans.push(span);
        if !resolved.exists() {
            diagnostics.push(
                Diagnostic::error(format!("QA load target `{path}` does not exist"))
                    .with_code(QA_SEMANTIC_MISSING_LOAD)
                    .with_span(span)
                    .in_file(script_file.clone()),
            );
        } else if resolved.is_dir() {
            collect_abide_files(&resolved, &mut load_paths);
        } else {
            load_paths.push(resolved);
        }
    }

    if !diagnostics.is_empty() || load_paths.is_empty() {
        return diagnostics;
    }

    let first_load_span = load_spans.first().copied();
    let model = match build_flow_model_from_paths(&load_paths) {
        Ok(model) => model,
        Err(messages) => {
            let span = first_load_span.unwrap_or(Span { start: 0, end: 1 });
            diagnostics.extend(messages.into_iter().map(|message| {
                Diagnostic::error(message)
                    .with_code(QA_SEMANTIC_INVALID_LOAD)
                    .with_span(span)
                    .in_file(script_file.clone())
            }));
            return diagnostics;
        }
    };

    for located in &statements {
        let Some(query) = statement_query(&located.statement) else {
            continue;
        };
        validate_query_reference(query, &model, located, &script_file, &mut diagnostics);
    }

    diagnostics
}

/// Validate embedded `abide { ... }` blocks as QA overlays against loaded specs.
#[must_use]
pub fn validate_embedded_abide_blocks(script_path: &Path, source: &str) -> Vec<Diagnostic> {
    let Ok(blocks) = embedded_abide_blocks(source) else {
        return Vec::new();
    };
    if blocks.is_empty() {
        return Vec::new();
    }

    let script_file = script_path.display().to_string();
    let base_env = base_env_for_qa_source(script_path, source);
    if matches!(base_env, BaseEnv::Invalid) {
        return Vec::new();
    }

    blocks
        .iter()
        .flat_map(|block| validate_embedded_abide_block(block, &base_env, &script_file))
        .collect()
}

fn base_env_for_qa_source(script_path: &Path, source: &str) -> BaseEnv {
    let Ok(_) = parse_qa(source) else {
        return BaseEnv::Invalid;
    };
    let script_dir = script_path.parent().unwrap_or_else(|| Path::new("."));
    let mut load_paths = Vec::new();

    for located in located_statements(source) {
        let QAStatement::Load(path) = located.statement else {
            continue;
        };
        let resolved = resolve_load_path(script_dir, &path);
        if !resolved.exists() {
            return BaseEnv::Invalid;
        }
        if resolved.is_dir() {
            collect_abide_files(&resolved, &mut load_paths);
        } else {
            load_paths.push(resolved);
        }
    }

    if load_paths.is_empty() {
        return BaseEnv::NoLoads;
    }

    match build_base_env_from_paths(&load_paths) {
        Ok(env) => BaseEnv::Loaded(Box::new(env)),
        Err(()) => BaseEnv::Invalid,
    }
}

fn validate_embedded_abide_block(
    block: &QAEmbeddedAbideBlock,
    base_env: &BaseEnv,
    script_file: &str,
) -> Vec<Diagnostic> {
    let parsed = match crate::parse::parse_string_recovering(&block.body) {
        Ok(parsed) => parsed,
        Err(errors) => {
            return errors
                .into_iter()
                .map(|error| map_embedded_diagnostic(error.to_diagnostic(), block, script_file))
                .collect();
        }
    };

    if !parsed.errors.is_empty() {
        return parsed
            .errors
            .into_iter()
            .map(|error| map_embedded_diagnostic(error.to_diagnostic(), block, script_file))
            .collect();
    }

    let overlay = elab::collect::collect(&parsed.program);
    let mut env = match base_env {
        BaseEnv::NoLoads => overlay,
        BaseEnv::Loaded(env) => {
            let mut merged = (**env).clone();
            super::runner::merge_env_overlay(&mut merged, &overlay);
            merged
        }
        BaseEnv::Invalid => return Vec::new(),
    };
    if matches!(base_env, BaseEnv::NoLoads) {
        env = elab::collect::collect(&parsed.program);
    }

    let (result, elab_errors) = elab::elaborate_env(env);
    let mut diagnostics = elab_errors
        .into_iter()
        .filter(|error| !matches!(error.severity, elab::error::Severity::Warning))
        .map(|error| map_embedded_diagnostic(error.to_diagnostic(), block, script_file))
        .collect::<Vec<_>>();

    let (_ir_program, lower_diagnostics) = ir::lower(&result);
    diagnostics.extend(
        lower_diagnostics
            .diagnostics
            .into_iter()
            .filter(|diagnostic| diagnostic.severity.is_error())
            .map(|diagnostic| map_embedded_diagnostic(diagnostic, block, script_file)),
    );
    diagnostics
}

fn build_base_env_from_paths(paths: &[PathBuf]) -> Result<elab::env::Env, ()> {
    let (mut env, load_errors, _all_paths) = loader::load_files(paths);
    if !load_errors.is_empty() || !env.include_load_errors.is_empty() {
        return Err(());
    }
    if paths.len() > 1 {
        env.module_name = None;
    }

    let (_result, elab_errors) = elab::elaborate_env(env.clone());
    if elab_errors
        .iter()
        .any(|error| !matches!(error.severity, elab::error::Severity::Warning))
    {
        return Err(());
    }
    Ok(env)
}

fn map_embedded_diagnostic(
    mut diagnostic: Diagnostic,
    block: &QAEmbeddedAbideBlock,
    script_file: &str,
) -> Diagnostic {
    diagnostic.file = Some(script_file.to_owned());
    diagnostic.span = Some(diagnostic.span.map_or(
        Span {
            start: block.body_span.start,
            end: block.body_span.start.saturating_add(1),
        },
        |span| offset_span(span, block.body_span.start),
    ));
    diagnostic.related = diagnostic
        .related
        .into_iter()
        .map(|mut related| {
            related.file = Some(script_file.to_owned());
            related.span = related
                .span
                .map(|span| offset_span(span, block.body_span.start));
            related
        })
        .collect();
    diagnostic
}

fn offset_span(span: Span, base: usize) -> Span {
    Span {
        start: base + span.start,
        end: base + span.end,
    }
}

fn located_statements(source: &str) -> Vec<LocatedStatement> {
    let mut statements = Vec::new();
    let mut line_start = 0usize;
    let mut abide_depth = 0i32;

    for (line_index, line) in source.lines().enumerate() {
        let line_no = line_index + 1;
        let trimmed = line.trim();
        let trimmed_start = line.find(trimmed).unwrap_or(0);
        let trimmed_offset = line_start + trimmed_start;

        if abide_depth > 0 {
            update_brace_depth(trimmed, &mut abide_depth);
            line_start += line.len() + 1;
            continue;
        }

        if trimmed.is_empty() || trimmed.starts_with("//") {
            line_start += line.len() + 1;
            continue;
        }

        if trimmed.starts_with("abide") && trimmed.contains('{') {
            abide_depth = 1;
            let after_brace = trimmed.find('{').map_or("", |index| &trimmed[index + 1..]);
            update_brace_depth(after_brace, &mut abide_depth);
            line_start += line.len() + 1;
            continue;
        }

        if let Ok(statement) = parse_statement(trimmed, line_no) {
            statements.push(LocatedStatement {
                statement,
                tokens: scan_tokens(trimmed, trimmed_offset),
            });
        }

        line_start += line.len() + 1;
    }

    statements
}

fn update_brace_depth(text: &str, depth: &mut i32) {
    for ch in text.chars() {
        match ch {
            '{' => *depth += 1,
            '}' => *depth -= 1,
            _ => {}
        }
    }
}

fn scan_tokens(line: &str, line_start: usize) -> Vec<LocatedToken> {
    let mut tokens = Vec::new();
    let mut token_start = None;

    for (offset, ch) in line.char_indices() {
        if ch.is_whitespace() {
            if let Some(start) = token_start.take() {
                tokens.push(token_from_slice(line, line_start, start, offset));
            }
        } else if token_start.is_none() {
            token_start = Some(offset);
        }
    }

    if let Some(start) = token_start {
        tokens.push(token_from_slice(line, line_start, start, line.len()));
    }

    tokens
}

fn token_from_slice(line: &str, line_start: usize, start: usize, end: usize) -> LocatedToken {
    let raw = &line[start..end];
    let (text, span) = if raw.len() >= 2 && raw.starts_with('"') && raw.ends_with('"') {
        (
            raw[1..raw.len() - 1].to_owned(),
            Span {
                start: line_start + start + 1,
                end: line_start + end - 1,
            },
        )
    } else {
        (
            raw.to_owned(),
            Span {
                start: line_start + start,
                end: line_start + end,
            },
        )
    };
    LocatedToken { text, span }
}

fn load_path_span(statement: &LocatedStatement) -> Option<Span> {
    statement.tokens.get(1).map(|token| token.span)
}

fn resolve_load_path(script_dir: &Path, path: &str) -> PathBuf {
    let path = Path::new(path);
    if path.is_absolute() {
        path.to_owned()
    } else {
        script_dir.join(path)
    }
}

fn collect_abide_files(dir: &Path, paths: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(entries) => entries
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .collect(),
        Err(_) => return,
    };
    entries.sort();
    for path in entries {
        if matches!(
            path.extension().and_then(|extension| extension.to_str()),
            Some("ab" | "abi" | "abp")
        ) {
            paths.push(path);
        } else if path.is_dir() {
            collect_abide_files(&path, paths);
        }
    }
}

fn build_flow_model_from_paths(paths: &[PathBuf]) -> Result<FlowModel, Vec<String>> {
    let (mut env, load_errors, _all_paths) = loader::load_files(paths);
    if !load_errors.is_empty() {
        return Err(load_errors
            .iter()
            .map(|error| format!("error: {error}"))
            .collect());
    }
    if !env.include_load_errors.is_empty() {
        return Err(env
            .include_load_errors
            .iter()
            .map(|error| format!("error: {error}"))
            .collect());
    }
    if paths.len() > 1 {
        env.module_name = None;
    }

    let (result, elab_errors) = elab::elaborate_env(env);
    let errors = elab_errors
        .iter()
        .filter(|error| !matches!(error.severity, elab::error::Severity::Warning))
        .map(|error| format!("error: {error}"))
        .collect::<Vec<_>>();
    if !errors.is_empty() {
        return Err(errors);
    }

    let (ir_program, lower_diagnostics) = ir::lower(&result);
    if lower_diagnostics.has_errors() {
        return Err(lower_diagnostics
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.is_error())
            .map(std::string::ToString::to_string)
            .collect());
    }

    Ok(extract::extract(&ir_program))
}

fn statement_query(statement: &QAStatement) -> Option<&Query> {
    match statement {
        QAStatement::Ask(query) | QAStatement::Explain(query) | QAStatement::Assert(query) => {
            Some(query)
        }
        _ => None,
    }
}

fn validate_query_reference(
    query: &Query,
    model: &FlowModel,
    located: &LocatedStatement,
    script_file: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Some((reference, valid)) = query_reference_validation(query, model) {
        if !valid {
            let span = reference_span(located, &reference).unwrap_or(Span { start: 0, end: 1 });
            diagnostics.push(
                Diagnostic::error(format!("unknown QA reference `{reference}`"))
                    .with_code(QA_SEMANTIC_UNKNOWN_REFERENCE)
                    .with_span(span)
                    .in_file(script_file.to_owned()),
            );
        }
    }
}

fn query_reference_validation(query: &Query, model: &FlowModel) -> Option<(String, bool)> {
    match query {
        Query::Reachable { entity, field, .. }
        | Query::Path { entity, field, .. }
        | Query::Terminal { entity, field }
        | Query::Initial { entity, field }
        | Query::Cycles { entity, field }
        | Query::Transitions { entity, field, .. }
        | Query::Updates { entity, field, .. }
        | Query::Events { entity, field }
        | Query::MatchCoverage { entity, field } => {
            let reference = format!("{entity}.{field}");
            Some((
                reference,
                model
                    .field_graph_meta
                    .contains_key(&(entity.clone(), field.clone())),
            ))
        }
        Query::Invariants { entity } | Query::Fsms { entity } => {
            Some((entity.clone(), model_has_owner(model, entity)))
        }
        Query::Contracts { entity, action } => {
            let reference = format!("{entity}.{action}");
            Some((
                reference,
                model
                    .action_contracts
                    .contains_key(&(entity.clone(), action.clone())),
            ))
        }
        Query::FsmTransitions { entity, field } | Query::FsmTerminalStates { entity, field } => {
            let reference = format!("{entity}::{field}");
            Some((
                reference,
                model
                    .fsm_decls
                    .contains_key(&(entity.clone(), field.clone())),
            ))
        }
        Query::CrossCalls { system } | Query::Deadlock { system } => {
            Some((system.clone(), model.systems.contains_key(system)))
        }
        Query::Not(inner) => query_reference_validation(inner, model),
        Query::Temporal { target, .. } => target
            .as_ref()
            .map(|target| temporal_target_reference_validation(target, model)),
        Query::Entities | Query::Systems | Query::Types | Query::Block { .. } => None,
    }
}

fn temporal_target_reference_validation(
    target: &TemporalTarget,
    model: &FlowModel,
) -> (String, bool) {
    if let Some(field) = &target.field {
        let reference = format!("{}.{}", target.owner, field);
        (
            reference,
            model
                .field_graph_meta
                .contains_key(&(target.owner.clone(), field.clone())),
        )
    } else {
        (target.owner.clone(), model_has_owner(model, &target.owner))
    }
}

fn model_has_owner(model: &FlowModel, owner: &str) -> bool {
    model.entity_names.iter().any(|entity| entity == owner) || model.systems.contains_key(owner)
}

fn reference_span(statement: &LocatedStatement, reference: &str) -> Option<Span> {
    statement
        .tokens
        .iter()
        .find(|token| token.text == reference)
        .map(|token| token.span)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validate_qa_source_reports_missing_load_target() {
        let script_path = Path::new("/tmp/qa_validate_missing.qa");
        let diagnostics = validate_qa_source(script_path, "load \"missing.ab\"\n");

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].code.as_deref(),
            Some(QA_SEMANTIC_MISSING_LOAD)
        );
        assert_eq!(diagnostics[0].span, Some(Span { start: 6, end: 16 }));
    }

    #[test]
    fn validate_qa_source_reports_unknown_query_reference() {
        let root = std::env::temp_dir().join(format!("abide-qa-validate-{}", std::process::id()));
        std::fs::create_dir_all(&root).expect("create temp root");
        std::fs::write(
            root.join("model.ab"),
            "module QAValidate\n\
             enum TicketStatus = Open | Closed\n\
             entity Ticket {\n\
               status: TicketStatus = @Open\n\
             }\n",
        )
        .expect("write model");

        let script_path = root.join("query.qa");
        let diagnostics = validate_qa_source(
            &script_path,
            "load \"model.ab\"\nask terminal Missing.status\n",
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].code.as_deref(),
            Some(QA_SEMANTIC_UNKNOWN_REFERENCE)
        );
        assert_eq!(diagnostics[0].span, Some(Span { start: 29, end: 43 }));
    }

    #[test]
    fn validate_embedded_abide_blocks_uses_loaded_qa_context() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("abide")
            .join("tests")
            .join("fixtures");
        let script_path = root.join("test_hypothetical.qa");
        let source = std::fs::read_to_string(&script_path).expect("fixture source");

        let diagnostics = validate_embedded_abide_blocks(&script_path, &source);

        assert!(
            diagnostics.iter().all(|diagnostic| {
                !(diagnostic.message.contains("unresolved name")
                    && diagnostic.message.contains("Closed"))
            }),
            "embedded block should see variants from loaded base spec: {diagnostics:#?}"
        );
    }
}
