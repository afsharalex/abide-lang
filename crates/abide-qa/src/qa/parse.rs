//! QA language parser — hand-rolled parser for `.qa` files and REPL QA mode.
//!
//! Parses QA statements: `ask`, `explain`, `assert`, `load`, and artifact commands.
//! Disambiguation: `ask reachable...` is a QA command; `ask(x)` would be
//! a user function call (handled by the Abide parser, not here).

use super::ast::{
    BlockArg, BlockPredicate, QAStatement, Query, SimulationRequest, StateSpaceRequest,
    TemporalBounds, TemporalOp, TemporalTarget,
};
use abide_syntax::diagnostic::Diagnostic;
use abide_syntax::span::Span;

const QA_PARSE_EXPECTED: &str = "abide::qa::parse::expected";
const QA_PARSE_ERROR: &str = "abide::qa::parse::error";
const QA_PARSE_UNCLOSED_BLOCK: &str = "abide::qa::parse::unclosed_block";

/// Parse error for QA input.
#[derive(Debug, Clone)]
pub struct QAParseError {
    pub message: String,
    pub line: usize,
    pub span: Span,
    pub code: String,
    pub help: Option<String>,
}

impl std::fmt::Display for QAParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "qa parse error (line {}): {}", self.line, self.message)
    }
}

impl QAParseError {
    #[must_use]
    pub fn to_diagnostic(&self) -> Diagnostic {
        let mut diagnostic = Diagnostic::error(self.message.clone())
            .with_code(self.code.clone())
            .with_span(self.span);
        if let Some(help) = &self.help {
            diagnostic = diagnostic.with_help(help.clone());
        }
        diagnostic
    }
}

#[derive(Debug, Clone, Copy)]
struct QAToken<'a> {
    text: &'a str,
    span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QAEmbeddedAbideBlock {
    pub body: String,
    pub body_span: Span,
}

#[derive(Debug, Clone, Copy)]
struct OpenAbideBlock {
    start_line: usize,
    keyword_span: Span,
    body_start: usize,
    depth: i32,
}

fn qa_error(
    message: impl Into<String>,
    line: usize,
    span: Span,
    code: &'static str,
    help: Option<&str>,
) -> QAParseError {
    QAParseError {
        message: message.into(),
        line,
        span,
        code: code.to_owned(),
        help: help.map(str::to_owned),
    }
}

fn expected_error(
    message: impl Into<String>,
    line: usize,
    span: Span,
    help: Option<&str>,
) -> QAParseError {
    qa_error(message, line, span, QA_PARSE_EXPECTED, help)
}

fn general_error(
    message: impl Into<String>,
    line: usize,
    span: Span,
    help: Option<&str>,
) -> QAParseError {
    qa_error(message, line, span, QA_PARSE_ERROR, help)
}

fn empty_span(offset: usize) -> Span {
    Span {
        start: offset,
        end: offset.saturating_add(1),
    }
}

fn scan_qa_tokens(line: &str, line_start: usize) -> Vec<QAToken<'_>> {
    let mut tokens = Vec::new();
    let mut token_start = None;

    for (offset, ch) in line.char_indices() {
        if ch.is_whitespace() {
            if let Some(start) = token_start.take() {
                tokens.push(QAToken {
                    text: &line[start..offset],
                    span: Span {
                        start: line_start + start,
                        end: line_start + offset,
                    },
                });
            }
        } else if token_start.is_none() {
            token_start = Some(offset);
        }
    }

    if let Some(start) = token_start {
        tokens.push(QAToken {
            text: &line[start..],
            span: Span {
                start: line_start + start,
                end: line_start + line.len(),
            },
        });
    }

    tokens
}

/// Extract embedded `abide { ... }` blocks with byte spans into the original QA source.
pub fn embedded_abide_blocks(input: &str) -> Result<Vec<QAEmbeddedAbideBlock>, QAParseError> {
    let mut blocks = Vec::new();
    let mut open_block: Option<OpenAbideBlock> = None;
    let mut line_start = 0usize;

    for (line_num, line) in input.lines().enumerate() {
        let line_no = line_num + 1;
        let trimmed = line.trim();
        let trimmed_start = line.find(trimmed).unwrap_or(0);
        let trimmed_offset = line_start + trimmed_start;

        if let Some(mut block) = open_block.take() {
            if let Some(body_end) = update_abide_block_depth(line, line_start, &mut block.depth) {
                blocks.push(QAEmbeddedAbideBlock {
                    body: input[block.body_start..body_end].to_owned(),
                    body_span: Span {
                        start: block.body_start,
                        end: body_end,
                    },
                });
            } else {
                open_block = Some(block);
            }
            line_start += line.len() + 1;
            continue;
        }

        if trimmed.is_empty() || trimmed.starts_with("//") {
            line_start += line.len() + 1;
            continue;
        }

        if trimmed.starts_with("abide") && trimmed.contains('{') {
            let open_brace_in_trimmed = trimmed.find('{').expect("checked contains");
            let open_brace = trimmed_offset + open_brace_in_trimmed;
            let body_start = open_brace + 1;
            let after_brace = &input[body_start..line_start + line.len()];
            let mut depth = 1;
            if let Some(body_end) = update_abide_block_depth(after_brace, body_start, &mut depth) {
                blocks.push(QAEmbeddedAbideBlock {
                    body: input[body_start..body_end].to_owned(),
                    body_span: Span {
                        start: body_start,
                        end: body_end,
                    },
                });
            } else {
                open_block = Some(OpenAbideBlock {
                    start_line: line_no,
                    keyword_span: Span {
                        start: trimmed_offset,
                        end: trimmed_offset + "abide".len(),
                    },
                    body_start,
                    depth,
                });
            }
        }

        line_start += line.len() + 1;
    }

    if let Some(block) = open_block {
        return Err(qa_error(
            "unclosed abide block",
            block.start_line,
            block.keyword_span,
            QA_PARSE_UNCLOSED_BLOCK,
            Some("close the block with `}`"),
        ));
    }

    Ok(blocks)
}

fn update_abide_block_depth(text: &str, text_start: usize, depth: &mut i32) -> Option<usize> {
    for (offset, ch) in text.char_indices() {
        match ch {
            '{' => *depth += 1,
            '}' => {
                *depth -= 1;
                if *depth <= 0 {
                    return Some(text_start + offset);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse a `.qa` file or multi-line QA input into statements.
pub fn parse_qa(input: &str) -> Result<Vec<QAStatement>, QAParseError> {
    let mut statements = Vec::new();
    let mut abide_block: Option<(usize, Span, String, i32)> = None; // (start_line, start_span, content, brace_depth)
    let mut line_start = 0usize;

    for (line_num, line) in input.lines().enumerate() {
        let line_no = line_num + 1;
        let trimmed = line.trim();
        let trimmed_start = line.find(trimmed).unwrap_or(0);
        let trimmed_offset = line_start + trimmed_start;

        // Inside an abide block: accumulate until braces balance
        if let Some((_, _, ref mut content, ref mut depth)) = abide_block {
            for ch in trimmed.chars() {
                match ch {
                    '{' => *depth += 1,
                    '}' => *depth -= 1,
                    _ => {}
                }
            }
            if *depth <= 0 {
                // Block closed — strip the final '}'
                let body = content.trim().to_owned();
                statements.push(QAStatement::AbideBlock(body));
                abide_block = None;
            } else {
                content.push_str(line);
                content.push('\n');
            }
            line_start += line.len() + 1;
            continue;
        }

        // Skip empty lines and comments
        if trimmed.is_empty() || trimmed.starts_with("//") {
            line_start += line.len() + 1;
            continue;
        }

        // Start of abide block
        if trimmed.starts_with("abide") && trimmed.contains('{') {
            let after_brace = trimmed.find('{').map_or("", |i| &trimmed[i + 1..]);
            let mut depth: i32 = 1;
            for ch in after_brace.chars() {
                match ch {
                    '{' => depth += 1,
                    '}' => depth -= 1,
                    _ => {}
                }
            }
            if depth <= 0 {
                // Single-line abide block: abide { entity Foo {... } }
                let body = after_brace
                    .trim()
                    .strip_suffix('}')
                    .unwrap_or(after_brace.trim())
                    .trim()
                    .to_owned();
                statements.push(QAStatement::AbideBlock(body));
            } else {
                // Multi-line: start accumulating
                let mut content = after_brace.to_owned();
                content.push('\n');
                abide_block = Some((
                    line_no,
                    Span {
                        start: trimmed_offset,
                        end: trimmed_offset + "abide".len(),
                    },
                    content,
                    depth,
                ));
            }
            line_start += line.len() + 1;
            continue;
        }

        statements.push(parse_statement_at(trimmed, line_no, trimmed_offset)?);
        line_start += line.len() + 1;
    }

    if let Some((start_line, start_span, _, _)) = abide_block {
        return Err(qa_error(
            "unclosed abide block",
            start_line,
            start_span,
            QA_PARSE_UNCLOSED_BLOCK,
            Some("close the block with `}`"),
        ));
    }

    Ok(statements)
}

/// Parse a single QA statement from one line.
pub fn parse_statement(input: &str, line: usize) -> Result<QAStatement, QAParseError> {
    parse_statement_at(input, line, 0)
}

fn parse_statement_at(
    input: &str,
    line: usize,
    line_start: usize,
) -> Result<QAStatement, QAParseError> {
    let tokens = scan_qa_tokens(input, line_start);
    if tokens.is_empty() {
        return Err(expected_error(
            "empty statement",
            line,
            empty_span(line_start),
            Some("write a QA command such as `ask entities`"),
        ));
    }

    match tokens[0].text {
        "load" => parse_load(input, line, line_start, &tokens),
        "verify" => Ok(QAStatement::Verify),
        "simulate" => parse_simulate(&tokens[1..], line),
        "explore" => parse_explore(&tokens[1..], line),
        "artifacts" => Ok(QAStatement::Artifacts),
        "show" => parse_show_artifact(&tokens[1..], line),
        "draw" => parse_draw_artifact(&tokens[1..], line),
        "state" => parse_state_artifact(&tokens[1..], line),
        "diff" => parse_diff_artifact(&tokens[1..], line),
        "export" => parse_export_artifact(&tokens[1..], line),
        "ask" => {
            if tokens.len() > 1 && tokens[1].text == "{" {
                parse_block_ask(input, line, line_start)
            } else {
                Ok(QAStatement::Ask(parse_query(&tokens[1..], line)?))
            }
        }
        "explain" => Ok(QAStatement::Explain(parse_query(&tokens[1..], line)?)),
        "assert" => Ok(QAStatement::Assert(parse_query(&tokens[1..], line)?)),
        _ => {
            let help = if tokens[0].text == "query"
                && tokens.get(1).is_some_and(|token| token.text == "entities")
            {
                Some("try `ask entities`")
            } else {
                Some("start QA statements with `ask`, `explain`, `assert`, or `load`")
            };
            Err(expected_error(
                format!(
                "expected 'ask', 'explain', 'assert', 'load', 'verify', 'simulate', 'explore', 'artifacts', 'show', 'draw', 'state', 'diff', or 'export', got '{}'",
                tokens[0].text
            ),
                line,
                tokens[0].span,
                help,
            ))
        }
    }
}

fn parse_simulate(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    let mut request = SimulationRequest::default();
    let mut index = 0usize;
    while index < tokens.len() {
        match tokens[index].text {
            "--steps" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "simulate --steps requires a value",
                        line,
                        tokens[index].span,
                        Some("provide a non-negative integer after `--steps`"),
                    )
                })?;
                request.steps = parse_usize(value, "step count", line)?;
                index += 2;
            }
            "--seed" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "simulate --seed requires a value",
                        line,
                        tokens[index].span,
                        Some("provide a non-negative integer after `--seed`"),
                    )
                })?;
                request.seed = value.text.parse::<u64>().map_err(|_| {
                    general_error(
                        format!("invalid simulation seed '{}'", value.text),
                        line,
                        value.span,
                        Some("simulation seeds must be non-negative integers"),
                    )
                })?;
                index += 2;
            }
            "--slots" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "simulate --slots requires a value",
                        line,
                        tokens[index].span,
                        Some("provide a non-negative integer after `--slots`"),
                    )
                })?;
                request.slots = parse_usize(value, "slot count", line)?;
                index += 2;
            }
            "--scope" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "simulate --scope requires Entity=N",
                        line,
                        tokens[index].span,
                        Some("write scopes as `--scope Entity=N`"),
                    )
                })?;
                let (entity, slots) = value.text.split_once('=').ok_or_else(|| {
                    expected_error(
                        format!(
                            "invalid simulation scope '{}', expected Entity=N",
                            value.text
                        ),
                        line,
                        value.span,
                        Some("write scopes as `--scope Entity=N`"),
                    )
                })?;
                if entity.trim().is_empty() {
                    return Err(expected_error(
                        format!(
                            "invalid simulation scope '{}'; entity name must not be empty",
                            value.text
                        ),
                        line,
                        value.span,
                        Some("put the entity name before `=`"),
                    ));
                }
                request.scopes.push((
                    entity.trim().to_owned(),
                    parse_usize_text(slots, value.span, "scope slot count", line)?,
                ));
                index += 2;
            }
            "--system" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "simulate --system requires a system name",
                        line,
                        tokens[index].span,
                        Some("provide a system name after `--system`"),
                    )
                })?;
                request.system = Some(value.text.to_owned());
                index += 2;
            }
            other => {
                return Err(expected_error(
                    format!("unknown simulate option '{other}'"),
                    line,
                    tokens[index].span,
                    Some(
                        "expected one of `--steps`, `--seed`, `--slots`, `--scope`, or `--system`",
                    ),
                ));
            }
        }
    }
    Ok(QAStatement::Simulate(request))
}

fn parse_explore(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    let mut request = StateSpaceRequest::default();
    let mut index = 0usize;
    while index < tokens.len() {
        match tokens[index].text {
            "--depth" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "explore --depth requires a value",
                        line,
                        tokens[index].span,
                        Some("provide a non-negative integer after `--depth`"),
                    )
                })?;
                request.depth = Some(parse_usize(value, "exploration depth", line)?);
                index += 2;
            }
            "--slots" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "explore --slots requires a value",
                        line,
                        tokens[index].span,
                        Some("provide a non-negative integer after `--slots`"),
                    )
                })?;
                request.slots = parse_usize(value, "slot count", line)?;
                index += 2;
            }
            "--scope" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "explore --scope requires Entity=N",
                        line,
                        tokens[index].span,
                        Some("write scopes as `--scope Entity=N`"),
                    )
                })?;
                let (entity, slots) = value.text.split_once('=').ok_or_else(|| {
                    expected_error(
                        format!("invalid explore scope '{}', expected Entity=N", value.text),
                        line,
                        value.span,
                        Some("write scopes as `--scope Entity=N`"),
                    )
                })?;
                if entity.trim().is_empty() {
                    return Err(expected_error(
                        format!(
                            "invalid explore scope '{}'; entity name must not be empty",
                            value.text
                        ),
                        line,
                        value.span,
                        Some("put the entity name before `=`"),
                    ));
                }
                request.scopes.push((
                    entity.trim().to_owned(),
                    parse_usize_text(slots, value.span, "scope slot count", line)?,
                ));
                index += 2;
            }
            "--system" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        "explore --system requires a system name",
                        line,
                        tokens[index].span,
                        Some("provide a system name after `--system`"),
                    )
                })?;
                request.system = Some(value.text.to_owned());
                index += 2;
            }
            other => {
                return Err(expected_error(
                    format!("unknown explore option '{other}'"),
                    line,
                    tokens[index].span,
                    Some("expected one of `--depth`, `--slots`, `--scope`, or `--system`"),
                ));
            }
        }
    }
    Ok(QAStatement::Explore(request))
}

fn parse_show_artifact(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 2 || tokens[0].text != "artifact" {
        return Err(expected_error(
            "expected: show artifact <selector>",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `show artifact <selector>`"),
        ));
    }
    Ok(QAStatement::ShowArtifact(tokens[1].text.to_owned()))
}

fn parse_draw_artifact(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 2 || tokens[0].text != "artifact" {
        return Err(expected_error(
            "expected: draw artifact <selector>",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `draw artifact <selector>`"),
        ));
    }
    Ok(QAStatement::DrawArtifact(tokens[1].text.to_owned()))
}

fn parse_state_artifact(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 3 || tokens[0].text != "artifact" {
        return Err(expected_error(
            "expected: state artifact <selector> <index>",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `state artifact <selector> <index>`"),
        ));
    }
    Ok(QAStatement::StateArtifact {
        selector: tokens[1].text.to_owned(),
        index: parse_usize(&tokens[2], "state index", line)?,
    })
}

fn parse_diff_artifact(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 4 || tokens[0].text != "artifact" {
        return Err(expected_error(
            "expected: diff artifact <selector> <from> <to>",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `diff artifact <selector> <from> <to>`"),
        ));
    }
    Ok(QAStatement::DiffArtifact {
        selector: tokens[1].text.to_owned(),
        from: parse_usize(&tokens[2], "from state index", line)?,
        to: parse_usize(&tokens[3], "to state index", line)?,
    })
}

fn parse_export_artifact(tokens: &[QAToken<'_>], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 3 || tokens[0].text != "artifact" {
        return Err(expected_error(
            "expected: export artifact <selector> <format>",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `export artifact <selector> <format>`"),
        ));
    }
    Ok(QAStatement::ExportArtifact {
        selector: tokens[1].text.to_owned(),
        format: tokens[2].text.to_owned(),
    })
}

fn parse_usize(token: &QAToken<'_>, label: &str, line: usize) -> Result<usize, QAParseError> {
    parse_usize_text(token.text, token.span, label, line)
}

fn parse_usize_text(
    token: &str,
    span: Span,
    label: &str,
    line: usize,
) -> Result<usize, QAParseError> {
    token.parse::<usize>().map_err(|_| {
        general_error(
            format!("invalid {label} '{token}'"),
            line,
            span,
            Some("use a non-negative integer"),
        )
    })
}

/// Parse a `load "path"` statement.
fn parse_load(
    input: &str,
    line: usize,
    line_start: usize,
    tokens: &[QAToken<'_>],
) -> Result<QAStatement, QAParseError> {
    // Extract the path from: load "path/to/specs"
    let rest = input.trim_start_matches("load").trim();
    if let Some(path) = rest.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        Ok(QAStatement::Load(path.to_owned()))
    } else {
        let span = if let Some(path_token) = tokens.get(1) {
            path_token.span
        } else {
            tokens
                .first()
                .map_or_else(|| empty_span(line_start), |token| token.span)
        };
        Err(expected_error(
            "load requires a quoted path: load \"path/to/specs\"",
            line,
            span,
            Some("write load paths as `load \"path\"`"),
        ))
    }
}

/// Parse a query from tokens (after the verb).
fn parse_query(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    if tokens.is_empty() {
        return Err(expected_error(
            "expected a query after ask/explain/assert",
            line,
            empty_span(0),
            Some("try a query such as `entities`, `reachable`, or `terminal`"),
        ));
    }

    match tokens[0].text {
        // Negation
        "not" => {
            let inner = parse_query(&tokens[1..], line)?;
            Ok(Query::Not(Box::new(inner)))
        }

        // Discovery queries (no arguments)
        "entities" => Ok(Query::Entities),
        "systems" => Ok(Query::Systems),
        "types" => Ok(Query::Types),
        "interfaces" => Ok(Query::Interfaces),

        // Entity field queries: subcommand E.field [args...]
        "reachable" => parse_reachable(&tokens[1..], line),
        "path" => parse_path(&tokens[1..], line),
        // `terminal E.field` (existing) OR
        // `terminal states of E::field` ( / )
        "terminal" => parse_terminal_or_states(&tokens[1..], line),
        "initial" => parse_entity_field(&tokens[1..], line).map(|(e, f)| Query::Initial {
            entity: e,
            field: f,
        }),
        "cycles" => parse_entity_field(&tokens[1..], line).map(|(e, f)| Query::Cycles {
            entity: e,
            field: f,
        }),
        // `transitions from E.field == @State` (existing) OR
        // `transitions of E::field` ( / )
        "transitions" => parse_transitions_or_of(&tokens[1..], line),
        "updates" => parse_updates(&tokens[1..], line),
        "events" => parse_events(&tokens[1..], line),
        "match-coverage" => {
            parse_entity_field(&tokens[1..], line).map(|(e, f)| Query::MatchCoverage {
                entity: e,
                field: f,
            })
        }

        // Entity queries
        "invariants" => {
            parse_on_entity(&tokens[1..], line).map(|e| Query::Invariants { entity: e })
        }
        "contracts" => parse_contracts(&tokens[1..], line),

        // `ask fsms on E` lists every fsm field
        // declared on the named entity.
        "fsms" => parse_on_entity(&tokens[1..], line).map(|e| Query::Fsms { entity: e }),

        // System queries
        "cross-calls" => {
            parse_from_system(&tokens[1..], line).map(|s| Query::CrossCalls { system: s })
        }
        "deadlock" => {
            if tokens.len() < 2 {
                return Err(expected_error(
                    "deadlock requires a system name",
                    line,
                    tokens[0].span,
                    Some("write `deadlock SystemName`"),
                ));
            }
            Ok(Query::Deadlock {
                system: tokens[1].text.to_owned(),
            })
        }

        // Temporal assertions (delegate to Abide expression)
        "always" => parse_temporal_query(TemporalOp::Always, &tokens[1..], line),
        "eventually" => parse_temporal_query(TemporalOp::Eventually, &tokens[1..], line),

        other => Err(expected_error(
            format!(
                "unknown query type '{other}'. Expected: reachable, path, terminal, initial, \
                 cycles, transitions, entities, systems, types, interfaces, invariants, \
                 contracts, events, match-coverage, cross-calls, updates, deadlock, always, \
                 eventually, not"
            ),
            line,
            tokens[0].span,
            Some("use a known QA query after `ask`, `explain`, or `assert`"),
        )),
    }
}

fn parse_temporal_query(
    op: TemporalOp,
    tokens: &[QAToken<'_>],
    line: usize,
) -> Result<Query, QAParseError> {
    if tokens.is_empty() {
        return Err(expected_error(
            format!(
                "{} requires an expression",
                match op {
                    TemporalOp::Always => "always",
                    TemporalOp::Eventually => "eventually",
                }
            ),
            line,
            empty_span(0),
            Some("provide an Abide expression for the temporal query"),
        ));
    }

    let mut bounds = TemporalBounds::default();
    let mut index = 0usize;
    while index < tokens.len() {
        match tokens[index].text {
            "--slots" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        format!(
                            "{} --slots requires a value",
                            match op {
                                TemporalOp::Always => "always",
                                TemporalOp::Eventually => "eventually",
                            }
                        ),
                        line,
                        tokens[index].span,
                        Some("provide a non-negative integer after `--slots`"),
                    )
                })?;
                bounds.slots = Some(parse_usize(value, "slot count", line)?);
                index += 2;
            }
            "--scope" => {
                let value = tokens.get(index + 1).ok_or_else(|| {
                    expected_error(
                        format!(
                            "{} --scope requires Entity=N",
                            match op {
                                TemporalOp::Always => "always",
                                TemporalOp::Eventually => "eventually",
                            }
                        ),
                        line,
                        tokens[index].span,
                        Some("write scopes as `--scope Entity=N`"),
                    )
                })?;
                let (entity, slots) = value.text.split_once('=').ok_or_else(|| {
                    expected_error(
                        format!("invalid temporal scope '{}', expected Entity=N", value.text),
                        line,
                        value.span,
                        Some("write scopes as `--scope Entity=N`"),
                    )
                })?;
                if entity.trim().is_empty() {
                    return Err(expected_error(
                        format!(
                            "invalid temporal scope '{}'; entity name must not be empty",
                            value.text
                        ),
                        line,
                        value.span,
                        Some("put the entity name before `=`"),
                    ));
                }
                bounds.scopes.push((
                    entity.trim().to_owned(),
                    parse_usize_text(slots, value.span, "scope slot count", line)?,
                ));
                index += 2;
            }
            _ => break,
        }
    }

    let (target, expr_tokens) = if tokens.get(index).is_some_and(|token| token.text == "on") {
        if tokens.len() < index + 3 {
            return Err(expected_error(
                format!(
                    "expected: {} on Owner[.field] <expr>",
                    match op {
                        TemporalOp::Always => "always",
                        TemporalOp::Eventually => "eventually",
                    }
                ),
                line,
                tokens[index].span,
                Some("provide a target and expression after `on`"),
            ));
        }
        (
            Some(parse_temporal_target(tokens[index + 1], line)?),
            &tokens[index + 2..],
        )
    } else {
        (None, &tokens[index..])
    };

    let expr = expr_tokens
        .iter()
        .map(|token| token.text)
        .collect::<Vec<_>>()
        .join(" ");
    if expr.trim().is_empty() {
        return Err(expected_error(
            format!(
                "{} requires an expression",
                match op {
                    TemporalOp::Always => "always",
                    TemporalOp::Eventually => "eventually",
                }
            ),
            line,
            tokens
                .last()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("provide an Abide expression for the temporal query"),
        ));
    }

    Ok(Query::Temporal {
        op,
        bounds,
        target,
        expr,
    })
}

fn parse_temporal_target(token: QAToken<'_>, line: usize) -> Result<TemporalTarget, QAParseError> {
    if let Some((owner, field)) = token.text.split_once('.') {
        return Ok(TemporalTarget {
            owner: owner.to_owned(),
            field: Some(field.to_owned()),
        });
    }

    if token.text.is_empty() {
        return Err(expected_error(
            "expected Owner or Owner.field after `on`",
            line,
            token.span,
            Some("write `on Owner` or `on Owner.field`"),
        ));
    }

    Ok(TemporalTarget {
        owner: token.text.to_owned(),
        field: None,
    })
}

/// Parse `E.field` from tokens. Returns `(entity, field)`.
fn parse_entity_field(
    tokens: &[QAToken<'_>],
    line: usize,
) -> Result<(String, String), QAParseError> {
    if tokens.is_empty() {
        return Err(expected_error(
            "expected E.field",
            line,
            empty_span(0),
            Some("provide an entity field such as `Order.status`"),
        ));
    }
    split_dot(tokens[0], line)
}

/// Split `E.field` into `(entity, field)`.
fn split_dot(token: QAToken<'_>, line: usize) -> Result<(String, String), QAParseError> {
    if let Some((entity, field)) = token.text.split_once('.') {
        Ok((entity.to_owned(), field.to_owned()))
    } else {
        Err(expected_error(
            format!("expected E.field (dot-separated), got '{}'", token.text),
            line,
            token.span,
            Some("write entity fields with `.`, for example `Order.status`"),
        ))
    }
}

/// Parse `reachable E.field -> @State`
fn parse_reachable(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    // reachable E.field -> @State
    if tokens.len() < 3 || tokens[1].text != "->" {
        return Err(expected_error(
            "expected: reachable E.field -> @State",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `reachable Entity.field -> @State`"),
        ));
    }
    let (entity, field) = split_dot(tokens[0], line)?;
    let state = strip_at(tokens[2].text);
    Ok(Query::Reachable {
        entity,
        field,
        state,
    })
}

/// Parse `path E.field @From -> @To`
fn parse_path(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    // path E.field @From -> @To
    if tokens.len() < 4 || tokens[2].text != "->" {
        return Err(expected_error(
            "expected: path E.field @From -> @To",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `path Entity.field @From -> @To`"),
        ));
    }
    let (entity, field) = split_dot(tokens[0], line)?;
    let from = strip_at(tokens[1].text);
    let to = strip_at(tokens[3].text);
    Ok(Query::Path {
        entity,
        field,
        from,
        to,
    })
}

/// Parse `transitions from E.field == @State`
fn parse_transitions(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    // transitions from E.field == @State
    if tokens.len() < 4 || tokens[0].text != "from" || tokens[2].text != "==" {
        return Err(expected_error(
            "expected: transitions from E.field == @State",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `transitions from Entity.field == @State`"),
        ));
    }
    let (entity, field) = split_dot(tokens[1], line)?;
    let state = strip_at(tokens[3].text);
    Ok(Query::Transitions {
        entity,
        field,
        state,
    })
}

/// dispatch `transitions from...` (the existing
/// state-graph query) vs `transitions of E::field` (the new fsm
/// declaration query).
fn parse_transitions_or_of(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    match tokens.first().map(|token| token.text) {
        Some("of") => {
            if tokens.len() < 2 {
                return Err(expected_error(
                    "expected: transitions of E::field",
                    line,
                    tokens[0].span,
                    Some("write `transitions of Entity::field`"),
                ));
            }
            let (entity, field) = split_double_colon(tokens[1], line)?;
            Ok(Query::FsmTransitions { entity, field })
        }
        Some("from") => parse_transitions(tokens, line),
        _ => Err(expected_error(
            "expected: transitions from E.field == @State, or transitions of E::field",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some(
                "write `transitions from Entity.field == @State` or `transitions of Entity::field`",
            ),
        )),
    }
}

/// dispatch `terminal E.field` (the existing
/// state-graph query) vs `terminal states of E::field` (the new fsm
/// declaration query).
fn parse_terminal_or_states(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    if matches!(tokens.first().map(|token| token.text), Some("states")) {
        // `terminal states of E::field`
        if tokens.len() < 3 || tokens[1].text != "of" {
            return Err(expected_error(
                "expected: terminal states of E::field",
                line,
                tokens
                    .first()
                    .map_or_else(|| empty_span(0), |token| token.span),
                Some("write `terminal states of Entity::field`"),
            ));
        }
        let (entity, field) = split_double_colon(tokens[2], line)?;
        Ok(Query::FsmTerminalStates { entity, field })
    } else {
        // Existing `terminal E.field`
        parse_entity_field(tokens, line).map(|(e, f)| Query::Terminal {
            entity: e,
            field: f,
        })
    }
}

/// Split `E::field` into `(entity, field)`. Used for the
/// / fsm queries which use `::` instead of `.`
/// to disambiguate fsm-declared structure from state-graph structure.
fn split_double_colon(token: QAToken<'_>, line: usize) -> Result<(String, String), QAParseError> {
    if let Some((entity, field)) = token.text.split_once("::") {
        Ok((entity.to_owned(), field.to_owned()))
    } else {
        Err(expected_error(
            format!(
                "expected E::field (double-colon-separated), got '{}'",
                token.text
            ),
            line,
            token.span,
            Some("write fsm fields with `::`, for example `Order::status`"),
        ))
    }
}

/// Parse `updates on E.field @From -> @To`
fn parse_updates(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    // updates on E.field @From -> @To
    if tokens.len() < 5 || tokens[0].text != "on" || tokens[3].text != "->" {
        return Err(expected_error(
            "expected: updates on E.field @From -> @To",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `updates on Entity.field @From -> @To`"),
        ));
    }
    let (entity, field) = split_dot(tokens[1], line)?;
    let from = strip_at(tokens[2].text);
    let to = strip_at(tokens[4].text);
    Ok(Query::Updates {
        entity,
        field,
        from,
        to,
    })
}

/// Parse `events on E.field`
fn parse_events(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    if tokens.len() < 2 || tokens[0].text != "on" {
        return Err(expected_error(
            "expected: events on E.field",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `events on Entity.field`"),
        ));
    }
    let (entity, field) = split_dot(tokens[1], line)?;
    Ok(Query::Events { entity, field })
}

/// Parse `invariants on E`
fn parse_on_entity(tokens: &[QAToken<'_>], line: usize) -> Result<String, QAParseError> {
    if tokens.len() < 2 || tokens[0].text != "on" {
        return Err(expected_error(
            "expected: ... on EntityName",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `on EntityName`"),
        ));
    }
    Ok(tokens[1].text.to_owned())
}

/// Parse `contracts on E.action`
fn parse_contracts(tokens: &[QAToken<'_>], line: usize) -> Result<Query, QAParseError> {
    if tokens.len() < 2 || tokens[0].text != "on" {
        return Err(expected_error(
            "expected: contracts on E.action",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `contracts on Entity.action`"),
        ));
    }
    let (entity, action) = split_dot(tokens[1], line)?;
    Ok(Query::Contracts { entity, action })
}

/// Parse `cross-calls from System`
fn parse_from_system(tokens: &[QAToken<'_>], line: usize) -> Result<String, QAParseError> {
    if tokens.len() < 2 || tokens[0].text != "from" {
        return Err(expected_error(
            "expected: ... from SystemName",
            line,
            tokens
                .first()
                .map_or_else(|| empty_span(0), |token| token.span),
            Some("write `from SystemName`"),
        ));
    }
    Ok(tokens[1].text.to_owned())
}

/// Parse block-form: `ask { for e, f, s where pred(e, f, s) select e, f, s }`
fn parse_block_ask(
    input: &str,
    line: usize,
    line_start: usize,
) -> Result<QAStatement, QAParseError> {
    // Strip "ask {" prefix and "}" suffix
    let inner = input
        .trim_start_matches("ask")
        .trim()
        .strip_prefix('{')
        .and_then(|s| s.strip_suffix('}'))
        .map(str::trim);

    let Some(inner) = inner else {
        return Err(expected_error(
            "block query must be: ask { for ... select ... }",
            line,
            Span {
                start: line_start,
                end: line_start + input.len(),
            },
            Some("close the block query with `}`"),
        ));
    };

    let mut bindings = Vec::new();
    let mut predicates = Vec::new();
    let mut select = Vec::new();

    // Split on keywords: for, where, not, select
    let parts: Vec<&str> = inner.split_whitespace().collect();
    let mut i = 0;

    // Parse "for e, f, s"
    if i < parts.len() && parts[i] == "for" {
        i += 1;
        while i < parts.len() && parts[i] != "where" && parts[i] != "not" && parts[i] != "select" {
            let var = parts[i].trim_end_matches(',');
            bindings.push(var.to_owned());
            i += 1;
        }
    }

    // Parse "where pred(args)" and "not pred(args)"
    // Predicates may span multiple whitespace-separated tokens due to
    // args containing spaces: state(e, f, s) → ["state(e,", "f,", "s)"]
    while i < parts.len() && (parts[i] == "where" || parts[i] == "not") {
        let negated = parts[i] == "not";
        i += 1; // skip "where" or "not"
        if i >= parts.len() {
            break;
        }
        // Collect tokens until we have balanced parens
        let mut pred_parts = vec![parts[i].to_owned()];
        i += 1;
        while i < parts.len() && !pred_parts.last().is_some_and(|s| s.ends_with(')')) {
            pred_parts.push(parts[i].to_owned());
            i += 1;
        }
        let pred_str = pred_parts.join(" ");
        if let Some((name, args_str)) = pred_str.split_once('(') {
            let args_str = args_str.trim_end_matches(')');
            let args = parse_block_args(args_str);
            predicates.push(BlockPredicate {
                negated,
                name: name.to_owned(),
                args,
            });
        }
    }

    // Parse "select e, f, s"
    if i < parts.len() && parts[i] == "select" {
        i += 1;
        while i < parts.len() {
            let var = parts[i].trim_end_matches(',');
            select.push(var.to_owned());
            i += 1;
        }
    }

    Ok(QAStatement::Ask(Query::Block {
        bindings,
        predicates,
        select,
    }))
}

/// Parse block predicate arguments: `e, f, s` or `e, f, from: s1, to: s2`
fn parse_block_args(input: &str) -> Vec<BlockArg> {
    input
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|arg| {
            if let Some((name, value)) = arg.split_once(':') {
                BlockArg::Named(name.trim().to_owned(), value.trim().to_owned())
            } else {
                BlockArg::Positional(arg.to_owned())
            }
        })
        .collect()
}

/// Strip optional `@` prefix from a state name.
fn strip_at(s: &str) -> String {
    s.strip_prefix('@').unwrap_or(s).to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_load_statement() {
        let stmts = parse_qa("load \"src/commerce/\"").unwrap();
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0], QAStatement::Load("src/commerce/".to_owned()));
    }

    #[test]
    fn parse_verify_and_artifact_commands() {
        assert_eq!(parse_qa("verify").unwrap()[0], QAStatement::Verify);
        assert_eq!(
            parse_qa("simulate --steps 5 --seed 7 --slots 2 --scope Order=3 --system Shop")
                .unwrap()[0],
            QAStatement::Simulate(SimulationRequest {
                steps: 5,
                seed: 7,
                slots: 2,
                scopes: vec![("Order".to_owned(), 3)],
                system: Some("Shop".to_owned()),
            })
        );
        assert_eq!(parse_qa("artifacts").unwrap()[0], QAStatement::Artifacts);
        assert_eq!(
            parse_qa("show artifact 3").unwrap()[0],
            QAStatement::ShowArtifact("3".to_owned())
        );
        assert_eq!(
            parse_qa("show artifact order_safety").unwrap()[0],
            QAStatement::ShowArtifact("order_safety".to_owned())
        );
        assert_eq!(
            parse_qa("draw artifact counterexample:order_safety").unwrap()[0],
            QAStatement::DrawArtifact("counterexample:order_safety".to_owned())
        );
        assert_eq!(
            parse_qa("state artifact deadlock:hang 5").unwrap()[0],
            QAStatement::StateArtifact {
                selector: "deadlock:hang".to_owned(),
                index: 5
            }
        );
        assert_eq!(
            parse_qa("diff artifact 5 1 2").unwrap()[0],
            QAStatement::DiffArtifact {
                selector: "5".to_owned(),
                from: 1,
                to: 2
            }
        );
        assert_eq!(
            parse_qa("export artifact admitted:proof_ref json").unwrap()[0],
            QAStatement::ExportArtifact {
                selector: "admitted:proof_ref".to_owned(),
                format: "json".to_owned()
            }
        );
    }

    #[test]
    fn parse_ask_entities() {
        let stmts = parse_qa("ask entities").unwrap();
        assert_eq!(stmts[0], QAStatement::Ask(Query::Entities));
    }

    #[test]
    fn parse_ask_systems() {
        let stmts = parse_qa("ask systems").unwrap();
        assert_eq!(stmts[0], QAStatement::Ask(Query::Systems));
    }

    #[test]
    fn parse_ask_types() {
        let stmts = parse_qa("ask types").unwrap();
        assert_eq!(stmts[0], QAStatement::Ask(Query::Types));
    }

    #[test]
    fn parse_ask_interfaces() {
        let stmts = parse_qa("ask interfaces").unwrap();
        assert_eq!(stmts[0], QAStatement::Ask(Query::Interfaces));
    }

    #[test]
    fn parse_ask_reachable() {
        let stmts = parse_qa("ask reachable Order.status -> @Shipped").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Reachable {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
                state: "Shipped".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_reachable_no_at() {
        let stmts = parse_qa("ask reachable Order.status -> Shipped").unwrap();
        match &stmts[0] {
            QAStatement::Ask(Query::Reachable { state, .. }) => {
                assert_eq!(state, "Shipped");
            }
            other => panic!("expected Reachable, got {other:?}"),
        }
    }

    #[test]
    fn parse_ask_path() {
        let stmts = parse_qa("ask path Order.status @Pending -> @Shipped").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Path {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
                from: "Pending".to_owned(),
                to: "Shipped".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_terminal() {
        let stmts = parse_qa("ask terminal Order.status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Terminal {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_cycles() {
        let stmts = parse_qa("ask cycles Order.status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Cycles {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })
        );
    }

    #[test]
    fn parse_assert_not_cycles() {
        let stmts = parse_qa("assert not cycles Order.status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Assert(Query::Not(Box::new(Query::Cycles {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })))
        );
    }

    #[test]
    fn parse_assert_reachable() {
        let stmts = parse_qa("assert reachable Order.status -> @Shipped").unwrap();
        match &stmts[0] {
            QAStatement::Assert(Query::Reachable { .. }) => {}
            other => panic!("expected Assert(Reachable), got {other:?}"),
        }
    }

    #[test]
    fn parse_explain_path() {
        let stmts = parse_qa("explain path Order.status @Pending -> @Shipped").unwrap();
        match &stmts[0] {
            QAStatement::Explain(Query::Path { .. }) => {}
            other => panic!("expected Explain(Path), got {other:?}"),
        }
    }

    #[test]
    fn parse_explain_not_reachable() {
        let stmts = parse_qa("explain not reachable Order.status -> @Refunded").unwrap();
        match &stmts[0] {
            QAStatement::Explain(Query::Not(inner)) => {
                assert!(matches!(**inner, Query::Reachable { .. }));
            }
            other => panic!("expected Explain(Not(Reachable)), got {other:?}"),
        }
    }

    #[test]
    fn parse_ask_transitions() {
        let stmts = parse_qa("ask transitions from Order.status == @Pending").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Transitions {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
                state: "Pending".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_cross_calls() {
        let stmts = parse_qa("ask cross-calls from Commerce").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::CrossCalls {
                system: "Commerce".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_invariants() {
        let stmts = parse_qa("ask invariants on Order").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Invariants {
                entity: "Order".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_contracts() {
        let stmts = parse_qa("ask contracts on Order.submit").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Contracts {
                entity: "Order".to_owned(),
                action: "submit".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_events() {
        let stmts = parse_qa("ask events on Order.status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Events {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_deadlock() {
        let stmts = parse_qa("ask deadlock Commerce").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Deadlock {
                system: "Commerce".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_updates() {
        let stmts = parse_qa("ask updates on Order.status @Pending -> @Confirmed").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Updates {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
                from: "Pending".to_owned(),
                to: "Confirmed".to_owned(),
            })
        );
    }

    // fsm-specific QA queries.

    #[test]
    fn parse_ask_fsms_on_entity() {
        let stmts = parse_qa("ask fsms on Order").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Fsms {
                entity: "Order".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_fsm_transitions() {
        let stmts = parse_qa("ask transitions of Order::status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::FsmTransitions {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })
        );
    }

    #[test]
    fn parse_ask_fsm_terminal_states() {
        let stmts = parse_qa("ask terminal states of Order::status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::FsmTerminalStates {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })
        );
    }

    /// The legacy `transitions from E.field == @State` and `terminal
    /// E.field` queries must keep working alongside the new fsm forms.
    #[test]
    fn parse_legacy_transitions_and_terminal_still_work() {
        let stmts = parse_qa("ask transitions from Order.status == @Pending").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Transitions {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
                state: "Pending".to_owned(),
            })
        );
        let stmts = parse_qa("ask terminal Order.status").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Ask(Query::Terminal {
                entity: "Order".to_owned(),
                field: "status".to_owned(),
            })
        );
    }

    #[test]
    fn parse_assert_terminal() {
        let stmts = parse_qa("assert terminal Order.status").unwrap();
        match &stmts[0] {
            QAStatement::Assert(Query::Terminal { entity, field }) => {
                assert_eq!(entity, "Order");
                assert_eq!(field, "status");
            }
            other => panic!("expected Assert(Terminal), got {other:?}"),
        }
    }

    #[test]
    fn parse_assert_always() {
        let stmts = parse_qa("assert always (all o: Order | o.balance >= 0)").unwrap();
        match &stmts[0] {
            QAStatement::Assert(Query::Temporal {
                op: TemporalOp::Always,
                bounds,
                target: None,
                expr,
            }) => {
                assert!(bounds.is_empty());
                assert!(expr.contains("all o: Order"));
            }
            other => panic!("expected Assert(Temporal Always), got {other:?}"),
        }
    }

    #[test]
    fn parse_assert_always_with_explicit_target() {
        let stmts = parse_qa("assert always on Order.status (o.status == @Paid)").unwrap();
        match &stmts[0] {
            QAStatement::Assert(Query::Temporal {
                op: TemporalOp::Always,
                bounds,
                target: Some(target),
                expr,
            }) => {
                assert!(bounds.is_empty());
                assert_eq!(target.owner, "Order");
                assert_eq!(target.field.as_deref(), Some("status"));
                assert!(expr.contains("o.status"));
            }
            other => panic!("expected Assert(Temporal Always on target), got {other:?}"),
        }
    }

    #[test]
    fn parse_assert_always_with_temporal_bounds() {
        let stmts = parse_qa(
            "assert always --slots 6 --scope Order=2 on Commerce (all o: Order | o.total >= 0.0)",
        )
        .unwrap();
        match &stmts[0] {
            QAStatement::Assert(Query::Temporal {
                op: TemporalOp::Always,
                bounds,
                target: Some(target),
                expr,
            }) => {
                assert_eq!(bounds.slots, Some(6));
                assert_eq!(bounds.scopes, vec![("Order".to_owned(), 2)]);
                assert_eq!(target.owner, "Commerce");
                assert_eq!(target.field, None);
                assert!(expr.contains("all o: Order"));
            }
            other => panic!("expected Assert(Temporal Always with bounds), got {other:?}"),
        }
    }

    #[test]
    fn parse_explore_with_bounds() {
        let stmts =
            parse_qa("explore --depth 5 --slots 2 --scope Order=3 --system Commerce").unwrap();
        assert_eq!(
            stmts[0],
            QAStatement::Explore(StateSpaceRequest {
                depth: Some(5),
                slots: 2,
                scopes: vec![("Order".to_owned(), 3)],
                system: Some("Commerce".to_owned()),
            })
        );
    }

    #[test]
    fn parse_multi_line_script() {
        let input = r#"
load "src/commerce/"

// Check reachability
ask entities
assert reachable Order.status -> @Shipped
assert not cycles Order.status
explain path Order.status @Pending -> @Shipped
"#;
        let stmts = parse_qa(input).unwrap();
        assert_eq!(stmts.len(), 5);
        assert!(matches!(stmts[0], QAStatement::Load(_)));
        assert!(matches!(stmts[1], QAStatement::Ask(Query::Entities)));
        assert!(matches!(
            stmts[2],
            QAStatement::Assert(Query::Reachable { .. })
        ));
        assert!(matches!(stmts[3], QAStatement::Assert(Query::Not(_))));
        assert!(matches!(stmts[4], QAStatement::Explain(Query::Path { .. })));
    }

    #[test]
    fn parse_block_query() {
        let stmts = parse_qa(
            "ask { for e, f, s where state(e, f, s) not transition(e, f, from: s) select e, f, s }",
        )
        .unwrap();
        match &stmts[0] {
            QAStatement::Ask(Query::Block {
                bindings,
                predicates,
                select,
            }) => {
                assert_eq!(bindings, &["e", "f", "s"]);
                assert_eq!(predicates.len(), 2);
                assert!(!predicates[0].negated);
                assert_eq!(predicates[0].name, "state");
                assert!(predicates[1].negated);
                assert_eq!(predicates[1].name, "transition");
                // Check named arg
                assert!(predicates[1].args.iter().any(|a| matches!(
                    a,
                    BlockArg::Named(n, v) if n == "from" && v == "s"
                )));
                assert_eq!(select, &["e", "f", "s"]);
            }
            other => panic!("expected Block query, got {other:?}"),
        }
    }

    #[test]
    fn parse_comments_and_blanks_skipped() {
        let input = "// This is a comment\n\n  \nask entities\n// Another comment\n";
        let stmts = parse_qa(input).unwrap();
        assert_eq!(stmts.len(), 1);
    }

    #[test]
    fn parse_error_unknown_verb() {
        let result = parse_qa("query entities");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("expected"));
    }

    #[test]
    fn parse_error_unknown_verb_has_diagnostic_payload() {
        let err = parse_qa("query entities").unwrap_err();
        assert_eq!(err.code, "abide::qa::parse::expected");
        assert_eq!(err.span.start, 0);
        assert_eq!(err.span.end, 5);
        assert_eq!(err.help.as_deref(), Some("try `ask entities`"));

        let diagnostic = err.to_diagnostic();
        assert_eq!(
            diagnostic.code.as_deref(),
            Some("abide::qa::parse::expected")
        );
        assert_eq!(diagnostic.span, Some(err.span));
        assert_eq!(diagnostic.help.as_deref(), Some("try `ask entities`"));
    }

    #[test]
    fn parse_error_missing_path() {
        let result = parse_qa("load commerce/");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("quoted path"));
    }

    #[test]
    fn parse_error_missing_load_quotes_points_at_path() {
        let err = parse_qa("load commerce/").unwrap_err();
        assert_eq!(err.code, "abide::qa::parse::expected");
        assert_eq!(err.span.start, 5);
        assert_eq!(err.span.end, 14);
        assert_eq!(
            err.help.as_deref(),
            Some("write load paths as `load \"path\"`")
        );
    }

    #[test]
    fn parse_error_missing_option_value_points_at_option() {
        let err = parse_qa("simulate --steps").unwrap_err();
        assert_eq!(err.code, "abide::qa::parse::expected");
        assert_eq!(err.span.start, 9);
        assert_eq!(err.span.end, 16);
        assert_eq!(
            err.help.as_deref(),
            Some("provide a non-negative integer after `--steps`")
        );
    }

    #[test]
    fn parse_error_unclosed_abide_block_points_at_block_start() {
        let err = parse_qa("ask entities\nabide {\n  entity Ticket {\n").unwrap_err();
        assert_eq!(err.code, "abide::qa::parse::unclosed_block");
        assert_eq!(err.line, 2);
        assert_eq!(err.span.start, 13);
        assert_eq!(err.span.end, 18);
        assert_eq!(err.help.as_deref(), Some("close the block with `}`"));
    }

    #[test]
    fn embedded_abide_blocks_record_multiline_body_span() {
        let source =
            "ask entities\nabide {\n  entity Ticket {\n    status: int\n  }\n}\nask types\n";
        let blocks = embedded_abide_blocks(source).expect("embedded blocks");

        assert_eq!(blocks.len(), 1);
        assert_eq!(
            blocks[0].body,
            "\n  entity Ticket {\n    status: int\n  }\n"
        );
        assert_eq!(blocks[0].body_span, Span { start: 20, end: 59 });
        assert_eq!(
            &source[blocks[0].body_span.start..blocks[0].body_span.end],
            blocks[0].body
        );
    }

    #[test]
    fn embedded_abide_blocks_record_single_line_body_span() {
        let source = "abide { entity Ticket { status: int } }\nask entities\n";
        let blocks = embedded_abide_blocks(source).expect("embedded blocks");

        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].body, " entity Ticket { status: int } ");
        assert_eq!(blocks[0].body_span, Span { start: 7, end: 38 });
        assert_eq!(
            &source[blocks[0].body_span.start..blocks[0].body_span.end],
            blocks[0].body
        );
    }

    #[test]
    fn parse_error_missing_dot() {
        let result = parse_qa("ask terminal Order");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("dot-separated"));
    }
}
