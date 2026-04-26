//! QA language parser — hand-rolled parser for `.qa` files and REPL QA mode.
//!
//! Parses QA statements: `ask`, `explain`, `assert`, `load`, and artifact commands.
//! Disambiguation: `ask reachable...` is a QA command; `ask(x)` would be
//! a user function call (handled by the Abide parser, not here).

use super::ast::{BlockArg, BlockPredicate, QAStatement, Query, SimulationRequest};

/// Parse error for QA input.
#[derive(Debug, Clone)]
pub struct QAParseError {
    pub message: String,
    pub line: usize,
}

impl std::fmt::Display for QAParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "qa parse error (line {}): {}", self.line, self.message)
    }
}

/// Parse a `.qa` file or multi-line QA input into statements.
pub fn parse_qa(input: &str) -> Result<Vec<QAStatement>, QAParseError> {
    let mut statements = Vec::new();
    let mut abide_block: Option<(usize, String, i32)> = None; // (start_line, content, brace_depth)

    for (line_num, line) in input.lines().enumerate() {
        let line_no = line_num + 1;
        let trimmed = line.trim();

        // Inside an abide block: accumulate until braces balance
        if let Some((_, ref mut content, ref mut depth)) = abide_block {
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
            continue;
        }

        // Skip empty lines and comments
        if trimmed.is_empty() || trimmed.starts_with("//") {
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
                abide_block = Some((line_no, content, depth));
            }
            continue;
        }

        statements.push(parse_statement(trimmed, line_no)?);
    }

    if let Some((start_line, _, _)) = abide_block {
        return Err(QAParseError {
            message: "unclosed abide block".to_owned(),
            line: start_line,
        });
    }

    Ok(statements)
}

/// Parse a single QA statement from one line.
pub fn parse_statement(input: &str, line: usize) -> Result<QAStatement, QAParseError> {
    let tokens: Vec<&str> = input.split_whitespace().collect();
    if tokens.is_empty() {
        return Err(QAParseError {
            message: "empty statement".to_owned(),
            line,
        });
    }

    match tokens[0] {
        "load" => parse_load(input, line),
        "verify" => Ok(QAStatement::Verify),
        "simulate" => parse_simulate(&tokens[1..], line),
        "artifacts" => Ok(QAStatement::Artifacts),
        "show" => parse_show_artifact(&tokens[1..], line),
        "draw" => parse_draw_artifact(&tokens[1..], line),
        "state" => parse_state_artifact(&tokens[1..], line),
        "diff" => parse_diff_artifact(&tokens[1..], line),
        "export" => parse_export_artifact(&tokens[1..], line),
        "ask" => {
            if tokens.len() > 1 && tokens[1] == "{" {
                parse_block_ask(input, line)
            } else {
                Ok(QAStatement::Ask(parse_query(&tokens[1..], line)?))
            }
        }
        "explain" => Ok(QAStatement::Explain(parse_query(&tokens[1..], line)?)),
        "assert" => Ok(QAStatement::Assert(parse_query(&tokens[1..], line)?)),
        _ => Err(QAParseError {
            message: format!(
                "expected 'ask', 'explain', 'assert', 'load', 'verify', 'simulate', 'artifacts', 'show', 'draw', 'state', 'diff', or 'export', got '{}'",
                tokens[0]
            ),
            line,
        }),
    }
}

fn parse_simulate(tokens: &[&str], line: usize) -> Result<QAStatement, QAParseError> {
    let mut request = SimulationRequest::default();
    let mut index = 0usize;
    while index < tokens.len() {
        match tokens[index] {
            "--steps" => {
                let value = tokens.get(index + 1).ok_or_else(|| QAParseError {
                    message: "simulate --steps requires a value".to_owned(),
                    line,
                })?;
                request.steps = parse_usize(value, "step count", line)?;
                index += 2;
            }
            "--seed" => {
                let value = tokens.get(index + 1).ok_or_else(|| QAParseError {
                    message: "simulate --seed requires a value".to_owned(),
                    line,
                })?;
                request.seed = value.parse::<u64>().map_err(|_| QAParseError {
                    message: format!("invalid simulation seed '{value}'"),
                    line,
                })?;
                index += 2;
            }
            "--slots" => {
                let value = tokens.get(index + 1).ok_or_else(|| QAParseError {
                    message: "simulate --slots requires a value".to_owned(),
                    line,
                })?;
                request.slots = parse_usize(value, "slot count", line)?;
                index += 2;
            }
            "--scope" => {
                let value = tokens.get(index + 1).ok_or_else(|| QAParseError {
                    message: "simulate --scope requires Entity=N".to_owned(),
                    line,
                })?;
                let (entity, slots) = value.split_once('=').ok_or_else(|| QAParseError {
                    message: format!("invalid simulation scope '{value}', expected Entity=N"),
                    line,
                })?;
                request.scopes.push((
                    entity.to_owned(),
                    parse_usize(slots, "scope slot count", line)?,
                ));
                index += 2;
            }
            "--system" => {
                let value = tokens.get(index + 1).ok_or_else(|| QAParseError {
                    message: "simulate --system requires a system name".to_owned(),
                    line,
                })?;
                request.system = Some((*value).to_owned());
                index += 2;
            }
            other => {
                return Err(QAParseError {
                    message: format!("unknown simulate option '{other}'"),
                    line,
                });
            }
        }
    }
    Ok(QAStatement::Simulate(request))
}

fn parse_show_artifact(tokens: &[&str], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 2 || tokens[0] != "artifact" {
        return Err(QAParseError {
            message: "expected: show artifact <selector>".to_owned(),
            line,
        });
    }
    Ok(QAStatement::ShowArtifact(tokens[1].to_owned()))
}

fn parse_draw_artifact(tokens: &[&str], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 2 || tokens[0] != "artifact" {
        return Err(QAParseError {
            message: "expected: draw artifact <selector>".to_owned(),
            line,
        });
    }
    Ok(QAStatement::DrawArtifact(tokens[1].to_owned()))
}

fn parse_state_artifact(tokens: &[&str], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 3 || tokens[0] != "artifact" {
        return Err(QAParseError {
            message: "expected: state artifact <selector> <index>".to_owned(),
            line,
        });
    }
    Ok(QAStatement::StateArtifact {
        selector: tokens[1].to_owned(),
        index: parse_usize(tokens[2], "state index", line)?,
    })
}

fn parse_diff_artifact(tokens: &[&str], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 4 || tokens[0] != "artifact" {
        return Err(QAParseError {
            message: "expected: diff artifact <selector> <from> <to>".to_owned(),
            line,
        });
    }
    Ok(QAStatement::DiffArtifact {
        selector: tokens[1].to_owned(),
        from: parse_usize(tokens[2], "from state index", line)?,
        to: parse_usize(tokens[3], "to state index", line)?,
    })
}

fn parse_export_artifact(tokens: &[&str], line: usize) -> Result<QAStatement, QAParseError> {
    if tokens.len() != 3 || tokens[0] != "artifact" {
        return Err(QAParseError {
            message: "expected: export artifact <selector> <format>".to_owned(),
            line,
        });
    }
    Ok(QAStatement::ExportArtifact {
        selector: tokens[1].to_owned(),
        format: tokens[2].to_owned(),
    })
}

fn parse_usize(token: &str, label: &str, line: usize) -> Result<usize, QAParseError> {
    token.parse::<usize>().map_err(|_| QAParseError {
        message: format!("invalid {label} '{token}'"),
        line,
    })
}

/// Parse a `load "path"` statement.
fn parse_load(input: &str, line: usize) -> Result<QAStatement, QAParseError> {
    // Extract the path from: load "path/to/specs"
    let rest = input.trim_start_matches("load").trim();
    if let Some(path) = rest.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        Ok(QAStatement::Load(path.to_owned()))
    } else {
        Err(QAParseError {
            message: "load requires a quoted path: load \"path/to/specs\"".to_owned(),
            line,
        })
    }
}

/// Parse a query from tokens (after the verb).
fn parse_query(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    if tokens.is_empty() {
        return Err(QAParseError {
            message: "expected a query after ask/explain/assert".to_owned(),
            line,
        });
    }

    match tokens[0] {
        // Negation
        "not" => {
            let inner = parse_query(&tokens[1..], line)?;
            Ok(Query::Not(Box::new(inner)))
        }

        // Discovery queries (no arguments)
        "entities" => Ok(Query::Entities),
        "systems" => Ok(Query::Systems),
        "types" => Ok(Query::Types),

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
                return Err(QAParseError {
                    message: "deadlock requires a system name".to_owned(),
                    line,
                });
            }
            Ok(Query::Deadlock {
                system: tokens[1].to_owned(),
            })
        }

        // Temporal assertions (delegate to Abide expression)
        "always" => {
            let expr_str = tokens[1..].join(" ");
            Ok(Query::AlwaysExpr(expr_str))
        }
        "eventually" => {
            let expr_str = tokens[1..].join(" ");
            Ok(Query::EventuallyExpr(expr_str))
        }

        other => Err(QAParseError {
            message: format!(
                "unknown query type '{other}'. Expected: reachable, path, terminal, initial, \
                 cycles, transitions, entities, systems, types, invariants, contracts, \
                 events, match-coverage, cross-calls, updates, deadlock, always, eventually, not"
            ),
            line,
        }),
    }
}

/// Parse `E.field` from tokens. Returns `(entity, field)`.
fn parse_entity_field(tokens: &[&str], line: usize) -> Result<(String, String), QAParseError> {
    if tokens.is_empty() {
        return Err(QAParseError {
            message: "expected E.field".to_owned(),
            line,
        });
    }
    split_dot(tokens[0], line)
}

/// Split `E.field` into `(entity, field)`.
fn split_dot(s: &str, line: usize) -> Result<(String, String), QAParseError> {
    if let Some((entity, field)) = s.split_once('.') {
        Ok((entity.to_owned(), field.to_owned()))
    } else {
        Err(QAParseError {
            message: format!("expected E.field (dot-separated), got '{s}'"),
            line,
        })
    }
}

/// Parse `reachable E.field -> @State`
fn parse_reachable(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    // reachable E.field -> @State
    if tokens.len() < 3 || tokens[1] != "->" {
        return Err(QAParseError {
            message: "expected: reachable E.field -> @State".to_owned(),
            line,
        });
    }
    let (entity, field) = split_dot(tokens[0], line)?;
    let state = strip_at(tokens[2]);
    Ok(Query::Reachable {
        entity,
        field,
        state,
    })
}

/// Parse `path E.field @From -> @To`
fn parse_path(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    // path E.field @From -> @To
    if tokens.len() < 4 || tokens[2] != "->" {
        return Err(QAParseError {
            message: "expected: path E.field @From -> @To".to_owned(),
            line,
        });
    }
    let (entity, field) = split_dot(tokens[0], line)?;
    let from = strip_at(tokens[1]);
    let to = strip_at(tokens[3]);
    Ok(Query::Path {
        entity,
        field,
        from,
        to,
    })
}

/// Parse `transitions from E.field == @State`
fn parse_transitions(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    // transitions from E.field == @State
    if tokens.len() < 4 || tokens[0] != "from" || tokens[2] != "==" {
        return Err(QAParseError {
            message: "expected: transitions from E.field == @State".to_owned(),
            line,
        });
    }
    let (entity, field) = split_dot(tokens[1], line)?;
    let state = strip_at(tokens[3]);
    Ok(Query::Transitions {
        entity,
        field,
        state,
    })
}

/// dispatch `transitions from...` (the existing
/// state-graph query) vs `transitions of E::field` (the new fsm
/// declaration query).
fn parse_transitions_or_of(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    match tokens.first().copied() {
        Some("of") => {
            if tokens.len() < 2 {
                return Err(QAParseError {
                    message: "expected: transitions of E::field".to_owned(),
                    line,
                });
            }
            let (entity, field) = split_double_colon(tokens[1], line)?;
            Ok(Query::FsmTransitions { entity, field })
        }
        Some("from") => parse_transitions(tokens, line),
        _ => Err(QAParseError {
            message: "expected: transitions from E.field == @State, or \
                      transitions of E::field"
                .to_owned(),
            line,
        }),
    }
}

/// dispatch `terminal E.field` (the existing
/// state-graph query) vs `terminal states of E::field` (the new fsm
/// declaration query).
fn parse_terminal_or_states(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    if matches!(tokens.first().copied(), Some("states")) {
        // `terminal states of E::field`
        if tokens.len() < 3 || tokens[1] != "of" {
            return Err(QAParseError {
                message: "expected: terminal states of E::field".to_owned(),
                line,
            });
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
fn split_double_colon(s: &str, line: usize) -> Result<(String, String), QAParseError> {
    if let Some((entity, field)) = s.split_once("::") {
        Ok((entity.to_owned(), field.to_owned()))
    } else {
        Err(QAParseError {
            message: format!("expected E::field (double-colon-separated), got '{s}'"),
            line,
        })
    }
}

/// Parse `updates on E.field @From -> @To`
fn parse_updates(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    // updates on E.field @From -> @To
    if tokens.len() < 5 || tokens[0] != "on" || tokens[3] != "->" {
        return Err(QAParseError {
            message: "expected: updates on E.field @From -> @To".to_owned(),
            line,
        });
    }
    let (entity, field) = split_dot(tokens[1], line)?;
    let from = strip_at(tokens[2]);
    let to = strip_at(tokens[4]);
    Ok(Query::Updates {
        entity,
        field,
        from,
        to,
    })
}

/// Parse `events on E.field`
fn parse_events(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    if tokens.len() < 2 || tokens[0] != "on" {
        return Err(QAParseError {
            message: "expected: events on E.field".to_owned(),
            line,
        });
    }
    let (entity, field) = split_dot(tokens[1], line)?;
    Ok(Query::Events { entity, field })
}

/// Parse `invariants on E`
fn parse_on_entity(tokens: &[&str], line: usize) -> Result<String, QAParseError> {
    if tokens.len() < 2 || tokens[0] != "on" {
        return Err(QAParseError {
            message: "expected: ... on EntityName".to_owned(),
            line,
        });
    }
    Ok(tokens[1].to_owned())
}

/// Parse `contracts on E.action`
fn parse_contracts(tokens: &[&str], line: usize) -> Result<Query, QAParseError> {
    if tokens.len() < 2 || tokens[0] != "on" {
        return Err(QAParseError {
            message: "expected: contracts on E.action".to_owned(),
            line,
        });
    }
    let (entity, action) = split_dot(tokens[1], line)?;
    Ok(Query::Contracts { entity, action })
}

/// Parse `cross-calls from System`
fn parse_from_system(tokens: &[&str], line: usize) -> Result<String, QAParseError> {
    if tokens.len() < 2 || tokens[0] != "from" {
        return Err(QAParseError {
            message: "expected: ... from SystemName".to_owned(),
            line,
        });
    }
    Ok(tokens[1].to_owned())
}

/// Parse block-form: `ask { for e, f, s where pred(e, f, s) select e, f, s }`
fn parse_block_ask(input: &str, line: usize) -> Result<QAStatement, QAParseError> {
    // Strip "ask {" prefix and "}" suffix
    let inner = input
        .trim_start_matches("ask")
        .trim()
        .strip_prefix('{')
        .and_then(|s| s.strip_suffix('}'))
        .map(str::trim);

    let Some(inner) = inner else {
        return Err(QAParseError {
            message: "block query must be: ask { for ... select ... }".to_owned(),
            line,
        });
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
            QAStatement::Assert(Query::AlwaysExpr(expr)) => {
                assert!(expr.contains("all o: Order"));
            }
            other => panic!("expected Assert(AlwaysExpr), got {other:?}"),
        }
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
    fn parse_error_missing_path() {
        let result = parse_qa("load commerce/");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("quoted path"));
    }

    #[test]
    fn parse_error_missing_dot() {
        let result = parse_qa("ask terminal Order");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("dot-separated"));
    }
}
