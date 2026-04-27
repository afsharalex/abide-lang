//! QA output formatting — human-readable and machine-readable output.

use super::exec::{QueryResult, TransitionInfo, Verb};

/// Format a QA result for human-readable terminal output.
pub fn format_result(verb: Verb, result: &QueryResult) -> String {
    match result {
        QueryResult::Bool(b) => {
            if verb == Verb::Assert {
                if *b {
                    "PASS".to_owned()
                } else {
                    "FAIL".to_owned()
                }
            } else {
                b.to_string()
            }
        }
        QueryResult::BoolWithMode { value, mode } => {
            if verb == Verb::Assert {
                if *value {
                    format!("PASS [{mode}]")
                } else {
                    format!("FAIL [{mode}]")
                }
            } else {
                format!("{value} [{mode}]")
            }
        }
        QueryResult::StateSet(states) => {
            if states.is_empty() {
                "(none)".to_owned()
            } else {
                states
                    .iter()
                    .map(|s| format!("@{s}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            }
        }
        QueryResult::Path(steps) => {
            if steps.is_empty() {
                "(no path)".to_owned()
            } else {
                format_path(steps)
            }
        }
        QueryResult::NameList(names) => {
            if names.is_empty() {
                "(none)".to_owned()
            } else {
                names.join(", ")
            }
        }
        QueryResult::Transitions(transitions) => {
            if transitions.is_empty() {
                "(none)".to_owned()
            } else {
                format_transitions(transitions)
            }
        }
        QueryResult::Table { columns, rows } => format_table(columns, rows),
        QueryResult::Error(msg) => format!("error: {msg}"),
    }
}

/// Format a path as `@From -> action -> @To -> action -> @Final`
fn format_path(steps: &[(String, String)]) -> String {
    let mut parts = Vec::new();
    if let Some((action, target)) = steps.first() {
        // We don't have the starting state in the path, so start from the first action
        parts.push(format!("{action} -> @{target}"));
    }
    for (action, target) in steps.iter().skip(1) {
        parts.push(format!("{action} -> @{target}"));
    }
    parts.join(" -> ")
}

/// Format transition edges.
fn format_transitions(transitions: &[TransitionInfo]) -> String {
    transitions
        .iter()
        .map(|t| format!("@{} -> {} -> @{}", t.from, t.action, t.to))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Format a table with aligned columns.
fn format_table(columns: &[String], rows: &[Vec<String>]) -> String {
    if rows.is_empty() {
        return "(no results)".to_owned();
    }

    // Calculate column widths
    let mut widths: Vec<usize> = columns.iter().map(String::len).collect();
    for row in rows {
        for (i, cell) in row.iter().enumerate() {
            if i < widths.len() && cell.len() > widths[i] {
                widths[i] = cell.len();
            }
        }
    }

    let mut output = String::new();

    // Header
    let header: Vec<String> = columns
        .iter()
        .enumerate()
        .map(|(i, col)| format!("{:width$}", col, width = widths[i]))
        .collect();
    output.push_str(&header.join("  "));
    output.push('\n');

    // Separator
    let sep: Vec<String> = widths.iter().map(|w| "-".repeat(*w)).collect();
    output.push_str(&sep.join("  "));
    output.push('\n');

    // Rows
    for row in rows {
        let cells: Vec<String> = row
            .iter()
            .enumerate()
            .map(|(i, cell)| {
                let w = widths.get(i).copied().unwrap_or(cell.len());
                format!("{cell:w$}")
            })
            .collect();
        output.push_str(&cells.join("  "));
        output.push('\n');
    }

    output
}

/// Format a result as JSON (for `--format json`).
pub fn format_result_json(verb: Verb, result: &QueryResult) -> String {
    let verb_str = match verb {
        Verb::Ask => "ask",
        Verb::Explain => "explain",
        Verb::Assert => "assert",
    };

    match result {
        QueryResult::Bool(b) => {
            let status = if verb == Verb::Assert {
                if *b {
                    "pass"
                } else {
                    "fail"
                }
            } else {
                "ok"
            };
            format!("{{\"verb\":\"{verb_str}\",\"status\":\"{status}\",\"value\":{b}}}")
        }
        QueryResult::BoolWithMode { value, mode } => {
            let status = if verb == Verb::Assert {
                if *value {
                    "pass"
                } else {
                    "fail"
                }
            } else {
                "ok"
            };
            format!(
                "{{\"verb\":\"{verb_str}\",\"status\":\"{status}\",\"value\":{value},\"mode\":\"{mode}\"}}"
            )
        }
        QueryResult::StateSet(states) => {
            let arr: Vec<String> = states.iter().map(|s| format!("\"{s}\"")).collect();
            format!(
                "{{\"verb\":\"{verb_str}\",\"status\":\"ok\",\"states\":[{}]}}",
                arr.join(",")
            )
        }
        QueryResult::NameList(names) => {
            let arr: Vec<String> = names.iter().map(|n| format!("\"{n}\"")).collect();
            format!(
                "{{\"verb\":\"{verb_str}\",\"status\":\"ok\",\"names\":[{}]}}",
                arr.join(",")
            )
        }
        QueryResult::Path(steps) => {
            let arr: Vec<String> = steps
                .iter()
                .map(|(a, s)| format!("{{\"action\":\"{a}\",\"state\":\"{s}\"}}"))
                .collect();
            format!(
                "{{\"verb\":\"{verb_str}\",\"status\":\"ok\",\"path\":[{}]}}",
                arr.join(",")
            )
        }
        QueryResult::Error(msg) => {
            format!("{{\"verb\":\"{verb_str}\",\"status\":\"error\",\"message\":\"{msg}\"}}")
        }
        _ => format!("{{\"verb\":\"{verb_str}\",\"status\":\"ok\"}}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fmt_bool_ask() {
        assert_eq!(format_result(Verb::Ask, &QueryResult::Bool(true)), "true");
        assert_eq!(format_result(Verb::Ask, &QueryResult::Bool(false)), "false");
    }

    #[test]
    fn fmt_bool_assert() {
        assert_eq!(
            format_result(Verb::Assert, &QueryResult::Bool(true)),
            "PASS"
        );
        assert_eq!(
            format_result(Verb::Assert, &QueryResult::Bool(false)),
            "FAIL"
        );
    }

    #[test]
    fn fmt_state_set() {
        let result = QueryResult::StateSet(vec!["Shipped".into(), "Cancelled".into()]);
        let output = format_result(Verb::Ask, &result);
        assert!(output.contains("@Shipped"));
        assert!(output.contains("@Cancelled"));
    }

    #[test]
    fn fmt_path() {
        let result = QueryResult::Path(vec![
            ("submit".into(), "Confirmed".into()),
            ("ship".into(), "Shipped".into()),
        ]);
        let output = format_result(Verb::Ask, &result);
        assert!(output.contains("submit"));
        assert!(output.contains("@Confirmed"));
        assert!(output.contains("ship"));
        assert!(output.contains("@Shipped"));
    }

    #[test]
    fn fmt_empty_path() {
        let output = format_result(Verb::Ask, &QueryResult::Path(vec![]));
        assert_eq!(output, "(no path)");
    }

    #[test]
    fn fmt_name_list() {
        let result = QueryResult::NameList(vec!["Order".into(), "Payment".into()]);
        let output = format_result(Verb::Ask, &result);
        assert!(output.contains("Order"));
        assert!(output.contains("Payment"));
    }

    #[test]
    fn fmt_table() {
        let result = QueryResult::Table {
            columns: vec!["entity".into(), "field".into(), "state".into()],
            rows: vec![
                vec!["Order".into(), "status".into(), "Shipped".into()],
                vec!["Order".into(), "status".into(), "Cancelled".into()],
            ],
        };
        let output = format_result(Verb::Ask, &result);
        assert!(output.contains("entity"));
        assert!(output.contains("Shipped"));
        assert!(output.contains("Cancelled"));
    }

    #[test]
    fn fmt_json_bool() {
        let json = format_result_json(Verb::Assert, &QueryResult::Bool(true));
        assert!(json.contains("\"status\":\"pass\""));
        assert!(json.contains("\"value\":true"));
    }

    #[test]
    fn fmt_json_error() {
        let json = format_result_json(Verb::Ask, &QueryResult::Error("not found".into()));
        assert!(json.contains("\"status\":\"error\""));
        assert!(json.contains("not found"));
    }
}
