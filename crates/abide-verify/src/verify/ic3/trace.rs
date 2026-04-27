use super::*;

/// Build column layout for system-level trace extraction.
pub(super) fn build_system_columns(
    entities: &[&IREntity],
    slots_per_entity: &HashMap<String, usize>,
) -> Vec<TraceColumn> {
    let mut columns = Vec::new();
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            let ent_label = if n_slots > 1 {
                format!("{}[{}]", entity.name, slot)
            } else {
                entity.name.clone()
            };
            for (fi, f) in entity.fields.iter().enumerate() {
                columns.push((ent_label.clone(), f.name.clone(), fi));
            }
            columns.push((ent_label, "active".to_owned(), usize::MAX));
        }
    }
    columns
}

/// Build column layout for multi-slot single-entity trace extraction.
pub(super) fn build_multi_slot_columns(entity: &IREntity, n_slots: usize) -> Vec<TraceColumn> {
    let mut columns = Vec::new();
    for slot in 0..n_slots {
        let ent_label = if n_slots > 1 {
            format!("{}[{}]", entity.name, slot)
        } else {
            entity.name.clone()
        };
        for (fi, f) in entity.fields.iter().enumerate() {
            columns.push((ent_label.clone(), f.name.clone(), fi));
        }
        columns.push((ent_label, "active".to_owned(), usize::MAX));
    }
    columns
}

// ── S-expression parser for Z3 answer derivation ────────────────────

/// A minimal s-expression token.
#[derive(Debug, Clone, PartialEq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Tokenize an s-expression string into a tree.
///
/// Handles nested parentheses, atoms (identifiers, numbers, booleans),
/// and negative literals like `(- 1)`.
fn parse_sexpr(input: &str) -> Option<SExpr> {
    let tokens = tokenize_sexpr(input);
    let mut pos = 0;
    let result = parse_sexpr_tokens(&tokens, &mut pos)?;
    // Reject trailing garbage — all tokens must be consumed
    if pos != tokens.len() {
        return None;
    }
    Some(result)
}

fn tokenize_sexpr(input: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else if c == '(' {
            tokens.push("(".to_owned());
            chars.next();
        } else if c == ')' {
            tokens.push(")".to_owned());
            chars.next();
        } else {
            // Atom: collect until whitespace or paren
            let mut atom = String::new();
            while let Some(&ch) = chars.peek() {
                if ch.is_whitespace() || ch == '(' || ch == ')' {
                    break;
                }
                atom.push(ch);
                chars.next();
            }
            if !atom.is_empty() {
                tokens.push(atom);
            }
        }
    }
    tokens
}

fn parse_sexpr_tokens(tokens: &[String], pos: &mut usize) -> Option<SExpr> {
    if *pos >= tokens.len() {
        return None;
    }
    if tokens[*pos] == ")" {
        // Unmatched closing paren — malformed input
        return None;
    }
    if tokens[*pos] == "(" {
        *pos += 1;
        let mut children = Vec::new();
        while *pos < tokens.len() && tokens[*pos] != ")" {
            let child = parse_sexpr_tokens(tokens, pos)?;
            children.push(child);
        }
        if *pos >= tokens.len() {
            // Unclosed paren — malformed input
            return None;
        }
        *pos += 1; // consume ')'
        Some(SExpr::List(children))
    } else {
        let atom = tokens[*pos].clone();
        *pos += 1;
        Some(SExpr::Atom(atom))
    }
}

/// Check if an s-expression atom is a ground value (integer, boolean, or negative literal).
fn is_ground_value(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(s) => {
            s == "true"
                || s == "false"
                || s.chars().next().is_some_and(|c| c.is_ascii_digit())
                || (s.starts_with('-') && s.len() > 1 && s[1..].chars().all(|c| c.is_ascii_digit()))
        }
        SExpr::List(children) => match children.first() {
            // (- X) — negation of a ground value
            Some(SExpr::Atom(op)) if op == "-" && children.len() == 2 => {
                is_ground_value(&children[1])
            }
            // (/ X Y) — rational: both operands must be ground
            Some(SExpr::Atom(op)) if op == "/" && children.len() == 3 => {
                is_ground_value(&children[1]) && is_ground_value(&children[2])
            }
            _ => false,
        },
    }
}

/// Convert an s-expression value to a display string.
///
/// Recurses into nested forms: `(- (/ 1 2))` → `"-1/2"`.
fn sexpr_value_to_string(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(children) => match children.first() {
            // (- X) → "-{X}"
            Some(SExpr::Atom(op)) if op == "-" && children.len() == 2 => {
                format!("-{}", sexpr_value_to_string(&children[1]))
            }
            // (/ X Y) → "{X}/{Y}"
            Some(SExpr::Atom(op)) if op == "/" && children.len() == 3 => {
                format!(
                    "{}/{}",
                    sexpr_value_to_string(&children[1]),
                    sexpr_value_to_string(&children[2])
                )
            }
            _ => format!("{expr:?}"),
        },
    }
}

/// Extract ground `(State v1 v2... vN)` applications from the derivation tree.
///
/// Walks the s-expression tree depth-first (children before parent). Spacer's
/// derivation nests earlier states deeper: the initial state is the innermost
/// `(asserted (State...))`, each `hyper-res` step produces the next state as
/// its conclusion (last child). Depth-first traversal therefore yields states
/// in chronological order for linear derivations.
///
/// **Limitation:** If the derivation has branches (e.g., multiple independent
/// rule applications merged), states from different branches may interleave.
/// Our CHC encoding produces linear chains (each rule takes one State and
/// produces one State), so this is not expected in practice.
fn collect_ground_states(expr: &SExpr, n_cols: usize, out: &mut Vec<Vec<SExpr>>) {
    if let SExpr::List(children) = expr {
        // Recurse into children first (depth-first = derivation order)
        for child in children {
            collect_ground_states(child, n_cols, out);
        }

        // Check if this is (State v1 v2... vN) with exactly n_cols ground args
        if children.len() == n_cols + 1 {
            if let SExpr::Atom(head) = &children[0] {
                if head == "State" {
                    let args = &children[1..];
                    if args.iter().all(is_ground_value) {
                        out.push(args.to_vec());
                    }
                }
            }
        }
    }
}

/// Parse the Z3 Spacer answer into IC3 trace steps.
///
/// Uses proper s-expression parsing to handle nested terms like `(- 1)`.
/// Extracts ground State applications in derivation order (depth-first).
pub(super) fn parse_state_snapshots(answer: &str, columns: &[TraceColumn]) -> Vec<Ic3TraceStep> {
    let n_cols = columns.len();
    if n_cols == 0 {
        return Vec::new();
    }

    let Some(tree) = parse_sexpr(answer) else {
        return Vec::new();
    };

    let mut ground_states: Vec<Vec<SExpr>> = Vec::new();
    collect_ground_states(&tree, n_cols, &mut ground_states);

    // Deduplicate consecutive identical states (stutter rule may repeat)
    ground_states.dedup_by(|a, b| {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(x, y)| sexpr_value_to_string(x) == sexpr_value_to_string(y))
    });

    let mut steps = Vec::new();
    for (step_idx, state_vals) in ground_states.iter().enumerate() {
        let mut assignments = Vec::new();
        for (i, val) in state_vals.iter().enumerate() {
            let (ref ent, ref field, fi) = columns[i];
            if fi == usize::MAX {
                continue; // active flag
            }
            // Check if entity slot is active
            let active_col =
                (0..n_cols).find(|&j| columns[j].0 == *ent && columns[j].2 == usize::MAX && j > i);
            let is_active = active_col
                .and_then(|j| state_vals.get(j))
                .is_some_and(|v| matches!(v, SExpr::Atom(s) if s == "true"));
            if is_active {
                assignments.push((ent.clone(), field.clone(), sexpr_value_to_string(val)));
            }
        }
        if !assignments.is_empty() {
            steps.push(Ic3TraceStep {
                step: step_idx,
                assignments,
            });
        }
    }

    steps
}
