//! Context-aware tab completion for the Abide REPL.

use reedline::{Completer, Span, Suggestion};

use crate::qa::model::FlowModel;

use super::Mode;

/// Tab completer that adapts to the current REPL mode.
pub struct AbideCompleter {
    mode: Mode,
    /// QA subcommand keywords.
    qa_verbs: Vec<String>,
    qa_subcommands: Vec<String>,
    /// Entity/field/state names from the `FlowModel`.
    model_names: Vec<String>,
    /// Abide definition names (entities, systems, fns, preds, types).
    env_names: Vec<String>,
    /// Entity field names keyed by entity name (for dot-completion).
    entity_fields: Vec<(String, Vec<String>)>,
    /// All enum variant names prefixed with `@` (for @-completion).
    state_atoms: Vec<String>,
    /// Tool commands.
    tool_commands: Vec<String>,
}

impl AbideCompleter {
    pub fn new(mode: Mode, model: Option<&FlowModel>, env_names: &[String]) -> Self {
        let mut model_names = Vec::new();
        let mut entity_fields: Vec<(String, Vec<String>)> = Vec::new();
        let mut state_atoms: Vec<String> = Vec::new();

        if let Some(m) = model {
            model_names.extend(m.entity_names.clone());
            model_names.extend(m.systems.keys().cloned());
            model_names.extend(m.type_names.clone());

            // Collect per-entity field names and state atoms
            let mut fields_by_entity: std::collections::HashMap<String, Vec<String>> =
                std::collections::HashMap::new();
            for ((entity, field), sg) in &m.state_graphs {
                model_names.push(format!("{entity}.{field}"));
                fields_by_entity
                    .entry(entity.clone())
                    .or_default()
                    .push(field.clone());
                for state in &sg.states {
                    let atom = format!("@{state}");
                    if !state_atoms.contains(&atom) {
                        state_atoms.push(atom);
                    }
                }
            }
            for (entity, fields) in fields_by_entity {
                entity_fields.push((entity, fields));
            }
        }

        Self {
            mode,
            qa_verbs: vec![
                "ask".into(),
                "explain".into(),
                "assert".into(),
                "load".into(),
            ],
            qa_subcommands: vec![
                "reachable".into(),
                "terminal".into(),
                "initial".into(),
                "cycles".into(),
                "transitions".into(),
                "entities".into(),
                "systems".into(),
                "types".into(),
                "invariants".into(),
                "contracts".into(),
                "cross-calls".into(),
                "deadlock".into(),
                "always".into(),
                "eventually".into(),
                "not".into(),
                "path".into(),
                "events".into(),
                "match-coverage".into(),
                "updates".into(),
            ],
            model_names,
            env_names: env_names.to_vec(),
            entity_fields,
            state_atoms,
            tool_commands: vec![
                "/help".into(),
                "/quit".into(),
                "/qa".into(),
                "/abide".into(),
                "/reload".into(),
                "/verify".into(),
                "/run".into(),
                "/simulate".into(),
                "/artifacts".into(),
                "/show".into(),
                "/draw".into(),
                "/state".into(),
                "/diff".into(),
                "/export".into(),
                "/schema".into(),
            ],
        }
    }
}

impl Completer for AbideCompleter {
    fn complete(&mut self, line: &str, pos: usize) -> Vec<Suggestion> {
        let (start, token) = current_token(line, pos);

        // Tool commands: /...
        if token.starts_with('/') {
            return suggest_from(&self.tool_commands, token, start);
        }

        // State atom completion: @... → enum variant names
        if token.starts_with('@') {
            return suggest_from(&self.state_atoms, token, start);
        }

        // Dot-completion: Entity.field or var.field
        if let Some(dot_pos) = token.rfind('.') {
            let before_dot = &token[..dot_pos];
            let after_dot = &token[dot_pos + 1..];
            // Find entity fields matching the prefix before the dot
            let field_candidates: Vec<String> = self
                .entity_fields
                .iter()
                .filter(|(entity, _)| entity == before_dot)
                .flat_map(|(_, fields)| fields.iter())
                .filter(|f| f.starts_with(after_dot) && f.as_str() != after_dot)
                .map(|f| format!("{before_dot}.{f}"))
                .collect();
            if !field_candidates.is_empty() {
                return suggest_from(&field_candidates, token, start);
            }
        }

        match self.mode {
            Mode::QA => {
                // First token: complete QA verbs
                if is_first_token(line, pos) {
                    return suggest_from(&self.qa_verbs, token, start);
                }
                // Second token: complete subcommands based on verb
                if is_second_token(line, pos) {
                    return suggest_from(&self.qa_subcommands, token, start);
                }
                // Remaining tokens: entity/field/state names
                suggest_from(&self.model_names, token, start)
            }
            Mode::Abide => {
                // Complete Abide names + keywords
                let mut candidates = self.env_names.clone();
                candidates.extend_from_slice(&[
                    "entity".into(),
                    "system".into(),
                    "enum".into(),
                    "struct".into(),
                    "type".into(),
                    "fn".into(),
                    "pred".into(),
                    "prop".into(),
                    "verify".into(),
                    "scene".into(),
                    "theorem".into(),
                    "axiom".into(),
                    "lemma".into(),
                    "const".into(),
                    "module".into(),
                    "use".into(),
                    "include".into(),
                    "pub".into(),
                ]);
                suggest_from(&candidates, token, start)
            }
        }
    }
}

/// Extract the current token being typed and its start position.
fn current_token(line: &str, pos: usize) -> (usize, &str) {
    let before = &line[..pos];
    // Token boundary: whitespace, but NOT dots or @ (those are part of the token)
    let token_start = before
        .rfind(|c: char| c.is_whitespace())
        .map_or(0, |i| i + 1);
    (token_start, &before[token_start..])
}

/// Check if cursor is at the first token position.
fn is_first_token(line: &str, pos: usize) -> bool {
    let before = line[..pos].trim_start();
    !before.contains(' ')
}

/// Check if cursor is at the second token position.
fn is_second_token(line: &str, pos: usize) -> bool {
    let before = line[..pos].trim_start();
    let spaces: Vec<usize> = before.match_indices(' ').map(|(i, _)| i).collect();
    spaces.len() == 1
}

/// Filter candidates by prefix and create suggestions.
fn suggest_from(candidates: &[String], prefix: &str, start: usize) -> Vec<Suggestion> {
    candidates
        .iter()
        .filter(|c| c.starts_with(prefix) && c.as_str() != prefix)
        .map(|c| Suggestion {
            value: c.clone(),
            description: None,
            style: None,
            extra: None,
            span: Span::new(start, start + prefix.len()),
            append_whitespace: true,
        })
        .collect()
}
