//! Shared completion candidates for the QA command surface.
//!
//! These are grammar-level candidates used by hosts such as the REPL
//! and LSP. Model-aware completions live in the host for now because
//! they depend on loaded source state.

/// Top-level QA commands accepted by the QA parser.
pub const QA_COMMANDS: &[&str] = &[
    "abide",
    "ask",
    "assert",
    "artifacts",
    "diff",
    "draw",
    "explore",
    "explain",
    "export",
    "load",
    "show",
    "simulate",
    "state",
    "verify",
];

/// Query names accepted after `ask`, `explain`, `assert`, or `not`.
pub const QA_QUERY_SUBCOMMANDS: &[&str] = &[
    "always",
    "contracts",
    "cross-calls",
    "cycles",
    "deadlock",
    "entities",
    "events",
    "eventually",
    "fsms",
    "initial",
    "interfaces",
    "invariants",
    "match-coverage",
    "not",
    "path",
    "reachable",
    "systems",
    "terminal",
    "transitions",
    "types",
    "updates",
];

/// Returns top-level QA command candidates as owned strings for hosts
/// whose completion APIs own suggestion values.
#[must_use]
pub fn qa_command_candidates() -> Vec<String> {
    QA_COMMANDS
        .iter()
        .map(std::string::ToString::to_string)
        .collect()
}

/// Returns QA query subcommand candidates as owned strings for hosts
/// whose completion APIs own suggestion values.
#[must_use]
pub fn qa_query_subcommand_candidates() -> Vec<String> {
    QA_QUERY_SUBCOMMANDS
        .iter()
        .map(std::string::ToString::to_string)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn qa_command_candidates_include_current_parser_commands() {
        for command in [
            "abide",
            "ask",
            "assert",
            "load",
            "verify",
            "simulate",
            "explore",
            "artifacts",
            "show",
            "draw",
            "state",
            "diff",
            "export",
        ] {
            assert!(
                QA_COMMANDS.contains(&command),
                "expected QA command candidate `{command}`"
            );
        }
    }

    #[test]
    fn qa_query_subcommand_candidates_include_current_parser_queries() {
        for subcommand in [
            "reachable",
            "terminal",
            "initial",
            "cycles",
            "transitions",
            "entities",
            "systems",
            "types",
            "interfaces",
            "invariants",
            "contracts",
            "cross-calls",
            "deadlock",
            "always",
            "eventually",
            "not",
            "path",
            "events",
            "match-coverage",
            "updates",
            "fsms",
        ] {
            assert!(
                QA_QUERY_SUBCOMMANDS.contains(&subcommand),
                "expected QA query subcommand candidate `{subcommand}`"
            );
        }
    }
}
