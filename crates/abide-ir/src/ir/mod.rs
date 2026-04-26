//! Core IR: lowering from elaborated AST and JSON emission.

pub mod lower;
pub mod types;

use crate::elab::types::ElabResult;
pub use lower::LowerDiagnostics;
use types::IRProgram;

/// Lower an elaborated result to the Core IR.
pub fn lower(result: &ElabResult) -> (IRProgram, LowerDiagnostics) {
    lower::lower(result)
}

/// Emit an IR program as pretty-printed JSON.
///
/// # Errors
///
/// Returns an error if serde serialization fails (should not happen with
/// well-formed IR, but handled gracefully rather than panicking).
pub fn emit_json(program: &IRProgram) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(program)
}
