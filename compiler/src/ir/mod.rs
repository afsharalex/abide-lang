//! Core IR: lowering from elaborated AST and JSON emission.

pub mod lower;
pub mod types;

use crate::elab::types::ElabResult;
use types::IRProgram;

/// Lower an elaborated result to the Core IR.
pub fn lower(result: &ElabResult) -> IRProgram {
    lower::lower(result)
}

/// Emit an IR program as pretty-printed JSON.
pub fn emit_json(program: &IRProgram) -> String {
    serde_json::to_string_pretty(program).expect("IR serialization should not fail")
}
