//! Verification backend — connects Abide IR to Z3.
//!
//! Architecture:
//! - `smt`: Z3 value types and sort mapping
//! - `context`: `VerifyContext` (variant IDs, field metadata, entity pool info)
//! - `encode`: IR → Z3 term encoding (expressions, actions, events)

pub mod context;
pub mod encode;
pub mod smt;

use crate::ir::types::IRProgram;

// ── Verification results ────────────────────────────────────────────

/// Result of checking a single verification target.
#[derive(Debug)]
pub enum VerificationResult {
    /// Property proved inductively (unbounded, all sizes).
    Proved {
        name: String,
        method: String,
        time_ms: u64,
    },
    /// Property checked to a bounded depth (no counterexample found).
    Checked {
        name: String,
        depth: usize,
        time_ms: u64,
    },
    /// Counterexample found — a trace of events that violates the property.
    Counterexample { name: String, trace: Vec<TraceStep> },
    /// Scene passed — the scenario is satisfiable and assertions hold.
    ScenePass { name: String, time_ms: u64 },
    /// Scene failed — the scenario is unsatisfiable or assertions violated.
    SceneFail { name: String, reason: String },
    /// Could not prove automatically — needs manual proof.
    Unprovable { name: String, hint: String },
}

/// A single step in a counterexample trace.
#[derive(Debug)]
pub struct TraceStep {
    pub step: usize,
    pub event: Option<String>,
    pub assignments: Vec<(String, String, String)>, // (entity, field, value)
}

// ── Top-level verification entry point ──────────────────────────────

/// Verify all targets in an IR program.
///
/// Processes verify blocks, scenes, and theorems.
/// Returns one result per target.
pub fn verify_all(_ir: &IRProgram) -> Vec<VerificationResult> {
    // TODO: Phase 3+ — wire up BMC, scenes, induction
    Vec::new()
}
