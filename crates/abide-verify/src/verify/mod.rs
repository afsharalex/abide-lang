//! Verification backend — connects Abide IR to SMT and CHC backends.
//!
//! Architecture:
//! - `smt`: Z3 value types, sort mapping, collection array support
//! - `context`: `VerifyContext` (variant IDs, field metadata, entity pool info)
//! - `harness`: Multi-slot entity pools, action/event/collection encoding
//! - `chc`: CHC backend routing (separate from ordinary SMT selection)
//! - `ic3`: IC3/PDR via CHC backends (Spacer is the current reference path)
//! - `transition`: backend-neutral transition obligations routed to the current CHC backend
//! - `defenv`: Definition environment for pred/prop/fn expansion
//! - `mod`: Tiered dispatch (`verify_all`), property encoding, counterexample extraction

pub mod chc;
mod collections;
pub mod context;
pub mod defenv;
mod explicit;
pub mod harness;
pub mod ic3;
#[cfg_attr(not(test), allow(dead_code))]
mod ltl;
pub mod smt;
mod sygus;
mod temporal;
#[cfg_attr(not(test), allow(dead_code))]
mod temporal_relational;
pub mod transition;
pub use explicit::{
    explore_verify_state_space, ExplicitStateSpace, ExplicitStateSpaceStoreBound,
    ExplicitStateSpaceTransition,
};
#[allow(clippy::wildcard_imports)]
use temporal::*;
pub use temporal::{export_verify_temporal_formulas, TemporalFormulaExport, VerifyTemporalExport};
mod walkers;
#[allow(clippy::wildcard_imports)]
use walkers::*;
mod scope;
#[allow(clippy::wildcard_imports)]
use scope::*;
mod encode;
#[allow(clippy::wildcard_imports)]
use encode::*;
mod fn_verify;
#[allow(clippy::wildcard_imports)]
use fn_verify::*;
mod property;
#[allow(clippy::wildcard_imports)]
use property::*;
#[cfg_attr(not(test), allow(dead_code))]
mod relation_sat;
mod theorem;
#[allow(clippy::wildcard_imports)]
use theorem::*;
mod scene;
#[allow(clippy::wildcard_imports)]
use scene::*;
mod obligation;
mod relational;
pub mod solver;

pub use obligation::{
    analyze_verification_dependency_graph, classify_verification_parallel_lanes,
    collect_verification_obligations, execute_verification_lane_plan,
    execute_verification_lane_plan_with_events, schedule_verification_obligations,
    VerificationConcurrencyBlocker, VerificationDependencyEdge, VerificationDependencyGraph,
    VerificationDependencyKind, VerificationExecutionMode, VerificationExecutionOutcome,
    VerificationExecutionResult, VerificationLaneConcurrency, VerificationObligation,
    VerificationObligationDependency, VerificationObligationId, VerificationObligationKind,
    VerificationObligationResultKind, VerificationParallelLane, VerificationParallelLanePlan,
    VerificationSchedule, VerificationScheduleStep, VerificationSchedulerEvent,
    VerificationSchedulerPolicy, VerificationSchedulingMode, VerificationTrustPolicy,
};

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;
use std::str::FromStr;
use std::thread;
use std::time::{Duration, Instant};

use abide_core::diagnostic::Diagnostic;
use abide_witness::{op, rel, Countermodel, EvidenceEnvelope, ProofArtifactRef, WitnessEnvelope};
use serde::{Deserialize, Serialize};

use self::smt::{AbideSolver, Bool, SatResult};

use crate::ir::types::{
    IRAction, IRAssumptionSet, IRExpr, IRFunction, IRProgram, IRStutterProvenance, IRSystem,
    IRTheorem, IRType, IRVerify, IRVerifySystem,
};

pub use self::chc::ChcSelection;
use self::context::VerifyContext;
use self::harness::{
    create_slot_pool_with_systems, domain_constraints, initial_state_constraints_with_store_ranges,
    store_active_cardinality_constraints, SlotPool,
};
use self::smt::SmtValue;
use self::solver::{
    active_solver_family, is_solver_family_available, set_active_solver_family, SolverFamily,
};
// ── Verification results ────────────────────────────────────────────

/// Per-event fairness analysis for lasso counterexamples.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FairnessStatus {
    /// Event was enabled in the loop AND fired at some loop step.
    EnabledAndFired,
    /// Event was enabled in the loop but NEVER fired — starved.
    EnabledButStarved,
    /// Event was never enabled at any loop step.
    NeverEnabled,
}

/// Weak or strong fairness annotation on a fair event.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FairnessKind {
    /// `assume { fair Sys::cmd }`.
    Weak,
    /// `assume { strong fair Sys::cmd }`.
    Strong,
}

/// Fairness analysis for a single event in a lasso counterexample.
///
/// Attached to liveness counterexamples so users can see *why* a
/// fairness assumption did or did not save the verdict.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FairnessEventAnalysis {
    pub system: String,
    pub event: String,
    pub kind: FairnessKind,
    pub status: FairnessStatus,
}

/// Per-event diagnostic for a deadlocked state.
///
/// One entry per command on the system at the deadlocked state,
/// recording why that command was not enabled (`reason`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockEventDiag {
    pub system: String,
    pub event: String,
    pub reason: String,
}

/// An assumption that a verification verdict depends on.
///
/// Emitted as part of every verification result so users (and Invaria)
/// can audit exactly what trust the verdict relies on. This is a
/// disclosure list, not a minimization: every assumption in scope is
/// listed, including ones the solver did not strictly need. The
/// distinction matters for review.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TrustedAssumption {
    /// Default stuttering assumption.
    DefaultStutter,
    /// Stuttering assumption (`assume { stutter }`).
    Stutter,
    /// No-stutter assumption (`assume { no stutter }`).
    NoStutter,
    /// Weak fairness (`assume { fair Sys::cmd }`).
    WeakFairness { system: String, command: String },
    /// Per-tuple weak fairness for a parameterized command.
    PerTupleWeakFairness { system: String, command: String },
    /// Strong fairness (`assume { strong fair Sys::cmd }`).
    StrongFairness { system: String, command: String },
    /// Per-tuple strong fairness for a parameterized command.
    PerTupleStrongFairness { system: String, command: String },
    /// Lemma conclusion injected via `by L`.
    Lemma { name: String },
    /// Axiom taken as a trusted fact (`axiom name = expr` or `axiom name by "file"`).
    Axiom {
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        proof_artifact: Option<ProofArtifactRef>,
    },
    /// Trusted assumption declared on a reachable extern boundary.
    ExternAssume { external: String, detail: String },
}

/// Build the comprehensive list of assumptions in scope for a verification site.
/// This is disclosure of all assumptions that COULD affect the verdict, not a
/// solver-level trace of which ones were strictly needed. The distinction matters
/// for auditability: the user sees everything they trusted, even if some
/// assumptions were redundant for this particular proof.
pub fn build_assumptions(
    set: &crate::ir::types::IRAssumptionSet,
    by_lemmas: &[String],
) -> Vec<TrustedAssumption> {
    build_assumptions_with_axioms(set, by_lemmas, &[])
}

/// Build assumptions including trusted extern-boundary assumptions reachable
/// from the provided system roots.
pub fn build_assumptions_for_system_scope(
    ir: &crate::ir::types::IRProgram,
    roots: &[String],
    set: &crate::ir::types::IRAssumptionSet,
    by_lemmas: &[String],
) -> Vec<TrustedAssumption> {
    let mut out = build_assumptions(set, by_lemmas);
    out.extend(collect_extern_assumptions(ir, roots));
    out
}

/// Build assumptions including axiom names from the IR program.
pub fn build_assumptions_with_axioms(
    set: &crate::ir::types::IRAssumptionSet,
    by_lemmas: &[String],
    axioms: &[crate::ir::types::IRAxiom],
) -> Vec<TrustedAssumption> {
    let mut out = Vec::new();
    out.push(match (set.stutter, set.stutter_provenance) {
        (true, IRStutterProvenance::Default) => TrustedAssumption::DefaultStutter,
        (true, IRStutterProvenance::ExplicitStutter) => TrustedAssumption::Stutter,
        (false, IRStutterProvenance::ExplicitNoStutter) => TrustedAssumption::NoStutter,
        (true, IRStutterProvenance::ExplicitNoStutter) => TrustedAssumption::Stutter,
        (false, IRStutterProvenance::Default | IRStutterProvenance::ExplicitStutter) => {
            TrustedAssumption::NoStutter
        }
    });
    for wf in &set.weak_fair {
        let is_per_tuple = set.per_tuple.iter().any(|pt| pt == wf);
        out.push(if is_per_tuple {
            TrustedAssumption::PerTupleWeakFairness {
                system: wf.system.clone(),
                command: wf.command.clone(),
            }
        } else {
            TrustedAssumption::WeakFairness {
                system: wf.system.clone(),
                command: wf.command.clone(),
            }
        });
    }
    for sf in &set.strong_fair {
        let is_per_tuple = set.per_tuple.iter().any(|pt| pt == sf);
        out.push(if is_per_tuple {
            TrustedAssumption::PerTupleStrongFairness {
                system: sf.system.clone(),
                command: sf.command.clone(),
            }
        } else {
            TrustedAssumption::StrongFairness {
                system: sf.system.clone(),
                command: sf.command.clone(),
            }
        });
    }
    for per_tuple in &set.per_tuple {
        let already_reported = set.weak_fair.iter().any(|wf| wf == per_tuple)
            || set.strong_fair.iter().any(|sf| sf == per_tuple);
        if !already_reported {
            out.push(TrustedAssumption::PerTupleWeakFairness {
                system: per_tuple.system.clone(),
                command: per_tuple.command.clone(),
            });
        }
    }
    for lemma in by_lemmas {
        out.push(TrustedAssumption::Lemma {
            name: lemma.clone(),
        });
    }
    out.extend(build_axiom_assumptions(axioms));
    out
}

fn build_axiom_assumptions(axioms: &[crate::ir::types::IRAxiom]) -> Vec<TrustedAssumption> {
    axioms
        .iter()
        .map(|axiom| TrustedAssumption::Axiom {
            name: axiom.name.clone(),
            proof_artifact: axiom.by_file.as_deref().and_then(|locator| {
                proof_artifact_ref_for_locator(locator, Some(&axiom.name)).ok()
            }),
        })
        .collect()
}

fn collect_extern_assumptions(
    ir: &crate::ir::types::IRProgram,
    roots: &[String],
) -> Vec<TrustedAssumption> {
    let mut out = Vec::new();
    let mut to_scan = roots.to_vec();
    let mut scanned = HashSet::new();

    while let Some(sys_name) = to_scan.pop() {
        if !scanned.insert(sys_name.clone()) {
            continue;
        }
        let Some(system) = ir.systems.iter().find(|s| s.name == sys_name) else {
            continue;
        };

        if system
            .preds
            .iter()
            .any(|pred| pred.name == "__abide_extern__marker")
        {
            for pred in &system.preds {
                if let Some(command) = pred.name.strip_prefix("__abide_extern_assume_wf__") {
                    out.push(TrustedAssumption::ExternAssume {
                        external: system.name.clone(),
                        detail: format!("WF {command}"),
                    });
                } else if let Some(command) = pred.name.strip_prefix("__abide_extern_assume_sf__") {
                    out.push(TrustedAssumption::ExternAssume {
                        external: system.name.clone(),
                        detail: format!("SF {command}"),
                    });
                } else if let Some(idx) = pred.name.strip_prefix("__abide_extern_assume_expr__") {
                    out.push(TrustedAssumption::ExternAssume {
                        external: system.name.clone(),
                        detail: format!("assume #{idx}"),
                    });
                }
            }
        }

        for step in &system.actions {
            collect_crosscall_systems(&step.body, &mut to_scan);
        }
        for lb in &system.let_bindings {
            if !to_scan.contains(&lb.system_type) {
                to_scan.push(lb.system_type.clone());
            }
        }
    }

    out
}

fn operational_evidence(witness: op::OperationalWitness) -> Result<EvidenceEnvelope, String> {
    let witness = WitnessEnvelope::operational(witness)
        .map_err(|err| format!("operational witness envelope validation failed: {err}"))?;
    EvidenceEnvelope::witness(witness)
        .map_err(|err| format!("operational witness evidence validation failed: {err}"))
}

pub fn replay_counterexample_witness(
    ir: &IRProgram,
    verify_block: &IRVerify,
    witness: &op::OperationalWitness,
) -> CounterexampleReplayReport {
    explicit::replay_counterexample_witness(ir, verify_block, witness)
}

fn relational_evidence(witness: rel::RelationalWitness) -> Result<EvidenceEnvelope, String> {
    let witness = WitnessEnvelope::relational(witness)
        .map_err(|err| format!("relational witness envelope validation failed: {err}"))?;
    EvidenceEnvelope::witness(witness)
        .map_err(|err| format!("relational witness evidence validation failed: {err}"))
}

fn materialize_relational_verify_outcome(
    ir: &IRProgram,
    verify_block: &IRVerify,
    bound: usize,
    outcome: relational::RelationalVerifyOutcome,
) -> VerificationResult {
    match outcome {
        relational::RelationalVerifyOutcome::Checked { time_ms } => VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: bound,
            method: Some("relational RustSAT".to_owned()),
            time_ms,
            assumptions: build_assumptions_for_system_scope(
                ir,
                &verify_block
                    .systems
                    .iter()
                    .map(|s| s.name.clone())
                    .collect::<Vec<_>>(),
                &verify_block.assumption_set,
                &[],
            ),
            backend_diagnostics: vec![],
            span: None,
            file: None,
        },
        relational::RelationalVerifyOutcome::Unknown { hint } => VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint,
            span: if verify_block.asserts.len() == 1 {
                expr_span(&verify_block.asserts[0])
            } else {
                None
            },
            file: None,
        },
        relational::RelationalVerifyOutcome::Counterexample {
            witness,
            witness_error,
        } => {
            let (evidence, evidence_extraction_error) = match witness {
                Some(witness) => match relational_evidence(witness) {
                    Ok(evidence) => (Some(evidence), witness_error),
                    Err(err) => (None, Some(err)),
                },
                None => (None, witness_error),
            };
            VerificationResult::Counterexample {
                name: verify_block.name.clone(),
                evidence,
                replay: None,
                evidence_extraction_error,
                assumptions: build_assumptions_for_system_scope(
                    ir,
                    &verify_block
                        .systems
                        .iter()
                        .map(|s| s.name.clone())
                        .collect::<Vec<_>>(),
                    &verify_block.assumption_set,
                    &[],
                ),
                span: if verify_block.asserts.len() == 1 {
                    expr_span(&verify_block.asserts[0])
                } else {
                    None
                },
                file: None,
            }
        }
    }
}

fn countermodel_evidence(countermodel: Countermodel) -> Result<EvidenceEnvelope, String> {
    EvidenceEnvelope::countermodel(countermodel)
        .map_err(|err| format!("countermodel evidence validation failed: {err}"))
}

/// Result of re-executing a counterexample trace independently to
/// confirm the verifier's verdict.
///
/// The replay protocol is part of DDR-042 Phase 3: every reported
/// counterexample is replayed through the operational simulator (or an
/// equivalent independent engine) and the property is rechecked. A
/// `checked: true, property_violated: true` report is the strongest
/// signal — the violation is observable, not just inferred from a
/// solver model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleReplayReport {
    pub checked: bool,
    pub steps: usize,
    pub property_violated: bool,
    pub engine: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

impl CounterexampleReplayReport {
    fn checked(steps: usize, property_violated: bool, engine: impl Into<String>) -> Self {
        Self {
            checked: true,
            steps,
            property_violated,
            engine: engine.into(),
            error: None,
        }
    }

    fn failed(steps: usize, engine: impl Into<String>, error: impl Into<String>) -> Self {
        Self {
            checked: false,
            steps,
            property_violated: false,
            engine: engine.into(),
            error: Some(error.into()),
        }
    }
}

/// Informational diagnostic attached to a [`VerificationResult`]
/// reporting a backend's outcome at one pipeline phase.
///
/// Carries the verifier phase (`bounded_safety`, `unbounded_safety`,
/// `proof_mode`, …), backend label (`Z3`, `IC3/PDR`, …), severity
/// (`info`/`warn`/`error`), and a human-readable message.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BackendDiagnostic {
    pub phase: String,
    pub backend: String,
    pub severity: String,
    pub message: String,
}

impl BackendDiagnostic {
    fn ic3_unknown(message: String) -> Self {
        Self {
            phase: "unbounded_safety".to_owned(),
            backend: "IC3/PDR".to_owned(),
            severity: "info".to_owned(),
            message,
        }
    }

    fn proof_mode_hint() -> Self {
        Self {
            phase: "proof_mode".to_owned(),
            backend: "verify".to_owned(),
            severity: "info".to_owned(),
            message: "ordinary verify ran bounded/exploration checking; rerun with --ic3 or --unbounded-only to attempt an unbounded proof".to_owned(),
        }
    }
}

/// One verifier verdict.
///
/// This is the top-level result type emitted per verification target
/// (verify/theorem/lemma/scene). Variant selection encodes both the
/// outcome and which pipeline phase produced it.
///
/// Reading the result kind alone is insufficient — the assumptions
/// list inside each variant declares the trust surface, and a
/// `Counterexample` with `replay.property_violated` is stronger than
/// one without (see [`CounterexampleReplayReport`]).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum VerificationResult {
    /// Property proved inductively (unbounded, all sizes).
    Proved {
        name: String,
        method: String,
        time_ms: u64,
        assumptions: Vec<TrustedAssumption>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Property accepted via a trusted proof-side mechanism rather than an
    /// internal automatic proof.
    Admitted {
        name: String,
        reason: String,
        time_ms: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence: Option<EvidenceEnvelope>,
        assumptions: Vec<TrustedAssumption>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Property checked to a bounded depth (no counterexample found).
    Checked {
        name: String,
        depth: usize,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        method: Option<String>,
        time_ms: u64,
        assumptions: Vec<TrustedAssumption>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        backend_diagnostics: Vec<BackendDiagnostic>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Counterexample found.
    ///
    /// For behavioral checks this remains a violating trace, with native
    /// behavioral evidence carried in `evidence`.
    ///
    /// For proof-oriented failures (for example failed lemmas), this may carry
    /// proof-side evidence such as a countermodel instead of a behavior trace.
    Counterexample {
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence: Option<EvidenceEnvelope>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        replay: Option<CounterexampleReplayReport>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence_extraction_error: Option<String>,
        assumptions: Vec<TrustedAssumption>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Scene passed — the scenario is satisfiable and assertions hold.
    ScenePass {
        name: String,
        time_ms: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence: Option<EvidenceEnvelope>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Scene failed — the scenario is unsatisfiable or assertions violated.
    SceneFail {
        name: String,
        reason: String,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Scene could not be decided because the solver returned unknown.
    SceneUnknown {
        name: String,
        reason: String,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Could not prove automatically — needs manual proof.
    Unprovable {
        name: String,
        hint: String,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Function contract (ensures) proved — body satisfies postcondition.
    FnContractProved {
        name: String,
        time_ms: u64,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Function contract admitted — body contains `assume` or `sorry`.
    /// Not a failure (exit code 0), but visually distinct from PROVED.
    FnContractAdmitted {
        name: String,
        reason: String,
        time_ms: u64,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Function contract (ensures) violated — counterexample found.
    FnContractFailed {
        name: String,
        counterexample: Vec<(String, String)>, // (param_name, value)
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Liveness violation — lasso-shaped counterexample (infinite execution).
    /// Native witness evidence carries the behavior; `loop_start` is kept as a
    /// summary field for quick inspection and machine-readable summaries.
    LivenessViolation {
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence: Option<EvidenceEnvelope>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence_extraction_error: Option<String>,
        loop_start: usize,
        fairness_analysis: Vec<FairnessEventAnalysis>,
        assumptions: Vec<TrustedAssumption>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Deadlock — the system reached a state where no events are
    /// enabled and stutter is opted out (per /  /// revised). Reported by direct deadlock detection in BMC paths
    /// where `assumption_set.stutter` is false and the trace can no
    /// longer be extended.
    ///
    /// Native witness evidence carries the behavior up to the deadlocked state.
    /// `step` is the index of the deadlocked state. `reason` is a short
    /// human-readable summary; per-entity diagnostics per are deferred to a
    /// follow-up polish pass.
    Deadlock {
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence: Option<EvidenceEnvelope>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        evidence_extraction_error: Option<String>,
        step: usize,
        reason: String,
        event_diagnostics: Vec<DeadlockEventDiag>,
        assumptions: Vec<TrustedAssumption>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
}

impl VerificationResult {
    /// Attach source location to this result (called by `verify_all` after dispatch).
    ///
    /// Only fills in span/file when the result doesn't already carry a more specific
    /// location (e.g., a per-assertion span set by the internal verification function).
    fn with_source(
        self,
        block_span: Option<crate::span::Span>,
        block_file: Option<String>,
    ) -> Self {
        match self {
            Self::Proved {
                name,
                method,
                time_ms,
                assumptions,
                span,
                file,
            } => Self::Proved {
                name,
                method,
                time_ms,
                assumptions,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Checked {
                name,
                depth,
                method,
                time_ms,
                assumptions,
                backend_diagnostics,
                span,
                file,
            } => Self::Checked {
                name,
                depth,
                method,
                time_ms,
                assumptions,
                backend_diagnostics,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Admitted {
                name,
                reason,
                time_ms,
                evidence,
                assumptions,
                span,
                file,
            } => Self::Admitted {
                name,
                reason,
                time_ms,
                evidence,
                assumptions,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Counterexample {
                name,
                evidence,
                replay,
                evidence_extraction_error,
                assumptions,
                span,
                file,
            } => Self::Counterexample {
                name,
                evidence,
                replay,
                evidence_extraction_error,
                assumptions,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::ScenePass {
                name,
                time_ms,
                evidence,
                span,
                file,
            } => Self::ScenePass {
                name,
                time_ms,
                evidence,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::SceneFail {
                name,
                reason,
                span,
                file,
            } => Self::SceneFail {
                name,
                reason,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::SceneUnknown {
                name,
                reason,
                span,
                file,
            } => Self::SceneUnknown {
                name,
                reason,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Unprovable {
                name,
                hint,
                span,
                file,
            } => Self::Unprovable {
                name,
                hint,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::FnContractProved {
                name,
                time_ms,
                span,
                file,
            } => Self::FnContractProved {
                name,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::FnContractAdmitted {
                name,
                reason,
                time_ms,
                span,
                file,
            } => Self::FnContractAdmitted {
                name,
                reason,
                time_ms,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::FnContractFailed {
                name,
                counterexample,
                span,
                file,
            } => Self::FnContractFailed {
                name,
                counterexample,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::LivenessViolation {
                name,
                evidence,
                evidence_extraction_error,
                loop_start,
                fairness_analysis,
                assumptions,
                span,
                file,
            } => Self::LivenessViolation {
                name,
                evidence,
                evidence_extraction_error,
                loop_start,
                fairness_analysis,
                assumptions,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::Deadlock {
                name,
                evidence,
                evidence_extraction_error,
                step,
                reason,
                event_diagnostics,
                assumptions,
                span,
                file,
            } => Self::Deadlock {
                name,
                evidence,
                evidence_extraction_error,
                step,
                reason,
                event_diagnostics,
                assumptions,
                span: span.or(block_span),
                file: file.or(block_file),
            },
        }
    }

    /// Add axiom assumptions to any result variant that carries assumptions.
    fn with_axioms(mut self, axioms: &[TrustedAssumption]) -> Self {
        if axioms.is_empty() {
            return self;
        }
        match &mut self {
            Self::Proved { assumptions, .. }
            | Self::Admitted { assumptions, .. }
            | Self::Checked { assumptions, .. }
            | Self::Counterexample { assumptions, .. }
            | Self::LivenessViolation { assumptions, .. }
            | Self::Deadlock { assumptions, .. } => {
                assumptions.extend_from_slice(axioms);
            }
            _ => {}
        }
        self
    }

    /// Replace the displayed elapsed time for result variants that carry one.
    fn with_time_ms(mut self, elapsed: u64) -> Self {
        match &mut self {
            Self::Proved { time_ms, .. }
            | Self::Admitted { time_ms, .. }
            | Self::Checked { time_ms, .. }
            | Self::ScenePass { time_ms, .. }
            | Self::FnContractProved { time_ms, .. }
            | Self::FnContractAdmitted { time_ms, .. } => {
                *time_ms = elapsed;
            }
            Self::Counterexample { .. }
            | Self::SceneFail { .. }
            | Self::SceneUnknown { .. }
            | Self::Unprovable { .. }
            | Self::FnContractFailed { .. }
            | Self::LivenessViolation { .. }
            | Self::Deadlock { .. } => {}
        }
        self
    }

    /// Is this a failure (counterexample, scene fail, fn contract fail, liveness violation, deadlock, or unprovable)?
    pub fn is_failure(&self) -> bool {
        matches!(
            self,
            Self::Counterexample { .. }
                | Self::SceneFail { .. }
                | Self::SceneUnknown { .. }
                | Self::Unprovable { .. }
                | Self::FnContractFailed { .. }
                | Self::LivenessViolation { .. }
                | Self::Deadlock { .. }
        )
    }

    /// Source span for diagnostic rendering.
    pub fn span(&self) -> Option<crate::span::Span> {
        match self {
            Self::Proved { span, .. }
            | Self::Admitted { span, .. }
            | Self::Checked { span, .. }
            | Self::Counterexample { span, .. }
            | Self::ScenePass { span, .. }
            | Self::SceneFail { span, .. }
            | Self::SceneUnknown { span, .. }
            | Self::Unprovable { span, .. }
            | Self::FnContractProved { span, .. }
            | Self::FnContractAdmitted { span, .. }
            | Self::FnContractFailed { span, .. }
            | Self::LivenessViolation { span, .. }
            | Self::Deadlock { span, .. } => *span,
        }
    }

    /// Source file for diagnostic rendering.
    pub fn file(&self) -> Option<&str> {
        match self {
            Self::Proved { file, .. }
            | Self::Admitted { file, .. }
            | Self::Checked { file, .. }
            | Self::Counterexample { file, .. }
            | Self::ScenePass { file, .. }
            | Self::SceneFail { file, .. }
            | Self::SceneUnknown { file, .. }
            | Self::Unprovable { file, .. }
            | Self::FnContractProved { file, .. }
            | Self::FnContractAdmitted { file, .. }
            | Self::LivenessViolation { file, .. }
            | Self::FnContractFailed { file, .. }
            | Self::Deadlock { file, .. } => file.as_deref(),
        }
    }

    /// Convert function verification outcomes into transport-friendly diagnostics.
    ///
    /// Successful proof/check results intentionally return `None`; callers can
    /// render those as ordinary verification results. This adapter is the shared
    /// surface for CLI/report/LSP diagnostics that need stable codes, severity,
    /// source location, and user-facing messages for failed or admitted function
    /// obligations.
    #[must_use]
    pub fn to_diagnostic(&self) -> Option<Diagnostic> {
        match self {
            Self::FnContractFailed {
                name,
                counterexample,
                span,
                file,
            } => Some(attach_diagnostic_source(
                Diagnostic::error(format!("function `{name}` violates its ensures contract"))
                    .with_code("abide::verify::fn_ensures_failed")
                    .with_help(fn_counterexample_help(counterexample)),
                *span,
                file.as_deref(),
            )),
            Self::FnContractAdmitted {
                name,
                reason,
                span,
                file,
                ..
            } => {
                let code = if reason.contains("sorry") {
                    "abide::verify::fn_admitted_sorry"
                } else if reason.contains("todo") {
                    "abide::verify::fn_admitted_todo"
                } else if reason.contains("assume") {
                    "abide::verify::fn_admitted_assume"
                } else {
                    "abide::verify::fn_admitted"
                };
                Some(attach_diagnostic_source(
                    Diagnostic::warning(format!(
                        "function `{name}` verification is admitted: {reason}"
                    ))
                    .with_code(code)
                    .with_help(
                        "admitted function obligations are trusted locally; other functions are still verified",
                    ),
                    *span,
                    file.as_deref(),
                ))
            }
            Self::Admitted {
                name,
                reason,
                span,
                file,
                ..
            } => Some(attach_diagnostic_source(
                Diagnostic::warning(format!("verification `{name}` is admitted: {reason}"))
                    .with_code("abide::verify::proof_admitted")
                    .with_help(
                        "admitted proof obligations are trusted; run full CLI or REPL verification before relying on them",
                    ),
                *span,
                file.as_deref(),
            )),
            Self::Unprovable {
                name,
                hint,
                span,
                file,
            } if name.starts_with("fn_") => {
                let function_name = name.strip_prefix("fn_").unwrap_or(name);
                let (code, message) = classify_function_unprovable(function_name, hint);
                Some(attach_diagnostic_source(
                    Diagnostic::error(message)
                        .with_code(code)
                        .with_help(hint.clone()),
                    *span,
                    file.as_deref(),
                ))
            }
            _ => None,
        }
    }

    /// Result-level evidence payload, when available.
    pub fn evidence(&self) -> Option<&EvidenceEnvelope> {
        match self {
            Self::Admitted { evidence, .. }
            | Self::Counterexample { evidence, .. }
            | Self::ScenePass { evidence, .. }
            | Self::LivenessViolation { evidence, .. }
            | Self::Deadlock { evidence, .. } => evidence.as_ref(),
            _ => None,
        }
    }

    /// Native witness payload, when available.
    pub fn witness(&self) -> Option<&WitnessEnvelope> {
        self.evidence().and_then(EvidenceEnvelope::as_witness)
    }

    /// Operational witness payload, when this result carries one.
    pub fn operational_witness(&self) -> Option<&op::OperationalWitness> {
        self.witness().and_then(WitnessEnvelope::as_operational)
    }

    /// Relational witness payload, when this result carries one.
    pub fn relational_witness(&self) -> Option<&rel::RelationalWitness> {
        self.witness().and_then(WitnessEnvelope::as_relational)
    }

    /// Countermodel evidence, when this result carries proof-side model data.
    pub fn countermodel(&self) -> Option<&Countermodel> {
        self.evidence().and_then(EvidenceEnvelope::as_countermodel)
    }

    /// External proof-artifact reference, when present.
    pub fn proof_artifact_ref(&self) -> Option<&ProofArtifactRef> {
        self.evidence()
            .and_then(EvidenceEnvelope::as_proof_artifact_ref)
    }

    /// Evidence extraction error, when the result kind was determined but
    /// witness/evidence construction degraded.
    pub fn evidence_extraction_error(&self) -> Option<&str> {
        match self {
            Self::Counterexample {
                evidence_extraction_error,
                ..
            }
            | Self::LivenessViolation {
                evidence_extraction_error,
                ..
            }
            | Self::Deadlock {
                evidence_extraction_error,
                ..
            } => evidence_extraction_error.as_deref(),
            _ => None,
        }
    }

    pub fn counterexample_replay(&self) -> Option<&CounterexampleReplayReport> {
        match self {
            Self::Counterexample { replay, .. } => replay.as_ref(),
            _ => None,
        }
    }

    /// Trusted assumptions disclosed on this result.
    pub fn assumptions(&self) -> &[TrustedAssumption] {
        match self {
            Self::Proved { assumptions, .. }
            | Self::Admitted { assumptions, .. }
            | Self::Checked { assumptions, .. }
            | Self::Counterexample { assumptions, .. }
            | Self::LivenessViolation { assumptions, .. }
            | Self::Deadlock { assumptions, .. } => assumptions,
            Self::ScenePass { .. }
            | Self::SceneFail { .. }
            | Self::SceneUnknown { .. }
            | Self::Unprovable { .. }
            | Self::FnContractProved { .. }
            | Self::FnContractAdmitted { .. }
            | Self::FnContractFailed { .. } => &[],
        }
    }

    pub fn backend_diagnostics(&self) -> &[BackendDiagnostic] {
        match self {
            Self::Checked {
                backend_diagnostics,
                ..
            } => backend_diagnostics,
            _ => &[],
        }
    }
}

fn attach_diagnostic_source(
    mut diagnostic: Diagnostic,
    span: Option<crate::span::Span>,
    file: Option<&str>,
) -> Diagnostic {
    if let Some(span) = span {
        diagnostic = diagnostic.with_span(span);
    }
    if let Some(file) = file {
        diagnostic = diagnostic.in_file(file.to_owned());
    }
    diagnostic
}

fn fn_counterexample_help(counterexample: &[(String, String)]) -> String {
    if counterexample.is_empty() {
        "the solver found inputs that violate the ensures clause".to_owned()
    } else {
        format!(
            "counterexample: {}",
            counterexample
                .iter()
                .map(|(name, value)| format!("{name} = {value}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn classify_function_unprovable(function_name: &str, hint: &str) -> (&'static str, String) {
    if hint.contains(crate::messages::FN_CALL_PRECONDITION_FAILED) || hint.contains("precondition")
    {
        (
            "abide::verify::fn_precondition_failed",
            format!("function `{function_name}` may call another function without satisfying its requires clause"),
        )
    } else if hint.contains(crate::messages::FN_TERMINATION_FAILED)
        || hint.contains(crate::messages::FN_LOOP_TERMINATION_FAILED)
        || hint.contains("termination")
        || hint.contains("decreases")
    {
        (
            "abide::verify::fn_decreases_failed",
            format!(
                "function `{function_name}` has an unproved decreases or termination obligation"
            ),
        )
    } else if hint.contains(crate::messages::FN_LOOP_NO_INVARIANT)
        || hint.contains(crate::messages::FN_LOOP_INIT_FAILED)
        || hint.contains(crate::messages::FN_LOOP_PRESERVATION_FAILED)
        || hint.contains("loop invariant")
    {
        (
            "abide::verify::fn_loop_invariant_failed",
            format!("function `{function_name}` has an unproved loop invariant obligation"),
        )
    } else if hint.contains(crate::messages::FN_ASSERT_FAILED) || hint.contains("assertion") {
        (
            "abide::verify::fn_assertion_failed",
            format!("function `{function_name}` has an assertion that may not hold"),
        )
    } else {
        (
            "abide::verify::fn_unprovable",
            format!("function `{function_name}` has an unproved verification obligation"),
        )
    }
}

/// Collect transport-friendly diagnostics from verifier results.
///
/// This is intentionally lossy for successful proof/check results: successes
/// remain ordinary [`VerificationResult`] values, while failed or admitted
/// function obligations become diagnostics that editor and report surfaces can
/// display with stable codes and source locations.
#[must_use]
pub fn verification_diagnostics(results: &[VerificationResult]) -> Vec<Diagnostic> {
    results
        .iter()
        .filter_map(VerificationResult::to_diagnostic)
        .collect()
}

fn attach_backend_diagnostics(
    result: VerificationResult,
    diagnostics: &[BackendDiagnostic],
) -> VerificationResult {
    if diagnostics.is_empty() {
        return result;
    }
    match result {
        VerificationResult::Checked {
            name,
            depth,
            method,
            time_ms,
            assumptions,
            mut backend_diagnostics,
            span,
            file,
        } => {
            backend_diagnostics.extend_from_slice(diagnostics);
            VerificationResult::Checked {
                name,
                depth,
                method,
                time_ms,
                assumptions,
                backend_diagnostics,
                span,
                file,
            }
        }
        other => other,
    }
}

fn attach_proof_mode_hint(result: VerificationResult, config: &VerifyConfig) -> VerificationResult {
    if config.bounded_only
        || config.unbounded_only
        || !config.no_ic3
        || config.cvc5_sygus
        || !matches!(result, VerificationResult::Checked { .. })
    {
        return result;
    }
    attach_backend_diagnostics(result, &[BackendDiagnostic::proof_mode_hint()])
}

/// Internal presentation helper for trace-shaped witness rendering.
#[derive(Debug, Clone)]
pub(super) struct TraceStep {
    pub step: usize,
    pub event: Option<String>,
    pub assignments: Vec<(String, String, String)>, // (entity, field, value)
}

type DeadlockProbeOutcome = (
    usize,
    Option<EvidenceEnvelope>,
    Option<String>,
    Vec<DeadlockEventDiag>,
);

struct DeadlockProbeCtx<'a> {
    ir: &'a IRProgram,
    relevant_entities: &'a [crate::ir::types::IREntity],
    relevant_systems: &'a [IRSystem],
    vctx: &'a VerifyContext,
    scope: &'a HashMap<String, usize>,
    store_ranges: &'a HashMap<String, VerifyStoreRange>,
    verify_block: &'a IRVerify,
    bound: usize,
    config: &'a VerifyConfig,
    witness_semantics: WitnessSemantics,
}

// ── Configuration ───────────────────────────────────────────────────

/// Which SMT backend ordinary (non-CHC) verification goes to. `Auto`
/// picks Z3 by default and falls back per-routing rule; `Both` runs
/// every check on both and warns on disagreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverSelection {
    /// Force Z3.
    Z3,
    /// Force CVC5 (selected obligations only — most paths fall back to Z3).
    Cvc5,
    /// Per-obligation routing (Z3 unless a rule routes elsewhere).
    Auto,
    /// Run every obligation on both solvers.
    Both,
}

/// Which native witness family the verifier prefers when both
/// extraction paths apply (e.g. relational and operational checks
/// converge on the same target).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WitnessSemantics {
    /// Default. Behavioral traces.
    Operational,
    /// SAT relational snapshots/lassos.
    Relational,
}

/// Verification-target kind selector. Used by
/// [`VerifyTargetSelector`] to narrow `--target` matching when a name
/// is ambiguous across declaration kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VerifyTargetKind {
    /// `verify` block.
    Verify,
    /// `scene` block.
    Scene,
    /// `theorem` declaration.
    Theorem,
    /// `lemma` declaration.
    Lemma,
    /// `prop` (temporal property) declaration.
    Prop,
    /// `fn` contract verification.
    Fn,
}

impl VerifyTargetKind {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Verify => "verify",
            Self::Scene => "scene",
            Self::Theorem => "theorem",
            Self::Lemma => "lemma",
            Self::Prop => "prop",
            Self::Fn => "fn",
        }
    }

    fn parse(input: &str) -> Option<Self> {
        match input {
            "verify" => Some(Self::Verify),
            "scene" => Some(Self::Scene),
            "theorem" => Some(Self::Theorem),
            "lemma" => Some(Self::Lemma),
            "prop" => Some(Self::Prop),
            "fn" => Some(Self::Fn),
            _ => None,
        }
    }
}

/// Streaming notification emitted by verifier runs that opt into
/// observation. `ResultReady` carries the same finalized result value
/// that is appended to the complete result vector returned by the run.
#[derive(Debug, Clone)]
pub enum VerificationStreamEvent {
    TargetStarted {
        kind: VerifyTargetKind,
        name: String,
    },
    ResultReady {
        result: VerificationResult,
    },
    TargetSkipped {
        kind: VerifyTargetKind,
        name: String,
        reason: String,
    },
    RunCompleted {
        result_count: usize,
    },
}

/// Optional `--target` filter. Parsed from the CLI as `[kind:]name`;
/// when `kind` is `None` the name must resolve unambiguously across
/// every declaration kind in scope.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VerifyTargetSelector {
    pub kind: Option<VerifyTargetKind>,
    pub name: String,
}

impl VerifyTargetSelector {
    /// Returns `true` if the selector matches a target with the given
    /// `kind` and `name`. A `kind`-less selector matches any kind with
    /// the same name; ambiguity is resolved at dispatch time.
    #[must_use]
    pub fn matches(&self, kind: VerifyTargetKind, name: &str) -> bool {
        self.name == name && self.kind.is_none_or(|selected| selected == kind)
    }
}

impl fmt::Display for VerifyTargetSelector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(kind) = self.kind {
            write!(f, "{}:{}", kind.as_str(), self.name)
        } else {
            f.write_str(&self.name)
        }
    }
}

impl FromStr for VerifyTargetSelector {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let input = input.trim();
        if input.is_empty() {
            return Err("verification target must not be empty".to_owned());
        }
        if let Some((kind, name)) = input.split_once(':') {
            let kind = VerifyTargetKind::parse(kind).ok_or_else(|| {
                format!(
                    "unknown verification target kind `{kind}`; expected one of verify, scene, theorem, lemma, prop, fn"
                )
            })?;
            let name = name.trim();
            if name.is_empty() {
                return Err(format!("{} target must include a name", kind.as_str()));
            }
            Ok(Self {
                kind: Some(kind),
                name: name.to_owned(),
            })
        } else {
            Ok(Self {
                kind: None,
                name: input.to_owned(),
            })
        }
    }
}

/// Configuration for the verification pipeline.
///
/// The defaults (see [`Self::default`]) are tuned for the validation
/// gate in `make check-lang`: Z3 backends, conservative 20-minute
/// timeouts, IC3 disabled for ordinary verifies, all property and
/// function verification on. Tooling (the CLI, the LSP, QA's
/// `verify`) clone-and-tweak this default rather than constructing
/// the struct directly.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone)]
pub struct VerifyConfig {
    /// Solver selection mode for ordinary SAT/BMC/property/theorem/scene paths.
    pub solver_selection: SolverSelection,
    /// Backend selection mode for CHC/IC3 paths.
    pub chc_selection: ChcSelection,
    /// Skip Tier 1 (induction), only run bounded model checking.
    pub bounded_only: bool,
    /// Skip Tier 2 (BMC), only try induction.
    pub unbounded_only: bool,
    /// Timeout for Tier 1 induction attempts, in milliseconds.
    pub induction_timeout_ms: u64,
    /// Timeout for Tier 2 BMC attempts, in milliseconds.
    pub bmc_timeout_ms: u64,
    /// Search bounded safety depths incrementally and stop at the first counterexample.
    pub bmc_iterative_deepening: bool,
    /// End-to-end timeout for the full verification command, in milliseconds.
    pub overall_timeout_ms: u64,
    /// Default BMC depth for auto-verified props (which lack explicit `[0..N]`).
    pub prop_bmc_depth: usize,
    /// Opt cvc5 solver runs into in-process SyGuS invariant synthesis.
    pub cvc5_sygus: bool,
    /// Timeout for IC3/PDR attempts, in milliseconds.
    pub ic3_timeout_ms: u64,
    /// Skip IC3/PDR for ordinary verify blocks and theorem proof attempts.
    pub no_ic3: bool,
    /// Skip automatic prop verification.
    pub no_prop_verify: bool,
    /// Skip function contract verification.
    pub no_fn_verify: bool,
    /// Native witness family to prefer when multiple extraction paths exist.
    pub witness_semantics: WitnessSemantics,
    /// Add semantics-preserving symmetry breaking to relational SAT encodings.
    pub relational_symmetry_breaking: bool,
    /// Optional target selector. Untyped selectors must resolve unambiguously.
    pub target: Option<VerifyTargetSelector>,
}

impl Default for VerifyConfig {
    fn default() -> Self {
        Self {
            solver_selection: SolverSelection::Z3,
            chc_selection: ChcSelection::Z3,
            bounded_only: false,
            unbounded_only: false,
            induction_timeout_ms: 1_200_000,
            bmc_timeout_ms: 1_200_000,
            bmc_iterative_deepening: true,
            overall_timeout_ms: 1_200_000,
            prop_bmc_depth: 10,
            cvc5_sygus: false,
            ic3_timeout_ms: 1_200_000,
            no_ic3: true,
            no_prop_verify: false,
            no_fn_verify: false,
            witness_semantics: WitnessSemantics::Operational,
            relational_symmetry_breaking: true,
            target: None,
        }
    }
}

pub(super) fn timeout_display_ms(ms: u64) -> String {
    if ms >= 1000 {
        format!("{}s", ms / 1000)
    } else {
        format!("{ms}ms")
    }
}

pub(super) fn verification_deadline(config: &VerifyConfig) -> Option<Instant> {
    (config.overall_timeout_ms > 0)
        .then(|| Instant::now() + Duration::from_millis(config.overall_timeout_ms))
}

pub(super) fn remaining_budget_ms(deadline: Option<Instant>) -> Option<u64> {
    deadline.map(|deadline| {
        let now = Instant::now();
        if now >= deadline {
            0
        } else {
            deadline
                .duration_since(now)
                .as_millis()
                .min(u128::from(u64::MAX)) as u64
        }
    })
}

pub(super) fn clamp_timeout_to_deadline(timeout_ms: u64, deadline: Option<Instant>) -> Option<u64> {
    match remaining_budget_ms(deadline) {
        Some(0) => None,
        Some(remaining_ms) => Some(if timeout_ms == 0 {
            remaining_ms
        } else {
            timeout_ms.min(remaining_ms)
        }),
        None => Some(timeout_ms),
    }
}

pub(super) fn clamp_config_to_deadline(
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> Option<VerifyConfig> {
    let induction_timeout_ms = clamp_timeout_to_deadline(config.induction_timeout_ms, deadline)?;
    let bmc_timeout_ms = clamp_timeout_to_deadline(config.bmc_timeout_ms, deadline)?;
    let ic3_timeout_ms = clamp_timeout_to_deadline(config.ic3_timeout_ms, deadline)?;
    let mut adjusted = config.clone();
    adjusted.induction_timeout_ms = induction_timeout_ms;
    adjusted.bmc_timeout_ms = bmc_timeout_ms;
    adjusted.ic3_timeout_ms = ic3_timeout_ms;
    adjusted.overall_timeout_ms =
        remaining_budget_ms(deadline).unwrap_or(config.overall_timeout_ms);
    Some(adjusted)
}

pub(super) fn verification_timeout_hint(config: &VerifyConfig) -> String {
    format!(
        "verification timed out after {} — increase --timeout or simplify the target",
        timeout_display_ms(config.overall_timeout_ms)
    )
}

/// One verifiable target found in an IR program: a (kind, name) pair.
/// Returned by [`available_verify_targets`] for CLI listing and
/// `--target` resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifyTargetEntry {
    pub kind: VerifyTargetKind,
    pub name: String,
}

impl fmt::Display for VerifyTargetEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.kind.as_str(), self.name)
    }
}

/// Enumerates every verifiable target in `ir` — every `verify`,
/// `scene`, `theorem`, `lemma`, `prop`, and contracted `fn`.
#[must_use]
pub fn available_verify_targets(ir: &IRProgram) -> Vec<VerifyTargetEntry> {
    let mut targets = Vec::new();
    targets.extend(ir.verifies.iter().map(|block| VerifyTargetEntry {
        kind: VerifyTargetKind::Verify,
        name: block.name.clone(),
    }));
    targets.extend(ir.scenes.iter().map(|block| VerifyTargetEntry {
        kind: VerifyTargetKind::Scene,
        name: block.name.clone(),
    }));
    targets.extend(ir.theorems.iter().map(|block| VerifyTargetEntry {
        kind: VerifyTargetKind::Theorem,
        name: block.name.clone(),
    }));
    targets.extend(ir.lemmas.iter().map(|block| VerifyTargetEntry {
        kind: VerifyTargetKind::Lemma,
        name: block.name.clone(),
    }));
    targets.extend(ir.functions.iter().filter_map(|func| {
        func.prop_target.as_ref().map(|_| VerifyTargetEntry {
            kind: VerifyTargetKind::Prop,
            name: func.name.clone(),
        })
    }));
    targets.extend(ir.functions.iter().filter_map(|func| {
        if func.prop_target.is_none()
            && (!func.ensures.is_empty()
                || func.decreases.is_some()
                || body_contains_assert(&func.body)
                || body_contains_sorry(&func.body)
                || body_contains_todo(&func.body))
        {
            Some(VerifyTargetEntry {
                kind: VerifyTargetKind::Fn,
                name: func.name.clone(),
            })
        } else {
            None
        }
    }));
    targets.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.kind.as_str().cmp(right.kind.as_str()))
    });
    targets
}

fn selected_target_error(ir: &IRProgram, config: &VerifyConfig) -> Option<VerificationResult> {
    let selector = config.target.as_ref()?;
    let available = available_verify_targets(ir);
    let matches: Vec<_> = available
        .iter()
        .filter(|entry| selector.matches(entry.kind, &entry.name))
        .collect();
    match matches.as_slice() {
        [entry] if entry.kind == VerifyTargetKind::Prop && config.no_prop_verify => {
            Some(VerificationResult::Unprovable {
                name: selector.to_string(),
                hint: "selected target is disabled by --no-prop-verify".to_owned(),
                span: None,
                file: None,
            })
        }
        [entry] if entry.kind == VerifyTargetKind::Fn && config.no_fn_verify => {
            Some(VerificationResult::Unprovable {
                name: selector.to_string(),
                hint: "selected target is disabled by --no-fn-verify".to_owned(),
                span: None,
                file: None,
            })
        }
        [_] => None,
        [] => Some(VerificationResult::Unprovable {
            name: selector.to_string(),
            hint: format!(
                "unknown verification target `{selector}`; available targets: {}",
                format_available_targets(&available)
            ),
            span: None,
            file: None,
        }),
        _ if selector.kind.is_none() => Some(VerificationResult::Unprovable {
            name: selector.to_string(),
            hint: format!(
                "verification target `{}` is ambiguous; use one of: {}",
                selector.name,
                matches
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            span: None,
            file: None,
        }),
        _ => None,
    }
}

fn format_available_targets(targets: &[VerifyTargetEntry]) -> String {
    if targets.is_empty() {
        "none".to_owned()
    } else {
        targets
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

pub(super) fn should_run_target(config: &VerifyConfig, kind: VerifyTargetKind, name: &str) -> bool {
    config
        .target
        .as_ref()
        .is_none_or(|selector| selector.matches(kind, name))
}

fn should_prepare_lemma_dependency(config: &VerifyConfig) -> bool {
    config
        .target
        .as_ref()
        .is_some_and(|selector| selector.kind != Some(VerifyTargetKind::Lemma))
}

fn solver_label(family: SolverFamily) -> &'static str {
    match family {
        SolverFamily::Z3 => "z3",
        SolverFamily::Cvc5 => "cvc5",
    }
}

fn result_name(result: &VerificationResult) -> &str {
    match result {
        VerificationResult::Proved { name, .. }
        | VerificationResult::Admitted { name, .. }
        | VerificationResult::Checked { name, .. }
        | VerificationResult::Counterexample { name, .. }
        | VerificationResult::ScenePass { name, .. }
        | VerificationResult::SceneFail { name, .. }
        | VerificationResult::SceneUnknown { name, .. }
        | VerificationResult::Unprovable { name, .. }
        | VerificationResult::FnContractProved { name, .. }
        | VerificationResult::FnContractAdmitted { name, .. }
        | VerificationResult::FnContractFailed { name, .. }
        | VerificationResult::LivenessViolation { name, .. }
        | VerificationResult::Deadlock { name, .. } => name,
    }
}

fn result_signature(result: &VerificationResult) -> String {
    match result {
        VerificationResult::Proved { name, method, .. } => format!("proved:{name}:{method}"),
        VerificationResult::Admitted { name, .. } => format!("admitted:{name}"),
        VerificationResult::Checked { name, depth, .. } => format!("checked:{name}:{depth}"),
        VerificationResult::Counterexample { name, .. } => format!("counterexample:{name}"),
        VerificationResult::ScenePass { name, .. } => format!("scene-pass:{name}"),
        VerificationResult::SceneFail { name, .. } => format!("scene-fail:{name}"),
        VerificationResult::SceneUnknown { name, .. } => format!("scene-unknown:{name}"),
        VerificationResult::Unprovable { name, .. } => format!("unprovable:{name}"),
        VerificationResult::FnContractProved { name, .. } => format!("fn-proved:{name}"),
        VerificationResult::FnContractAdmitted { name, .. } => format!("fn-admitted:{name}"),
        VerificationResult::FnContractFailed { name, .. } => format!("fn-failed:{name}"),
        VerificationResult::LivenessViolation { name, .. } => format!("liveness:{name}"),
        VerificationResult::Deadlock { name, .. } => format!("deadlock:{name}"),
    }
}

fn reconcile_solver_results(
    left_family: SolverFamily,
    left: Vec<VerificationResult>,
    right_family: SolverFamily,
    right: Vec<VerificationResult>,
) -> Vec<VerificationResult> {
    if left.len() != right.len() {
        return vec![VerificationResult::Unprovable {
            name: "solver_backend_comparison".to_owned(),
            hint: format!(
                "solver result count mismatch: {} produced {}, {} produced {}",
                solver_label(left_family),
                left.len(),
                solver_label(right_family),
                right.len()
            ),
            span: None,
            file: None,
        }];
    }

    left.into_iter()
        .zip(right)
        .map(|(lhs, rhs)| {
            if result_signature(&lhs) == result_signature(&rhs) {
                lhs
            } else {
                VerificationResult::Unprovable {
                    name: result_name(&lhs).to_owned(),
                    hint: format!(
                        "solver disagreement: {} reported `{}`, {} reported `{}`",
                        solver_label(left_family),
                        result_signature(&lhs),
                        solver_label(right_family),
                        result_signature(&rhs)
                    ),
                    span: lhs.span(),
                    file: lhs.file().map(str::to_owned),
                }
            }
        })
        .collect()
}

fn auto_solver_for_scene() -> SolverFamily {
    if is_solver_family_available(SolverFamily::Cvc5) {
        SolverFamily::Cvc5
    } else {
        SolverFamily::Z3
    }
}

fn unavailable_solver_result(name: &str, hint: String) -> VerificationResult {
    VerificationResult::Unprovable {
        name: name.to_owned(),
        hint,
        span: None,
        file: None,
    }
}

pub(super) fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(msg) = payload.downcast_ref::<String>() {
        msg.clone()
    } else if let Some(msg) = payload.downcast_ref::<&'static str>() {
        (*msg).to_owned()
    } else {
        // `panic!` payloads are almost always `String` or `&'static str`.
        // Keep this fallback explicit so `panic_any(...)` callers still
        // degrade honestly without forcing a debug-format dependency here.
        "non-string panic payload".to_owned()
    }
}

pub(super) fn internal_verifier_hint(context: &str, detail: &str) -> String {
    format!("internal verifier error while {context}: {detail}")
}

fn catch_verification_panic<F>(
    name: &str,
    span: Option<crate::span::Span>,
    file: Option<String>,
    context: &str,
    f: F,
) -> VerificationResult
where
    F: FnOnce() -> VerificationResult,
{
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(result) => result,
        Err(payload) => VerificationResult::Unprovable {
            name: name.to_owned(),
            hint: internal_verifier_hint(context, &panic_message(payload)),
            span,
            file,
        },
    }
}

fn synthetic_prop_name(func: &IRFunction) -> String {
    format!("prop_{}", func.name)
}

fn synthetic_prop_theorem(func: &IRFunction, target_system: &str) -> IRTheorem {
    IRTheorem {
        name: synthetic_prop_name(func),
        systems: vec![target_system.to_owned()],
        // Synthetic theorem for a top-level prop. Props verified through the
        // theorem path keep theorem/lemma defaults (stutter on).
        assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
        invariants: vec![],
        shows: vec![IRExpr::Always {
            body: Box::new(func.body.clone()),
            span: None,
        }],
        by_file: None,
        by_lemmas: vec![],
        span: func.span,
        file: func.file.clone(),
    }
}

fn synthetic_prop_verify(
    func: &IRFunction,
    target_system: &str,
    prop_bmc_depth: usize,
) -> IRVerify {
    let depth = prop_bmc_depth.max(1);
    let bound = depth.min(i64::MAX as usize) as i64;
    IRVerify {
        name: synthetic_prop_name(func),
        depth: Some(depth),
        systems: vec![IRVerifySystem {
            name: target_system.to_owned(),
            lo: 0,
            hi: bound,
        }],
        stores: vec![],
        // Props verified through the bounded verify fallback still represent
        // top-level proof obligations, so keep theorem/lemma defaults.
        assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
        activations: vec![],
        initial_constraints: vec![],
        asserts: vec![IRExpr::Always {
            body: Box::new(func.body.clone()),
            span: None,
        }],
        span: func.span,
        file: func.file.clone(),
    }
}

fn check_prop_bmc_fallback(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    func: &IRFunction,
    target_system: &str,
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> VerificationResult {
    let synthetic_verify = synthetic_prop_verify(func, target_system, config.prop_bmc_depth);
    let mut prop_bmc_config = config.clone();
    prop_bmc_config.bounded_only = true;
    prop_bmc_config.unbounded_only = false;
    check_verify_block_tiered(
        ir,
        vctx,
        defs,
        &synthetic_verify,
        &prop_bmc_config,
        deadline,
    )
    .with_source(func.span, func.file.clone())
}

// ── Top-level verification entry point ──────────────────────────────

/// Verify all targets in an IR program.
///
/// Processes function-contract preflight first, then verify blocks
/// (tiered: induction → IC3 → BMC), scene blocks (SAT), and theorem blocks
/// (IC3 → induction). Hard function preflight failures gate later targets;
/// admitted obligations remain visible but allow later verification to run.
/// Returns one result per target, each carrying source location for diagnostic rendering.
pub fn verify_all(ir: &IRProgram, config: &VerifyConfig) -> Vec<VerificationResult> {
    let mut event_sink = ignore_verification_stream_event;
    verify_all_inner(ir, config, &mut event_sink, false)
}

/// Verify all targets and notify a caller-provided sink as each finalized
/// result becomes available.
///
/// The returned vector is identical to [`verify_all`]. Streaming events are
/// observational: they do not change target selection, solver semantics,
/// report generation, or trace artifact inputs.
pub fn verify_all_with_events<F>(
    ir: &IRProgram,
    config: &VerifyConfig,
    mut event_sink: F,
) -> Vec<VerificationResult>
where
    F: FnMut(&VerificationStreamEvent),
{
    let results = verify_all_inner(ir, config, &mut event_sink, true);
    event_sink(&VerificationStreamEvent::RunCompleted {
        result_count: results.len(),
    });
    results
}

fn verify_all_inner(
    ir: &IRProgram,
    config: &VerifyConfig,
    event_sink: &mut dyn FnMut(&VerificationStreamEvent),
    streaming: bool,
) -> Vec<VerificationResult> {
    if let Some(result) = selected_target_error(ir, config) {
        emit_stream_result(event_sink, &result);
        return vec![result];
    }

    let resolved_chc_family = match chc::resolve_chc_family(config.chc_selection) {
        Ok(family) => family,
        Err(hint) => {
            let result = unavailable_solver_result("chc_backend", hint);
            emit_stream_result(event_sink, &result);
            return vec![result];
        }
    };

    match config.solver_selection {
        SolverSelection::Z3 => verify_all_single(
            ir,
            config,
            SolverFamily::Z3,
            SolverFamily::Z3,
            resolved_chc_family,
            event_sink,
        ),
        SolverSelection::Cvc5 => {
            if !is_solver_family_available(SolverFamily::Cvc5) {
                let result = unavailable_solver_result(
                    "verification",
                    "requested solver `cvc5` is not available in this build".to_owned(),
                );
                emit_stream_result(event_sink, &result);
                return vec![result];
            }
            verify_all_single(
                ir,
                config,
                SolverFamily::Cvc5,
                SolverFamily::Cvc5,
                resolved_chc_family,
                event_sink,
            )
        }
        SolverSelection::Auto => {
            let scene_family = auto_solver_for_scene();
            verify_all_single(
                ir,
                config,
                SolverFamily::Z3,
                scene_family,
                resolved_chc_family,
                event_sink,
            )
        }
        SolverSelection::Both => {
            if !is_solver_family_available(SolverFamily::Cvc5) {
                let result = unavailable_solver_result(
                    "solver_backend_comparison",
                    "requested solver `both` requires the cvc5 backend to be available in this build"
                        .to_owned(),
                );
                emit_stream_result(event_sink, &result);
                return vec![result];
            }
            if streaming {
                let mut z3_config = config.clone();
                z3_config.solver_selection = SolverSelection::Z3;
                let mut cvc5_config = config.clone();
                cvc5_config.solver_selection = SolverSelection::Cvc5;
                let z3_results = verify_all_single(
                    ir,
                    &z3_config,
                    SolverFamily::Z3,
                    SolverFamily::Z3,
                    resolved_chc_family,
                    event_sink,
                );
                let cvc5_results = verify_all_single(
                    ir,
                    &cvc5_config,
                    SolverFamily::Cvc5,
                    SolverFamily::Cvc5,
                    resolved_chc_family,
                    event_sink,
                );
                return reconcile_solver_results(
                    SolverFamily::Z3,
                    z3_results,
                    SolverFamily::Cvc5,
                    cvc5_results,
                );
            }
            let ir_z3 = ir.clone();
            let ir_cvc5 = ir.clone();
            let mut z3_config = config.clone();
            z3_config.solver_selection = SolverSelection::Z3;
            let mut cvc5_config = config.clone();
            cvc5_config.solver_selection = SolverSelection::Cvc5;

            let z3 = thread::spawn(move || {
                let mut event_sink = ignore_verification_stream_event;
                verify_all_single(
                    &ir_z3,
                    &z3_config,
                    SolverFamily::Z3,
                    SolverFamily::Z3,
                    resolved_chc_family,
                    &mut event_sink,
                )
            });
            let cvc5 = thread::spawn(move || {
                let mut event_sink = ignore_verification_stream_event;
                verify_all_single(
                    &ir_cvc5,
                    &cvc5_config,
                    SolverFamily::Cvc5,
                    SolverFamily::Cvc5,
                    resolved_chc_family,
                    &mut event_sink,
                )
            });

            let z3_results = match z3.join() {
                Ok(results) => results,
                Err(payload) => {
                    return vec![VerificationResult::Unprovable {
                        name: "verification".to_owned(),
                        hint: internal_verifier_hint(
                            "running z3 verification thread",
                            &panic_message(payload),
                        ),
                        span: None,
                        file: None,
                    }];
                }
            };
            let cvc5_results = match cvc5.join() {
                Ok(results) => results,
                Err(payload) => {
                    return vec![VerificationResult::Unprovable {
                        name: "verification".to_owned(),
                        hint: internal_verifier_hint(
                            "running cvc5 verification thread",
                            &panic_message(payload),
                        ),
                        span: None,
                        file: None,
                    }];
                }
            };
            reconcile_solver_results(
                SolverFamily::Z3,
                z3_results,
                SolverFamily::Cvc5,
                cvc5_results,
            )
        }
    }
}

fn emit_stream_result(
    event_sink: &mut dyn FnMut(&VerificationStreamEvent),
    result: &VerificationResult,
) {
    event_sink(&VerificationStreamEvent::ResultReady {
        result: result.clone(),
    });
}

fn ignore_verification_stream_event(_: &VerificationStreamEvent) {}

/// Verify only function contracts in an IR program.
///
/// This is intended for latency-sensitive editor feedback. It runs the same
/// function preflight used by [`verify_all`] but does not dispatch verify
/// blocks, scenes, lemmas, theorems, or props.
pub fn verify_function_contracts_only(
    ir: &IRProgram,
    config: &VerifyConfig,
) -> Vec<VerificationResult> {
    let solver_family = match config.solver_selection {
        SolverSelection::Cvc5 => {
            if !is_solver_family_available(SolverFamily::Cvc5) {
                return vec![unavailable_solver_result(
                    "verification",
                    "requested solver `cvc5` is not available in this build".to_owned(),
                )];
            }
            SolverFamily::Cvc5
        }
        SolverSelection::Z3 | SolverSelection::Auto | SolverSelection::Both => SolverFamily::Z3,
    };

    match panic::catch_unwind(AssertUnwindSafe(|| {
        let mut event_sink = ignore_verification_stream_event;
        let mut run = VerifyAllRun::new(ir, config, solver_family, solver_family, &mut event_sink);
        run.verify_function_contracts();
        run.finish()
    })) {
        Ok(results) => results,
        Err(payload) => vec![VerificationResult::Unprovable {
            name: "fn_verification".to_owned(),
            hint: internal_verifier_hint(
                &format!(
                    "running {} function verification",
                    solver_label(solver_family)
                ),
                &panic_message(payload),
            ),
            span: None,
            file: None,
        }],
    }
}

/// Verify only theorem and lemma proof obligations in an IR program.
///
/// This focused entry point is intended for explicit editor or REPL preflight
/// commands. It does not dispatch verify blocks, scenes, props, or function
/// contract checks. Expensive proof search follows the supplied
/// [`VerifyConfig`], so IC3/PDR remains disabled unless `no_ic3` is false.
pub fn verify_proof_obligations_only(
    ir: &IRProgram,
    config: &VerifyConfig,
) -> Vec<VerificationResult> {
    let solver_family = match config.solver_selection {
        SolverSelection::Cvc5 => {
            if !is_solver_family_available(SolverFamily::Cvc5) {
                return vec![unavailable_solver_result(
                    "proof_verification",
                    "requested solver `cvc5` is not available in this build".to_owned(),
                )];
            }
            SolverFamily::Cvc5
        }
        SolverSelection::Z3 | SolverSelection::Auto | SolverSelection::Both => SolverFamily::Z3,
    };

    match panic::catch_unwind(AssertUnwindSafe(|| {
        let mut event_sink = ignore_verification_stream_event;
        let mut run = VerifyAllRun::new(ir, config, solver_family, solver_family, &mut event_sink);
        run.verify_lemmas();
        run.verify_theorems();
        run.finish()
    })) {
        Ok(results) => results,
        Err(payload) => vec![VerificationResult::Unprovable {
            name: "proof_verification".to_owned(),
            hint: internal_verifier_hint(
                &format!(
                    "running {} proof obligation verification",
                    solver_label(solver_family)
                ),
                &panic_message(payload),
            ),
            span: None,
            file: None,
        }],
    }
}

fn verify_all_single(
    ir: &IRProgram,
    config: &VerifyConfig,
    solver_family: SolverFamily,
    scene_solver_family: SolverFamily,
    chc_family: SolverFamily,
    event_sink: &mut dyn FnMut(&VerificationStreamEvent),
) -> Vec<VerificationResult> {
    match panic::catch_unwind(AssertUnwindSafe(|| {
        verify_all_single_impl(
            ir,
            config,
            solver_family,
            scene_solver_family,
            chc_family,
            event_sink,
        )
    })) {
        Ok(results) => results,
        Err(payload) => {
            let result = VerificationResult::Unprovable {
                name: "verification".to_owned(),
                hint: internal_verifier_hint(
                    &format!("running {} backend", solver_label(solver_family)),
                    &panic_message(payload),
                ),
                span: None,
                file: None,
            };
            emit_stream_result(event_sink, &result);
            vec![result]
        }
    }
}

fn verify_all_single_impl(
    ir: &IRProgram,
    config: &VerifyConfig,
    solver_family: SolverFamily,
    scene_solver_family: SolverFamily,
    chc_family: SolverFamily,
    event_sink: &mut dyn FnMut(&VerificationStreamEvent),
) -> Vec<VerificationResult> {
    if let Err(hint) = set_active_solver_family(solver_family) {
        let result = unavailable_solver_result("verification", hint);
        emit_stream_result(event_sink, &result);
        return vec![result];
    }
    if let Err(hint) = chc::set_active_chc_family(chc_family) {
        let result = unavailable_solver_result("chc_backend", hint);
        emit_stream_result(event_sink, &result);
        return vec![result];
    }
    VerifyAllRun::new(ir, config, solver_family, scene_solver_family, event_sink).run()
}

struct VerifyAllRun<'a, 'e> {
    ir: &'a IRProgram,
    config: &'a VerifyConfig,
    solver_family: SolverFamily,
    scene_solver_family: SolverFamily,
    vctx: VerifyContext,
    defs: defenv::DefEnv,
    deadline: Option<Instant>,
    results: Vec<VerificationResult>,
    axiom_assumptions: Vec<TrustedAssumption>,
    event_sink: &'e mut dyn FnMut(&VerificationStreamEvent),
}

impl<'a, 'e> VerifyAllRun<'a, 'e> {
    fn new(
        ir: &'a IRProgram,
        config: &'a VerifyConfig,
        solver_family: SolverFamily,
        scene_solver_family: SolverFamily,
        event_sink: &'e mut dyn FnMut(&VerificationStreamEvent),
    ) -> Self {
        Self {
            ir,
            config,
            solver_family,
            scene_solver_family,
            vctx: context::VerifyContext::from_ir(ir),
            defs: defenv::DefEnv::from_ir(ir),
            deadline: verification_deadline(config),
            results: Vec::new(),
            axiom_assumptions: build_axiom_assumptions(&ir.axioms),
            event_sink,
        }
    }

    fn run(mut self) -> Vec<VerificationResult> {
        self.verify_function_contracts();
        if self.has_blocking_function_preflight_failure() {
            return self.finish();
        }
        self.verify_lemmas();
        self.verify_blocks();
        self.verify_scenes();
        self.verify_theorems();
        self.verify_props();
        self.finish()
    }

    fn finish(self) -> Vec<VerificationResult> {
        self.results
    }

    fn push_result(&mut self, result: VerificationResult) {
        let result = result.with_axioms(&self.axiom_assumptions);
        emit_stream_result(self.event_sink, &result);
        self.results.push(result);
    }

    fn effective_config_for_target(
        &mut self,
        name: &str,
        span: Option<crate::span::Span>,
        file: Option<String>,
    ) -> Option<VerifyConfig> {
        let Some(effective_config) = clamp_config_to_deadline(self.config, self.deadline) else {
            self.push_result(VerificationResult::Unprovable {
                name: name.to_owned(),
                hint: verification_timeout_hint(self.config),
                span,
                file,
            });
            return None;
        };
        Some(effective_config)
    }

    fn verify_lemmas(&mut self) {
        for lemma_block in &self.ir.lemmas {
            let selected =
                should_run_target(self.config, VerifyTargetKind::Lemma, &lemma_block.name);
            if !selected && !should_prepare_lemma_dependency(self.config) {
                continue;
            }
            let Some(effective_config) = self.effective_config_for_selected(
                selected,
                &lemma_block.name,
                lemma_block.span,
                lemma_block.file.clone(),
            ) else {
                continue;
            };
            if let Err(hint) = set_active_solver_family(self.solver_family) {
                if selected {
                    self.push_result(
                        unavailable_solver_result(&lemma_block.name, hint)
                            .with_source(lemma_block.span, lemma_block.file.clone()),
                    );
                }
                continue;
            }
            let start = Instant::now();
            let result = catch_verification_panic(
                &lemma_block.name,
                lemma_block.span,
                lemma_block.file.clone(),
                "proving lemma",
                || {
                    check_lemma_block(&self.vctx, &self.defs, lemma_block, &effective_config)
                        .with_source(lemma_block.span, lemma_block.file.clone())
                },
            );
            let result = result.with_time_ms(elapsed_ms(&start));
            if matches!(&result, VerificationResult::Proved { .. }) {
                self.defs
                    .add_lemma_fact(&lemma_block.name, &lemma_block.body);
            }
            if selected {
                self.push_result(result);
            }
        }
    }

    fn effective_config_for_selected(
        &mut self,
        selected: bool,
        name: &str,
        span: Option<crate::span::Span>,
        file: Option<String>,
    ) -> Option<VerifyConfig> {
        let Some(effective_config) = clamp_config_to_deadline(self.config, self.deadline) else {
            if selected {
                self.push_result(VerificationResult::Unprovable {
                    name: name.to_owned(),
                    hint: verification_timeout_hint(self.config),
                    span,
                    file,
                });
            }
            return None;
        };
        Some(effective_config)
    }

    fn verify_blocks(&mut self) {
        for verify_block in &self.ir.verifies {
            if !should_run_target(self.config, VerifyTargetKind::Verify, &verify_block.name) {
                continue;
            }
            let Some(effective_config) = self.effective_config_for_target(
                &verify_block.name,
                verify_block.span,
                verify_block.file.clone(),
            ) else {
                continue;
            };
            if let Err(hint) = set_active_solver_family(self.solver_family) {
                self.push_result(
                    unavailable_solver_result(&verify_block.name, hint)
                        .with_source(verify_block.span, verify_block.file.clone()),
                );
                continue;
            }
            clear_prop_precondition_obligations();
            clear_path_guard_stack();
            let start = Instant::now();
            let result = catch_verification_panic(
                &verify_block.name,
                verify_block.span,
                verify_block.file.clone(),
                "checking verify block",
                || {
                    check_verify_block_tiered(
                        self.ir,
                        &self.vctx,
                        &self.defs,
                        verify_block,
                        &effective_config,
                        self.deadline,
                    )
                    .with_source(verify_block.span, verify_block.file.clone())
                },
            );
            let result = result.with_time_ms(elapsed_ms(&start));
            self.push_result_or_precondition_violation(
                &verify_block.name,
                verify_block.span,
                verify_block.file.clone(),
                result,
            );
        }
    }

    fn verify_scenes(&mut self) {
        for scene_block in &self.ir.scenes {
            if !should_run_target(self.config, VerifyTargetKind::Scene, &scene_block.name) {
                continue;
            }
            let Some(effective_config) = self.effective_config_for_target(
                &scene_block.name,
                scene_block.span,
                scene_block.file.clone(),
            ) else {
                continue;
            };
            let start = Instant::now();
            let result = catch_verification_panic(
                &scene_block.name,
                scene_block.span,
                scene_block.file.clone(),
                "checking scene block",
                || self.check_scene(scene_block, &effective_config),
            );
            let result = result.with_time_ms(elapsed_ms(&start));
            self.push_result(result);
        }
    }

    fn check_scene(
        &self,
        scene_block: &crate::ir::types::IRScene,
        config: &VerifyConfig,
    ) -> VerificationResult {
        if let Some(result) = relational::try_check_scene_block_relational(self.ir, scene_block) {
            return result.with_source(scene_block.span, scene_block.file.clone());
        }
        if let Err(hint) = set_active_solver_family(self.scene_solver_family) {
            return unavailable_solver_result(&scene_block.name, hint)
                .with_source(scene_block.span, scene_block.file.clone());
        }
        check_scene_block(
            self.ir,
            &self.vctx,
            &self.defs,
            scene_block,
            config,
            self.deadline,
        )
        .with_source(scene_block.span, scene_block.file.clone())
    }

    fn verify_theorems(&mut self) {
        for theorem_block in &self.ir.theorems {
            if !should_run_target(self.config, VerifyTargetKind::Theorem, &theorem_block.name) {
                continue;
            }
            let Some(effective_config) = self.effective_config_for_target(
                &theorem_block.name,
                theorem_block.span,
                theorem_block.file.clone(),
            ) else {
                continue;
            };
            if let Err(hint) = set_active_solver_family(self.solver_family) {
                self.push_result(
                    unavailable_solver_result(&theorem_block.name, hint)
                        .with_source(theorem_block.span, theorem_block.file.clone()),
                );
                continue;
            }
            clear_prop_precondition_obligations();
            clear_path_guard_stack();
            let start = Instant::now();
            let result = catch_verification_panic(
                &theorem_block.name,
                theorem_block.span,
                theorem_block.file.clone(),
                "proving theorem",
                || {
                    check_theorem_block(
                        self.ir,
                        &self.vctx,
                        &self.defs,
                        theorem_block,
                        &effective_config,
                        self.deadline,
                    )
                    .with_source(theorem_block.span, theorem_block.file.clone())
                },
            );
            let result = result.with_time_ms(elapsed_ms(&start));
            self.push_result_or_precondition_violation(
                &theorem_block.name,
                theorem_block.span,
                theorem_block.file.clone(),
                result,
            );
        }
    }

    fn verify_function_contracts(&mut self) {
        if self.config.no_fn_verify {
            return;
        }
        if let Err(hint) = set_active_solver_family(self.solver_family) {
            self.push_result(unavailable_solver_result("fn_verification", hint));
        } else {
            let first_new_result = self.results.len();
            verify_fn_contracts(
                self.ir,
                &self.vctx,
                &self.defs,
                &self.function_preflight_config(),
                self.deadline,
                &mut self.results,
            );
            let new_results = self.results.split_off(first_new_result);
            for result in new_results {
                self.push_result(result);
            }
        }
    }

    fn function_preflight_config(&self) -> VerifyConfig {
        let mut config = self.config.clone();
        if self.selected_target_kind() != Some(VerifyTargetKind::Fn) {
            config.target = None;
        }
        config
    }

    fn selected_target_kind(&self) -> Option<VerifyTargetKind> {
        let selector = self.config.target.as_ref()?;
        let matches: Vec<_> = available_verify_targets(self.ir)
            .into_iter()
            .filter(|entry| selector.matches(entry.kind, &entry.name))
            .collect();
        match matches.as_slice() {
            [entry] => Some(entry.kind),
            _ => None,
        }
    }

    fn has_blocking_function_preflight_failure(&self) -> bool {
        self.results.iter().any(|result| {
            matches!(
                result,
                VerificationResult::FnContractFailed { .. } | VerificationResult::Unprovable { .. }
            )
        })
    }

    fn verify_props(&mut self) {
        if self.config.no_prop_verify || !target_kind_matches(self.config, VerifyTargetKind::Prop) {
            return;
        }
        let covered = self.covered_prop_names();
        for func in &self.ir.functions {
            self.verify_prop_function(func, &covered);
        }
    }

    fn covered_prop_names(&self) -> HashSet<String> {
        let mut covered = HashSet::new();
        for theorem in &self.ir.theorems {
            collect_def_refs_in_exprs(&theorem.shows, &mut covered);
            collect_def_refs_in_exprs(&theorem.invariants, &mut covered);
            let expanded: Vec<IRExpr> = theorem
                .shows
                .iter()
                .chain(theorem.invariants.iter())
                .map(|expr| expand_through_defs(expr, &self.defs))
                .collect();
            collect_def_refs_in_exprs(&expanded, &mut covered);
        }
        for verify in &self.ir.verifies {
            collect_def_refs_in_exprs(&verify.asserts, &mut covered);
            let expanded: Vec<IRExpr> = verify
                .asserts
                .iter()
                .map(|expr| expand_through_defs(expr, &self.defs))
                .collect();
            collect_def_refs_in_exprs(&expanded, &mut covered);
        }
        covered
    }

    fn verify_prop_function(&mut self, func: &IRFunction, covered: &HashSet<String>) {
        if !should_run_target(self.config, VerifyTargetKind::Prop, &func.name) {
            return;
        }
        let Some(target_system) = func.prop_target.as_ref() else {
            return;
        };
        if self.config.target.is_none() && covered.contains(&func.name) {
            return;
        }
        let result_name = format!("prop_{}", func.name);
        let Some(effective_config) =
            self.effective_config_for_target(&result_name, func.span, func.file.clone())
        else {
            return;
        };
        if let Some(result) = self.prop_preflight_result(func, &result_name) {
            self.push_result(result);
            return;
        }
        let start = Instant::now();
        let result = catch_verification_panic(
            &result_name,
            func.span,
            func.file.clone(),
            "verifying prop",
            || self.check_prop_function(func, target_system, &effective_config),
        );
        let result = result.with_time_ms(elapsed_ms(&start));
        self.push_result(result);
    }

    fn prop_preflight_result(
        &self,
        func: &IRFunction,
        result_name: &str,
    ) -> Option<VerificationResult> {
        if let Err(hint) = set_active_solver_family(self.solver_family) {
            return Some(
                unavailable_solver_result(result_name, hint)
                    .with_source(func.span, func.file.clone()),
            );
        }
        if func.ty != IRType::Bool {
            return Some(
                VerificationResult::Unprovable {
                    name: result_name.to_owned(),
                    hint: format!(
                        "internal error: prop `{}` has non-Bool return type {:?}",
                        func.name, func.ty
                    ),
                    span: None,
                    file: None,
                }
                .with_source(func.span, func.file.clone()),
            );
        }
        None
    }

    fn check_prop_function(
        &self,
        func: &IRFunction,
        target_system: &str,
        config: &VerifyConfig,
    ) -> VerificationResult {
        if config.bounded_only {
            return check_prop_bmc_fallback(
                self.ir,
                &self.vctx,
                &self.defs,
                func,
                target_system,
                config,
                self.deadline,
            );
        }
        let synthetic_theorem = synthetic_prop_theorem(func, target_system);
        let theorem_result = check_theorem_block(
            self.ir,
            &self.vctx,
            &self.defs,
            &synthetic_theorem,
            config,
            self.deadline,
        )
        .with_source(func.span, func.file.clone());
        if config.unbounded_only {
            theorem_result
        } else if matches!(theorem_result, VerificationResult::Unprovable { .. }) {
            check_prop_bmc_fallback(
                self.ir,
                &self.vctx,
                &self.defs,
                func,
                target_system,
                config,
                self.deadline,
            )
        } else if matches!(theorem_result, VerificationResult::Proved { .. }) {
            let bounded_result = check_prop_bmc_fallback(
                self.ir,
                &self.vctx,
                &self.defs,
                func,
                target_system,
                config,
                self.deadline,
            );
            if matches!(
                bounded_result,
                VerificationResult::Counterexample { .. } | VerificationResult::Deadlock { .. }
            ) {
                bounded_result
            } else {
                theorem_result
            }
        } else {
            theorem_result
        }
    }

    fn push_result_or_precondition_violation(
        &mut self,
        name: &str,
        span: Option<crate::span::Span>,
        file: Option<String>,
        result: VerificationResult,
    ) {
        if let Some(violation) = check_prop_precondition_obligations() {
            self.push_result(VerificationResult::Unprovable {
                name: name.to_owned(),
                hint: violation,
                span,
                file,
            });
        } else {
            self.push_result(result);
        }
    }
}

fn target_kind_matches(config: &VerifyConfig, kind: VerifyTargetKind) -> bool {
    config
        .target
        .as_ref()
        .is_none_or(|selector| selector.kind.is_none_or(|selected| selected == kind))
}

/// Extract the source span from an `IRExpr` (top-level only).
pub(super) fn expr_span(e: &IRExpr) -> Option<crate::span::Span> {
    match e {
        IRExpr::Lit { span, .. }
        | IRExpr::Var { span, .. }
        | IRExpr::Ctor { span, .. }
        | IRExpr::BinOp { span, .. }
        | IRExpr::UnOp { span, .. }
        | IRExpr::App { span, .. }
        | IRExpr::Lam { span, .. }
        | IRExpr::Let { span, .. }
        | IRExpr::Forall { span, .. }
        | IRExpr::Exists { span, .. }
        | IRExpr::One { span, .. }
        | IRExpr::Lone { span, .. }
        | IRExpr::Field { span, .. }
        | IRExpr::Prime { span, .. }
        | IRExpr::Always { span, .. }
        | IRExpr::Eventually { span, .. }
        | IRExpr::Until { span, .. }
        | IRExpr::Historically { span, .. }
        | IRExpr::Once { span, .. }
        | IRExpr::Previously { span, .. }
        | IRExpr::Since { span, .. }
        | IRExpr::Match { span, .. }
        | IRExpr::Choose { span, .. }
        | IRExpr::MapUpdate { span, .. }
        | IRExpr::Index { span, .. }
        | IRExpr::SetLit { span, .. }
        | IRExpr::SeqLit { span, .. }
        | IRExpr::Tuple { span, .. }
        | IRExpr::MapLit { span, .. }
        | IRExpr::SetComp { span, .. }
        | IRExpr::RelComp { span, .. }
        | IRExpr::Card { span, .. }
        | IRExpr::Assert { span, .. }
        | IRExpr::Assume { span, .. }
        | IRExpr::Sorry { span, .. }
        | IRExpr::Todo { span, .. }
        | IRExpr::Block { span, .. }
        | IRExpr::VarDecl { span, .. }
        | IRExpr::While { span, .. }
        | IRExpr::IfElse { span, .. }
        | IRExpr::Saw { span, .. }
        | IRExpr::Aggregate { span, .. } => *span,
    }
}

// ── Direct deadlock detection ( / revised) ──────────

/// Check for a global deadlock at the verification site.
///
/// Returns `Some(Deadlock)` when the verification site has stutter
/// opted out AND the BMC's transition relation is unsatisfiable from
/// the initial state for at least one step. Returns `None` otherwise.
///
/// The check is intentionally minimal: it builds a small (1-step)
/// pool, asserts the initial state, asserts a single transition, and
/// asks the SMT whether any valid event sequence exists from step 0
/// to step 1. Per (revised) and (revised), under
/// stutter-off the only legal trace step is a real event firing; if
/// every event is disabled at the initial state, that single
/// transition constraint is `false`, the solver returns UNSAT, and
/// we report a deadlock instead of letting downstream proof
/// techniques (1-induction, IC3, BMC) vacuously "prove" the property
/// from a contradictory transition relation.
///
/// **Limitation:** the current check only catches deadlock at the
/// initial state. Reaching-state deadlocks (system runs for a few
/// steps then deadlocks) still surface via the BMC's full-bound
/// trace-validity probe in `check_verify_block`. A more refined
/// per-step diagnostic per is bookmarked for /// (counterexample presentation).
fn check_for_deadlock(
    ir: &IRProgram,
    vctx: &VerifyContext,
    verify_block: &IRVerify,
    config: &VerifyConfig,
    deadline: Option<Instant>,
    witness_semantics: WitnessSemantics,
) -> Option<VerificationResult> {
    let system = transition::TransitionSystemSpec::for_verify_shallow(ir, vctx, verify_block)?;
    let encoding = match transition::TransitionSmtEncoding::from_plan(
        transition::TransitionExecutionPlan::for_deadlock_probe(system),
    ) {
        Ok(encoding) => encoding,
        Err(_) => return None,
    };
    let pool = encoding.pool();
    let solver = AbideSolver::new();
    if let Some(timeout_ms) = clamp_timeout_to_deadline(config.bmc_timeout_ms, deadline) {
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }
    } else {
        return Some(VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: verification_timeout_hint(config),
            span: verify_block.span,
            file: verify_block.file.clone(),
        });
    }

    for c in encoding.initial_constraints() {
        solver.assert(c);
    }
    for c in encoding.domain_constraints() {
        solver.assert(c);
    }
    for c in &encoding.fire_tracking().constraints {
        solver.assert(c);
    }

    match solver.check() {
        SatResult::Unsat => {
            let assert_span = if verify_block.asserts.len() == 1 {
                expr_span(&verify_block.asserts[0])
            } else {
                None
            };
            // Extract per-event diagnostics from the initial state.
            // Build a solver with just initial+domain (no transitions)
            // to get a model of the initial state.
            let diag_solver = AbideSolver::new();
            if let Some(timeout_ms) = clamp_timeout_to_deadline(config.bmc_timeout_ms, deadline) {
                if timeout_ms > 0 {
                    diag_solver.set_timeout(timeout_ms);
                }
            }
            for c in encoding.initial_constraints() {
                diag_solver.assert(c);
            }
            for c in encoding.domain_constraints() {
                diag_solver.assert(c);
            }
            let (event_diagnostics, evidence, evidence_extraction_error) =
                if let SatResult::Sat = diag_solver.check() {
                    let diagnostics = extract_deadlock_diagnostics(
                        &diag_solver,
                        pool,
                        vctx,
                        encoding.system().relevant_entities(),
                        encoding.system().relevant_systems(),
                        0,
                    );
                    let evidence = match witness_semantics {
                        WitnessSemantics::Operational => extract_initial_operational_deadlock(
                            &diag_solver,
                            pool,
                            vctx,
                            encoding.system().relevant_entities(),
                            encoding.system().relevant_systems(),
                        )
                        .and_then(operational_evidence),
                        WitnessSemantics::Relational => extract_initial_relational_deadlock(
                            &diag_solver,
                            pool,
                            vctx,
                            encoding.system().relevant_entities(),
                            encoding.system().relevant_systems(),
                        )
                        .and_then(relational_evidence),
                    };
                    match evidence {
                        Ok(evidence) => (diagnostics, Some(evidence), None),
                        Err(err) => (diagnostics, None, Some(err)),
                    }
                } else {
                    (vec![], None, None)
                };

            Some(VerificationResult::Deadlock {
                name: verify_block.name.clone(),
                evidence,
                evidence_extraction_error,
                step: 0,
                reason: "no events are enabled at the initial state and stutter is opted out"
                    .to_owned(),
                event_diagnostics,
                assumptions: build_assumptions_for_system_scope(
                    ir,
                    &verify_block
                        .systems
                        .iter()
                        .map(|s| s.name.clone())
                        .collect::<Vec<_>>(),
                    &verify_block.assumption_set,
                    &[],
                ),
                span: assert_span,
                file: None,
            })
        }
        SatResult::Sat | SatResult::Unknown(_) => None,
    }
}

/// Find the exact step where a deadlock occurs via linear scan.
///
/// Called when the full-bound BMC trace is UNSAT (some step within
/// `0..bound` deadlocks). Probes incrementally: for K = 1, 2,...,
/// builds a solver with K transition steps. When step K makes the
/// solver UNSAT, the deadlock is at state K (after K-1 valid
/// transitions). Returns the trace prefix from the K-1 SAT model
/// and per-event diagnostics at the deadlocked state.
/// Returns `None` if no confirming UNSAT was found (all probes
/// returned Unknown or the bound was exhausted without hitting UNSAT).
fn find_deadlock_step(ctx: DeadlockProbeCtx<'_>) -> Option<DeadlockProbeOutcome> {
    let DeadlockProbeCtx {
        ir,
        relevant_entities,
        relevant_systems,
        vctx,
        scope,
        store_ranges,
        verify_block,
        bound,
        config,
        witness_semantics,
    } = ctx;
    let selected_parts_for_bound = |bound| transition::TransitionSelectedParts {
        selected_system_names: relevant_systems
            .iter()
            .map(|sys| sys.name.clone())
            .collect(),
        relevant_entities: relevant_entities.to_vec(),
        relevant_systems: relevant_systems.to_vec(),
        slots_per_entity: scope.clone(),
        bound,
        store_ranges: store_ranges.clone(),
        activations: verify_block.activations.clone(),
        initial_constraints: verify_block.initial_constraints.clone(),
    };

    // We know step 0 is fine (check_for_deadlock passed).
    // Probe K = 1, 2,... until UNSAT.
    let mut last_sat_solver: Option<AbideSolver> = None;
    let mut last_sat_steps: Option<usize> = None;
    let mut deadlock_step: Option<usize> = None;

    for k in 1..=bound {
        let system = transition::TransitionSystemSpec::from_selected(
            ir,
            vctx,
            selected_parts_for_bound(k),
            &verify_block.assumption_set,
        )?;
        let encoding = transition::TransitionSmtEncoding::from_plan(
            transition::TransitionExecutionPlan::for_prefix_probe(system, k),
        )
        .ok()?;
        let probe_solver = AbideSolver::new();
        if config.bmc_timeout_ms > 0 {
            probe_solver.set_timeout(config.bmc_timeout_ms);
        }

        for c in encoding.initial_constraints() {
            probe_solver.assert(c);
        }
        for c in encoding.system_initial_constraints() {
            probe_solver.assert(c);
        }
        for c in encoding.domain_constraints() {
            probe_solver.assert(c);
        }
        let fire_tracking = encoding.fire_tracking();
        for c in &fire_tracking.constraints {
            probe_solver.assert(c);
        }

        match probe_solver.check() {
            SatResult::Sat => {
                last_sat_solver = Some(probe_solver);
                last_sat_steps = Some(k);
            }
            SatResult::Unsat => {
                deadlock_step = Some(k);
                break;
            }
            SatResult::Unknown(_) => {
                // Solver timeout/unknown — cannot confirm deadlock.
                // Keep probing; if no UNSAT is found, return None.
            }
        }
    }

    let ds = deadlock_step?;

    // Extract trace prefix from the last SAT model (K-1 steps).
    let (evidence, evidence_extraction_error) =
        if let (Some(ref sat_solver), Some(sat_steps)) = (&last_sat_solver, last_sat_steps) {
            let sat_system = transition::TransitionSystemSpec::from_selected(
                ir,
                vctx,
                selected_parts_for_bound(sat_steps),
                &verify_block.assumption_set,
            )?;
            let sat_encoding = transition::TransitionSmtEncoding::from_plan(
                transition::TransitionExecutionPlan::for_prefix_probe(sat_system, sat_steps),
            )
            .ok()?;
            let sat_pool = sat_encoding.pool();
            let sat_fire_tracking = sat_encoding.fire_tracking();
            let evidence = match witness_semantics {
                WitnessSemantics::Operational => extract_operational_deadlock_with_fire(
                    sat_solver,
                    sat_pool,
                    vctx,
                    relevant_entities,
                    relevant_systems,
                    sat_fire_tracking,
                    ds.saturating_sub(1),
                )
                .and_then(operational_evidence),
                WitnessSemantics::Relational => extract_relational_deadlock(
                    sat_solver,
                    sat_pool,
                    vctx,
                    relevant_entities,
                    relevant_systems,
                    ds.saturating_sub(1),
                )
                .and_then(relational_evidence),
            };
            match evidence {
                Ok(evidence) => (Some(evidence), None),
                Err(err) => (None, Some(err)),
            }
        } else {
            return None;
        };

    // Extract per-event diagnostics at the deadlocked state.
    let event_diagnostics =
        if let (Some(ref sat_solver), Some(sat_steps)) = (&last_sat_solver, last_sat_steps) {
            let sat_system = transition::TransitionSystemSpec::from_selected(
                ir,
                vctx,
                selected_parts_for_bound(sat_steps),
                &verify_block.assumption_set,
            )?;
            let sat_encoding = transition::TransitionSmtEncoding::from_plan(
                transition::TransitionExecutionPlan::for_prefix_probe(sat_system, sat_steps),
            )
            .ok()?;
            let sat_pool = sat_encoding.pool();
            extract_deadlock_diagnostics(
                sat_solver,
                sat_pool,
                vctx,
                relevant_entities,
                relevant_systems,
                ds.saturating_sub(1),
            )
        } else {
            vec![]
        };

    Some((ds, evidence, evidence_extraction_error, event_diagnostics))
}

// ── Tiered dispatch for verify blocks ───────────────────────────────

fn record_verify_assert_precondition_obligations(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
) {
    let (scope, system_names, bound, store_ranges) = compute_verify_scope(ir, verify_block);
    let (relevant_entities, relevant_systems) = select_verify_relevant(ir, &scope, &system_names);
    let pool_bound = bound.max(1);
    let pool =
        create_slot_pool_with_systems(&relevant_entities, &scope, pool_bound, &relevant_systems);

    for assert_expr in &verify_block.asserts {
        let _ = encode_property_at_step(
            &pool,
            vctx,
            defs,
            assert_expr,
            0,
            &store_ranges,
            &relevant_systems,
        );
    }
}

/// Check a verify block using tiered dispatch ():
///
/// 1. If asserts contain `eventually`, skip Tier 1 (liveness can't be proved by induction)
/// 2. **Tier 1a:** Try 1-induction with timeout — if PROVED, done
/// 3. **Tier 1b:** Try IC3/PDR — discovers strengthening invariants automatically
/// 4. **Tier 2:** Fall back to bounded model checking with `[0..N]` depth
///
/// The user writes the same `verify` block regardless of which tier succeeds.
fn check_verify_block_tiered(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> VerificationResult {
    // collect entity and system invariants in
    // scope and merge them into the verify block's asserts as
    // additional `Always`-wrapped properties. Each entity invariant
    // becomes `Always { Forall { __inv_self: E | rewritten_body } }`,
    // each system invariant becomes `Always { body }`. Per  // entity invariants travel; system invariants stay scoped.
    //
    // The downstream proof techniques (induction, IC3, BMC, lasso) are
    // unchanged — they walk `verify_block.asserts` as before. We
    // construct an in-memory clone with the invariants merged in.
    //
    // system invariants must stay scoped to
    // the LITERAL target systems, not the crosscall-expanded set —
    // otherwise a callee system's invariant silently leaks into the
    // caller's verify. Build `target_systems` from `verify_block.systems`
    // by name and pass it to `collect_in_scope_invariants` separately
    // from `relevant_entities`.
    let (scope, system_names, _bound, _store_ranges) = compute_verify_scope(ir, verify_block);
    // store_ranges captured above but unused in tiered dispatch — the
    // downstream proof paths (induction, IC3, BMC, lasso) each call
    // compute_verify_scope independently and thread store_ranges to
    // PropertyCtx when applicable.
    let (relevant_entities, _relevant_systems) = select_verify_relevant(ir, &scope, &system_names);
    let target_system_names: HashSet<String> = verify_block
        .systems
        .iter()
        .map(|vs| vs.name.clone())
        .collect();
    let target_systems: Vec<IRSystem> = ir
        .systems
        .iter()
        .filter(|s| target_system_names.contains(&s.name))
        .cloned()
        .collect();
    let invariant_asserts = collect_in_scope_invariants(defs, &relevant_entities, &target_systems);
    let verify_block_with_invariants;
    let effective_block = if invariant_asserts.is_empty() {
        verify_block
    } else {
        let mut merged_asserts = verify_block.asserts.clone();
        merged_asserts.extend(invariant_asserts);
        verify_block_with_invariants = IRVerify {
            name: verify_block.name.clone(),
            depth: verify_block.depth,
            systems: verify_block.systems.clone(),
            stores: verify_block.stores.clone(),
            assumption_set: verify_block.assumption_set.clone(),
            activations: verify_block.activations.clone(),
            initial_constraints: verify_block.initial_constraints.clone(),
            asserts: merged_asserts,
            span: verify_block.span,
            file: verify_block.file.clone(),
        };
        &verify_block_with_invariants
    };

    let verify_spec =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, effective_block, defs);
    let has_liveness = verify_spec
        .as_ref()
        .is_some_and(transition::TransitionVerifyObligation::has_liveness);

    record_verify_assert_precondition_obligations(ir, vctx, defs, effective_block);

    if !config.unbounded_only
        && effective_block.systems.is_empty()
        && effective_block.stores.is_empty()
    {
        if let Some(result) =
            relation_sat::try_check_static_relation_assertions(&effective_block.asserts)
        {
            return match result {
                Ok(relation_sat::StaticRelationOutcome::Checked) => VerificationResult::Checked {
                    name: effective_block.name.clone(),
                    depth: 0,
                    method: Some("relational RustSAT".to_owned()),
                    time_ms: 0,
                    assumptions: build_assumptions_for_system_scope(
                        ir,
                        &system_names,
                        &effective_block.assumption_set,
                        &[],
                    ),
                    backend_diagnostics: vec![],
                    span: effective_block.span,
                    file: effective_block.file.clone(),
                },
                Ok(relation_sat::StaticRelationOutcome::Counterexample {
                    witness,
                    witness_error,
                }) => {
                    let (evidence, evidence_extraction_error) = match witness {
                        Some(witness) => match relational_evidence(witness) {
                            Ok(evidence) => (Some(evidence), witness_error),
                            Err(err) => (None, Some(err)),
                        },
                        None => (None, witness_error),
                    };
                    VerificationResult::Counterexample {
                        name: effective_block.name.clone(),
                        evidence,
                        replay: None,
                        evidence_extraction_error,
                        assumptions: build_assumptions_for_system_scope(
                            ir,
                            &system_names,
                            &effective_block.assumption_set,
                            &[],
                        ),
                        span: effective_block.span,
                        file: effective_block.file.clone(),
                    }
                }
                Err(hint) => VerificationResult::Unprovable {
                    name: effective_block.name.clone(),
                    hint,
                    span: effective_block.span,
                    file: effective_block.file.clone(),
                },
            };
        }

        return check_static_verify_assertions(ir, vctx, defs, effective_block, config);
    }

    // When stutter is explicitly opted out, deadlock is part of the observable
    // result surface. Check it before optimized backends that can prove/check
    // "no property violation" but do not return deadlock as a distinct outcome.
    if !verify_block.assumption_set.stutter {
        if let Some(deadlock) = check_for_deadlock(
            ir,
            vctx,
            effective_block,
            config,
            deadline,
            config.witness_semantics,
        ) {
            return deadlock;
        }
    }

    let scoped_system_has_actions = effective_block.systems.iter().any(|scope| {
        ir.systems
            .iter()
            .any(|system| system.name == scope.name && !system.actions.is_empty())
    });
    let mut bounded_checked_result: Option<VerificationResult> = None;
    let mut backend_diagnostics: Vec<BackendDiagnostic> = Vec::new();

    if let Some(result) =
        explicit::try_check_verify_block_explicit(ir, vctx, defs, effective_block, config, deadline)
    {
        let explicit_result_has_witness = matches!(
            result,
            VerificationResult::Counterexample { .. }
                | VerificationResult::Deadlock { .. }
                | VerificationResult::LivenessViolation { .. }
        );
        let explicit_hit_temporal_fallback = matches!(
            &result,
            VerificationResult::Unprovable { hint, .. }
                if has_liveness && hint.contains("future-time temporal")
        );
        if !(config.witness_semantics == WitnessSemantics::Relational
            && explicit_result_has_witness)
        {
            if !explicit_hit_temporal_fallback
                && (config.bounded_only
                    || has_liveness
                    || !matches!(result, VerificationResult::Checked { .. }))
            {
                return result;
            }
            bounded_checked_result = Some(result);
        }
    }

    if effective_block.assumption_set.stutter && !has_liveness && !config.unbounded_only {
        let Some(relational_config) = clamp_config_to_deadline(config, deadline) else {
            return VerificationResult::Unprovable {
                name: effective_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: effective_block.span,
                file: effective_block.file.clone(),
            };
        };
        let (_scope, _system_names, bound, _store_ranges) =
            compute_verify_scope(ir, effective_block);
        if let Some(result) = relational::try_check_verify_block_relational(
            ir,
            effective_block,
            bound,
            relational_config.witness_semantics,
            relational_config.relational_symmetry_breaking,
        ) {
            match result {
                relational::RelationalVerifyOutcome::Checked { .. } if !config.bounded_only => {
                    // Keep the relational SAT backend as a bounded safety
                    // screen. If it only establishes the current bound, still
                    // allow stronger proof tiers to discharge the verify block
                    // as PROVED before falling back to CHECKED.
                    bounded_checked_result = Some(materialize_relational_verify_outcome(
                        ir,
                        effective_block,
                        bound,
                        result,
                    ));
                }
                result => {
                    return materialize_relational_verify_outcome(
                        ir,
                        effective_block,
                        bound,
                        result,
                    );
                }
            }
        }
    }

    let proof_search_enabled = config.unbounded_only || !config.no_ic3 || config.cvc5_sygus;

    // Tier 1a: Try induction only for explicit proof-search modes.
    if proof_search_enabled
        && !config.bounded_only
        && !has_liveness
        && active_solver_family() == SolverFamily::Z3
    {
        let Some(induction_config) = clamp_config_to_deadline(config, deadline) else {
            return VerificationResult::Unprovable {
                name: effective_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: effective_block.span,
                file: effective_block.file.clone(),
            };
        };
        if let Some(result) =
            try_induction_on_verify(ir, vctx, defs, effective_block, &induction_config)
        {
            return result;
        }
        // Induction failed or timed out — try IC3
    }

    // Tier 1b: Try IC3/PDR for ordinary verify blocks only when explicitly
    // enabled (unless bounded-only or liveness).
    if !config.bounded_only && !config.no_ic3 && !has_liveness {
        let Some(ic3_config) = clamp_config_to_deadline(config, deadline) else {
            return VerificationResult::Unprovable {
                name: effective_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: effective_block.span,
                file: effective_block.file.clone(),
            };
        };
        let attempt =
            try_ic3_on_verify_with_diagnostics(ir, vctx, defs, effective_block, &ic3_config);
        if let Some(result) = attempt.result {
            return result;
        }
        backend_diagnostics.extend(attempt.diagnostics);
        // IC3 failed — fall through to Tier 2
    }

    if config.cvc5_sygus
        && !config.bounded_only
        && !has_liveness
        && config.chc_selection != ChcSelection::Cvc5
    {
        let Some(sygus_config) = clamp_config_to_deadline(config, deadline) else {
            return VerificationResult::Unprovable {
                name: effective_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: effective_block.span,
                file: effective_block.file.clone(),
            };
        };
        if let Some(result) =
            try_cvc5_sygus_on_verify(ir, vctx, defs, effective_block, &sygus_config)
        {
            return result;
        }
    }

    if scoped_system_has_actions {
        if let Some(result) = bounded_checked_result {
            return attach_proof_mode_hint(
                attach_backend_diagnostics(result, &backend_diagnostics),
                config,
            );
        }
    }

    // Tier 2: Bounded model checking (unless unbounded-only)
    if config.unbounded_only {
        let techniques = if has_liveness {
            crate::messages::TIERED_LIVENESS_SKIP.to_owned()
        } else if config.no_ic3 {
            crate::messages::TIERED_NO_IC3.to_owned()
        } else {
            crate::messages::TIERED_BOTH_FAILED.to_owned()
        };
        return VerificationResult::Unprovable {
            name: effective_block.name.clone(),
            hint: format!("{techniques}, and --unbounded-only was specified"),
            span: None,
            file: None,
        };
    }

    // Liveness properties: lasso BMC first (finds violations), then reduction (proves)
    if has_liveness {
        // read fairness from the verification site's normalized
        // assumption set. The resolve pass in elab already restricted
        // each fair event reference to the verify block's scope, so the
        // assumption set entries are already trusted to lie inside
        // `verify_block.systems`.
        let has_fair_events = effective_block.assumption_set.has_fair_events();

        // Tier 2a: Try lasso BMC first — future-time temporal operators must
        // not fall through to the single-step safety encoder, even when no
        // fairness assumptions are present.
        let Some(bmc_config) = clamp_config_to_deadline(config, deadline) else {
            return VerificationResult::Unprovable {
                name: effective_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: effective_block.span,
                file: effective_block.file.clone(),
            };
        };
        let lasso_result = check_verify_block_lasso(ir, vctx, defs, effective_block, &bmc_config);
        match &lasso_result {
            VerificationResult::LivenessViolation { .. } => return lasso_result,
            VerificationResult::Checked { .. } => {
                // No violation found at this depth. Try reduction for PROVED
                // only when fairness assumptions provide a reduction target.
                if has_fair_events && !config.bounded_only {
                    let Some(reduction_config) = clamp_config_to_deadline(config, deadline) else {
                        return VerificationResult::Unprovable {
                            name: effective_block.name.clone(),
                            hint: verification_timeout_hint(config),
                            span: effective_block.span,
                            file: effective_block.file.clone(),
                        };
                    };
                    if let Some(proved) =
                        try_liveness_reduction(ir, vctx, defs, effective_block, &reduction_config)
                    {
                        return proved;
                    }
                }
                // Reduction failed or is not applicable — return CHECKED from lasso.
                return attach_proof_mode_hint(lasso_result, config);
            }
            _ => return lasso_result,
        }
    }

    let Some(bmc_config) = clamp_config_to_deadline(config, deadline) else {
        return VerificationResult::Unprovable {
            name: effective_block.name.clone(),
            hint: verification_timeout_hint(config),
            span: effective_block.span,
            file: effective_block.file.clone(),
        };
    };
    attach_proof_mode_hint(
        attach_backend_diagnostics(
            check_verify_block_with_depth_search(ir, vctx, defs, effective_block, &bmc_config),
            &backend_diagnostics,
        ),
        config,
    )
}

fn check_static_verify_assertions(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    let assumptions =
        build_assumptions_for_system_scope(ir, &[], &verify_block.assumption_set, &[]);
    if verify_block.asserts.is_empty() {
        return VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: 0,
            method: None,
            time_ms: 0,
            assumptions,
            backend_diagnostics: vec![],
            span: verify_block.span,
            file: verify_block.file.clone(),
        };
    }

    let solver = AbideSolver::new();
    if config.bmc_timeout_ms > 0 {
        solver.set_timeout(config.bmc_timeout_ms);
    }

    let env = HashMap::new();
    let mut negated = Vec::with_capacity(verify_block.asserts.len());
    for assertion in &verify_block.asserts {
        let Ok(encoded) = encode_pure_expr(assertion, &env, vctx, defs) else {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: "verify block did not produce a transition-system obligation".to_owned(),
                span: verify_block.span,
                file: verify_block.file.clone(),
            };
        };
        let Ok(prop) = encoded.to_bool() else {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: "static verify assertion did not encode as a boolean".to_owned(),
                span: expr_span(assertion),
                file: verify_block.file.clone(),
            };
        };
        negated.push(smt::bool_not(&prop));
    }

    let refs: Vec<&Bool> = negated.iter().collect();
    solver.assert(smt::bool_or(&refs));
    match solver.check() {
        SatResult::Sat => VerificationResult::Counterexample {
            name: verify_block.name.clone(),
            evidence: None,
            replay: None,
            evidence_extraction_error: None,
            assumptions,
            span: verify_block.span,
            file: verify_block.file.clone(),
        },
        SatResult::Unsat => VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: 0,
            method: None,
            time_ms: 0,
            assumptions,
            backend_diagnostics: vec![],
            span: verify_block.span,
            file: verify_block.file.clone(),
        },
        SatResult::Unknown(reason) => VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: format!("static verify assertion check was inconclusive: {reason}"),
            span: verify_block.span,
            file: verify_block.file.clone(),
        },
    }
}

fn try_cvc5_sygus_on_verify(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    if active_solver_family() != SolverFamily::Cvc5 {
        return None;
    }
    if !config.cvc5_sygus {
        return None;
    }
    if verify_block.asserts.is_empty() {
        return None;
    }

    let safety = transition::TransitionSafetySpec::for_verify(ir, vctx, verify_block, defs)?;
    let system = safety.system();
    if verify_block.systems.len() != 1 || system.relevant_systems().is_empty() {
        return None;
    }

    let combined_property = safety.combined_step_property()?;
    let root_name = &verify_block.systems[0].name;
    let mut root_system = system
        .relevant_systems()
        .iter()
        .find(|system| system.name == *root_name)
        .cloned()?;
    let mut sygus_systems = system.relevant_systems().to_vec();
    for system in &mut sygus_systems {
        system.invariants.clear();
    }
    root_system.invariants.clear();
    let sygus_result = if system.relevant_entities().is_empty() {
        sygus::try_cvc5_sygus_system_safety_opted_in(
            &root_system,
            &combined_property,
            config.induction_timeout_ms,
        )
    } else if !system.relevant_entities().is_empty() {
        let mut entities = system.relevant_entities().to_vec();
        for entity in &mut entities {
            entity.invariants.clear();
        }
        sygus::try_cvc5_sygus_multi_system_pooled_safety_opted_in(
            &root_system,
            &sygus_systems,
            &entities,
            system.slots_per_entity(),
            &combined_property,
            config.induction_timeout_ms,
        )
    } else {
        return None;
    };
    match sygus_result {
        transition::TransitionResult::Proved => Some(VerificationResult::Proved {
            name: verify_block.name.clone(),
            method: "CVC5 SyGuS invariant synthesis".to_owned(),
            time_ms: 0,
            assumptions: build_assumptions_for_system_scope(
                ir,
                &verify_block
                    .systems
                    .iter()
                    .map(|s| s.name.clone())
                    .collect::<Vec<_>>(),
                &verify_block.assumption_set,
                &[],
            ),
            span: None,
            file: None,
        }),
        transition::TransitionResult::Violated(_) => None,
        transition::TransitionResult::Unknown(hint) if config.unbounded_only => {
            Some(VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: format!("cvc5 SyGuS opt-in could not prove this verify block: {hint}"),
                span: verify_block.span,
                file: verify_block.file.clone(),
            })
        }
        transition::TransitionResult::Unknown(_) => None,
    }
}

/// Attempt to prove a verify block's asserts by 1-induction.
///
/// Returns `Some(Proved)` if all asserts are inductive.
/// Returns `None` if induction fails, times out, or can't be applied.
fn try_induction_on_verify(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();

    let obligation =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)?;
    let safety = obligation.safety();
    let system = safety.system();

    // No-stutter verify treats deadlock as an observable failure. The current
    // 1-induction obligation proves only assertion preservation over existing
    // transitions; it does not prove that every reachable state has a next
    // transition. Let the bounded path, which is deadlock-aware, own this
    // semantic surface until induction carries an explicit enabledness
    // obligation.
    if !system.assumptions().stutter() {
        return None;
    }

    if !induction_inputs_supported(safety) {
        return None;
    }

    if !prove_induction_base(safety, vctx, defs, config)? {
        return None;
    }
    if !prove_induction_step(safety, vctx, defs, config)? {
        return None;
    }

    Some(induction_proved_result(
        ir,
        verify_block,
        elapsed_ms(&start),
    ))
}

fn induction_inputs_supported(safety: &transition::TransitionSafetySpec<'_>) -> bool {
    let system = safety.system();
    for expr in safety.step_properties() {
        if find_unsupported_scene_expr(expr).is_some() {
            return false;
        }
    }
    for entity in system.relevant_entities() {
        for trans in &entity.transitions {
            if find_unsupported_scene_expr(&trans.guard).is_some() {
                return false;
            }
            if trans
                .updates
                .iter()
                .any(|update| find_unsupported_scene_expr(&update.value).is_some())
            {
                return false;
            }
        }
    }
    system.relevant_systems().iter().all(|system| {
        system.actions.iter().all(|event| {
            find_unsupported_scene_expr(&event.guard).is_none()
                && find_unsupported_in_actions(&event.body).is_none()
        })
    })
}

fn prove_induction_base(
    safety: &transition::TransitionSafetySpec<'_>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    config: &VerifyConfig,
) -> Option<bool> {
    let system = safety.system();
    let pool = create_slot_pool_with_systems(
        system.relevant_entities(),
        system.slots_per_entity(),
        0,
        system.relevant_systems(),
    );
    let solver = induction_solver(config);
    let initial_bindings =
        allocate_initial_activations(system.store_ranges(), system.activations()).ok()?;
    for c in initial_state_constraints_with_store_ranges(
        &pool,
        &initial_bindings.active_slots,
        system.store_ranges(),
    ) {
        solver.assert(&c);
    }
    for c in store_active_cardinality_constraints(&pool, system.store_ranges()) {
        solver.assert(&c);
    }
    for c in domain_constraints(&pool, vctx, system.relevant_entities()) {
        solver.assert(&c);
    }
    assert_negated_induction_properties(&solver, &pool, safety, vctx, defs, 0)?;
    Some(matches!(solver.check(), SatResult::Unsat))
}

fn prove_induction_step(
    safety: &transition::TransitionSafetySpec<'_>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    config: &VerifyConfig,
) -> Option<bool> {
    let system = safety.system();
    let encoding = transition::TransitionSmtEncoding::from_plan(
        transition::TransitionExecutionPlan::for_inductive_step(system.clone()),
    )
    .ok()?;
    let pool = encoding.pool();
    let solver = induction_solver(config);
    for c in encoding.domain_constraints() {
        solver.assert(c);
    }
    assert_induction_properties(&solver, pool, safety, vctx, defs, 0)?;
    for c in &encoding.fire_tracking().constraints {
        solver.assert(c);
    }
    assert_negated_induction_properties(&solver, pool, safety, vctx, defs, 1)?;
    Some(matches!(solver.check(), SatResult::Unsat))
}

fn induction_solver(config: &VerifyConfig) -> AbideSolver {
    let solver = AbideSolver::new();
    solver.set_timeout(config.induction_timeout_ms);
    solver
}

fn assert_induction_properties(
    solver: &AbideSolver,
    pool: &SlotPool,
    safety: &transition::TransitionSafetySpec<'_>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    step: usize,
) -> Option<()> {
    let system = safety.system();
    for expr in safety.step_properties() {
        let prop = encode_property_at_step(
            pool,
            vctx,
            defs,
            expr,
            step,
            system.store_ranges(),
            system.relevant_systems(),
        )
        .ok()?;
        solver.assert(&prop);
    }
    Some(())
}

fn assert_negated_induction_properties(
    solver: &AbideSolver,
    pool: &SlotPool,
    safety: &transition::TransitionSafetySpec<'_>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    step: usize,
) -> Option<()> {
    let system = safety.system();
    let mut negated = Vec::new();
    for expr in safety.step_properties() {
        let prop = encode_property_at_step(
            pool,
            vctx,
            defs,
            expr,
            step,
            system.store_ranges(),
            system.relevant_systems(),
        )
        .ok()?;
        negated.push(smt::bool_not(&prop));
    }
    if !negated.is_empty() {
        solver.assert(smt::bool_or(&negated.iter().collect::<Vec<_>>()));
    }
    Some(())
}

fn induction_proved_result(
    ir: &IRProgram,
    verify_block: &IRVerify,
    elapsed: u64,
) -> VerificationResult {
    VerificationResult::Proved {
        name: verify_block.name.clone(),
        method: "1-induction".to_owned(),
        time_ms: elapsed,
        assumptions: build_assumptions_for_system_scope(
            ir,
            &verify_block
                .systems
                .iter()
                .map(|s| s.name.clone())
                .collect::<Vec<_>>(),
            &verify_block.assumption_set,
            &[],
        ),
        span: None,
        file: None,
    }
}

// ── Liveness-to-Safety Reduction () ──────────────────────────

/// Try symmetry reduction for quantified liveness patterns.
///
/// Validates entity symmetry for each quantified pattern. Currently cannot
/// PROVE properties unboundedly — returns None to fall back to lasso BMC
/// (CHECKED) or UNPROVABLE.
///
/// IC3's BAS monitor encoding uses coarse justice tracking that is fundamentally
/// unsound for liveness: it under-approximates the accepting condition by
/// requiring all fair events to have fired, but doesn't account for events that
/// are never enabled (where fairness is vacuously satisfied). This causes false
/// PROVED results on systems with reachable dead states. No fixed-depth lasso
/// sanity check can compensate — the dead state may be arbitrarily deep.
///
/// Sound unbounded liveness proofs require either:
/// - A BAS encoding with per-event enabled tracking (IC3/Spacer struggles with
///   the additional CHC columns)
/// - k-liveness (Claessen & Sörensson) which sidesteps BAS entirely
/// - Manual proof via `axiom... by "file"`
fn quantified_liveness_symmetry_holds(
    ir: &IRProgram,
    patterns: &[(usize, LivenessPattern)],
    relevant_systems: &[IRSystem],
) -> bool {
    // Validate symmetry for each quantified entity type.
    // Even though we can't PROVE properties here, symmetry validation
    // is still useful for diagnostics and future k-liveness integration.
    for (_assert_idx, pattern) in patterns {
        let entity_name = match pattern {
            LivenessPattern::QuantifiedResponse { entity, .. }
            | LivenessPattern::QuantifiedRecurrence { entity, .. }
            | LivenessPattern::QuantifiedEventuality { entity, .. }
            | LivenessPattern::QuantifiedPersistence { entity, .. } => entity.as_str(),
            _ => continue,
        };

        if !validate_symmetry(entity_name, relevant_systems, &ir.systems, pattern) {
            return false;
        }
    }

    // Cannot prove quantified liveness unboundedly with current IC3 encoding.
    // Fall through to lasso BMC (CHECKED) or UNPROVABLE.
    true
}

/// Try to prove liveness properties in a verify block via
/// liveness-to-safety reduction (Biere-Artho-Schuppan 2002).
///
/// Reduces `always (P implies eventually Q)` to a safety property
/// `always (not accepting)` with monitor state, then proves the
/// safety property via 1-induction.
///
/// Returns `Some(Proved)` if the safety property holds unboundedly,
/// or `None` if the proof fails (caller falls back to lasso BMC).
pub(super) fn try_liveness_reduction(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();
    if !liveness_reduction_applicable(verify_block) {
        return None;
    }

    let obligation =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)?;
    let liveness = obligation.liveness()?;
    let system = obligation.system();
    let safety_obligations = liveness.safety_obligations().to_vec();
    if !liveness_transition_inputs_supported(system) {
        return None;
    }

    let safety_proved = |obligations: &[IRExpr]| {
        prove_liveness_safety_obligations(ir, vctx, defs, verify_block, config, obligations)
    };
    if prove_liveness_by_monitor_induction(
        vctx,
        defs,
        liveness,
        obligation.fair_event_keys(),
        config,
    )? && safety_proved(&safety_obligations)
    {
        return Some(liveness_reduction_result(
            ir,
            verify_block,
            crate::messages::LIVENESS_REDUCTION_METHOD,
            elapsed_ms(&start),
        ));
    }

    if prove_liveness_by_ic3(ir, system, liveness, config)? && safety_proved(&safety_obligations) {
        return Some(liveness_reduction_result(
            ir,
            verify_block,
            "liveness-to-safety (IC3/PDR)",
            elapsed_ms(&start),
        ));
    }

    None
}

fn liveness_reduction_applicable(verify_block: &IRVerify) -> bool {
    verify_block.assumption_set.has_fair_events()
        && verify_block.assumption_set.per_tuple.is_empty()
}

fn liveness_transition_inputs_supported(system: &transition::TransitionSystemSpec<'_>) -> bool {
    let entities_supported = system.relevant_entities().iter().all(|entity| {
        entity.transitions.iter().all(|transition| {
            find_unsupported_scene_expr(&transition.guard).is_none()
                && transition
                    .updates
                    .iter()
                    .all(|update| find_unsupported_scene_expr(&update.value).is_none())
        })
    });
    let systems_supported = system.relevant_systems().iter().all(|system| {
        system.actions.iter().all(|event| {
            find_unsupported_scene_expr(&event.guard).is_none()
                && find_unsupported_in_actions(&event.body).is_none()
        })
    });
    entities_supported && systems_supported
}

fn prove_liveness_by_monitor_induction(
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    liveness: &transition::TransitionLivenessSpec<'_>,
    fair_event_keys: &[(String, String)],
    config: &VerifyConfig,
) -> Option<bool> {
    let system = liveness.system();
    let encoding = match transition::TransitionSmtEncoding::from_plan(
        transition::TransitionExecutionPlan::for_inductive_step(system.clone()),
    ) {
        Ok(encoding) => encoding,
        Err(_) => return None,
    };
    let pool = encoding.pool();
    let fire_tracking = encoding.fire_tracking();
    let solver = AbideSolver::new();
    solver.set_timeout(config.induction_timeout_ms);

    for c in encoding.domain_constraints() {
        solver.assert(c);
    }
    for c in &fire_tracking.constraints {
        solver.assert(c);
    }

    let true_lit = IRExpr::Lit {
        ty: IRType::Bool,
        value: crate::ir::types::LitVal::Bool { value: true },
        span: None,
    };
    let monitor_ctx = LivenessMonitorBuildCtx {
        pool,
        vctx,
        defs,
        system,
        fair_event_keys,
        fire_tracking,
        solver: &solver,
        true_lit: &true_lit,
    };
    let accepting_vars_step1 = liveness_accepting_step1(liveness, &monitor_ctx)?;
    let any_accepting = bool_or_owned(&accepting_vars_step1);
    solver.assert(&any_accepting);
    Some(solver.check() == SatResult::Unsat)
}

struct LivenessMonitorBuildCtx<'a> {
    pool: &'a SlotPool,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    system: &'a transition::TransitionSystemSpec<'a>,
    fair_event_keys: &'a [(String, String)],
    fire_tracking: &'a harness::FireTracking,
    solver: &'a AbideSolver,
    true_lit: &'a IRExpr,
}

fn liveness_accepting_step1(
    liveness: &transition::TransitionLivenessSpec<'_>,
    ctx: &LivenessMonitorBuildCtx<'_>,
) -> Option<Vec<Bool>> {
    let mut accepting = Vec::new();
    for recipe in liveness.recipes() {
        accepting.extend(liveness_recipe_accepting_step1(recipe, ctx)?);
    }
    Some(accepting)
}

fn liveness_recipe_accepting_step1(
    recipe: &transition::TransitionLivenessMonitorRecipe,
    ctx: &LivenessMonitorBuildCtx<'_>,
) -> Option<Vec<Bool>> {
    (0..recipe.slot_count())
        .map(|target_slot| liveness_slot_accepting_step1(recipe, target_slot, ctx))
        .collect()
}

fn liveness_slot_accepting_step1(
    recipe: &transition::TransitionLivenessMonitorRecipe,
    target_slot: usize,
    ctx: &LivenessMonitorBuildCtx<'_>,
) -> Option<Bool> {
    let prefix = liveness_monitor_prefix(recipe, target_slot);
    let pending_0 = smt::bool_named(&format!("{prefix}_pending_t0"));
    let pending_1 = smt::bool_named(&format!("{prefix}_pending_t1"));
    let saved_state = liveness_saved_state(ctx.pool, ctx.system, &prefix);
    let justice = liveness_justice_vars(ctx.fair_event_keys, &prefix);
    let prop_ctx = liveness_property_ctx(recipe, target_slot);
    let trigger_0 = encode_prop_expr(
        ctx.pool,
        ctx.vctx,
        ctx.defs,
        &prop_ctx,
        recipe.trigger(ctx.true_lit),
        0,
    )
    .ok()?;
    let response_0 = encode_prop_expr(
        ctx.pool,
        ctx.vctx,
        ctx.defs,
        &prop_ctx,
        recipe.response(),
        0,
    )
    .ok()?;
    let trigger_fires = smt::bool_and(&[
        &smt::bool_not(&pending_0),
        &trigger_0,
        &smt::bool_not(&response_0),
    ]);
    let discharge = smt::bool_and(&[&pending_0, &response_0]);
    let pending_1_val = smt::bool_ite(
        &trigger_fires,
        &smt::bool_const(true),
        &smt::bool_ite(&discharge, &smt::bool_const(false), &pending_0),
    );
    ctx.solver.assert(smt::bool_eq(&pending_1, &pending_1_val));
    assert_liveness_saved_state_capture(ctx.solver, ctx.pool, &saved_state, &trigger_fires);
    assert_liveness_justice_progress(
        ctx.solver,
        ctx.fire_tracking,
        ctx.fair_event_keys,
        &justice,
        &trigger_fires,
    );
    let state_matches = liveness_state_matches(ctx.pool, &saved_state);
    let all_justice = bool_and_owned(&justice.step1);
    Some(smt::bool_and(&[&pending_1, &state_matches, &all_justice]))
}

fn liveness_monitor_prefix(
    recipe: &transition::TransitionLivenessMonitorRecipe,
    target_slot: usize,
) -> String {
    if recipe.is_quantified() {
        format!("mon{}_s{target_slot}", recipe.assert_index())
    } else {
        format!("mon{}", recipe.assert_index())
    }
}

struct LivenessSavedState {
    fields: Vec<(String, usize, String, SmtValue)>,
    active: Vec<(String, usize, SmtValue)>,
}

struct LivenessJusticeVars {
    step0: Vec<Bool>,
    step1: Vec<Bool>,
}

fn liveness_saved_state(
    pool: &SlotPool,
    system: &transition::TransitionSystemSpec<'_>,
    prefix: &str,
) -> LivenessSavedState {
    let mut fields = Vec::new();
    let mut active = Vec::new();
    for entity in system.relevant_entities() {
        for slot in 0..pool.slots_for(&entity.name) {
            for field in &entity.fields {
                let name = format!("{prefix}_saved_{}_s{}_{}", entity.name, slot, field.name);
                let var = match &field.ty {
                    IRType::Bool => smt::bool_var(&name),
                    IRType::Real | IRType::Float => smt::real_var(&name),
                    _ => smt::int_var(&name),
                };
                fields.push((entity.name.clone(), slot, field.name.clone(), var));
            }
            active.push((
                entity.name.clone(),
                slot,
                smt::bool_var(&format!("{prefix}_saved_{}_s{}_active", entity.name, slot)),
            ));
        }
    }
    LivenessSavedState { fields, active }
}

fn liveness_justice_vars(
    fair_event_keys: &[(String, String)],
    prefix: &str,
) -> LivenessJusticeVars {
    let step0 = fair_event_keys
        .iter()
        .enumerate()
        .map(|(i, _key)| smt::bool_named(&format!("{prefix}_justice{i}_t0")))
        .collect();
    let step1 = fair_event_keys
        .iter()
        .enumerate()
        .map(|(i, _key)| smt::bool_named(&format!("{prefix}_justice{i}_t1")))
        .collect();
    LivenessJusticeVars { step0, step1 }
}

fn liveness_property_ctx(
    recipe: &transition::TransitionLivenessMonitorRecipe,
    target_slot: usize,
) -> PropertyCtx {
    if let (Some(var), Some(ent_name)) = recipe.quantified_binding() {
        PropertyCtx::new().with_binding(var, ent_name, target_slot)
    } else {
        PropertyCtx::new()
    }
}

fn assert_liveness_saved_state_capture(
    solver: &AbideSolver,
    pool: &SlotPool,
    saved_state: &LivenessSavedState,
    trigger_fires: &Bool,
) {
    for (ent, slot, field, saved_var) in &saved_state.fields {
        if let Some(current) = pool.field_at(ent, *slot, field, 0) {
            let saved_val = smt::smt_ite(trigger_fires, current, saved_var);
            if let Ok(eq) = smt::smt_eq(&saved_val, saved_var) {
                solver.assert(&eq);
            }
        }
    }
    for (ent, slot, saved_act) in &saved_state.active {
        if let (Some(SmtValue::Bool(current)), SmtValue::Bool(saved_bool)) =
            (pool.active_at(ent, *slot, 0), saved_act)
        {
            let saved_val = smt::bool_ite(trigger_fires, current, saved_bool);
            solver.assert(smt::bool_eq(saved_bool, &saved_val));
        }
    }
}

fn assert_liveness_justice_progress(
    solver: &AbideSolver,
    fire_tracking: &harness::FireTracking,
    fair_event_keys: &[(String, String)],
    justice: &LivenessJusticeVars,
    trigger_fires: &Bool,
) {
    for (i, key) in fair_event_keys.iter().enumerate() {
        let fired_at_0 = fire_tracking
            .fire_vars
            .get(key)
            .and_then(|v| v.first())
            .cloned()
            .unwrap_or_else(|| smt::bool_const(false));
        let justice_val = smt::bool_ite(
            trigger_fires,
            &fired_at_0,
            &smt::bool_or(&[&justice.step0[i], &fired_at_0]),
        );
        solver.assert(smt::bool_eq(&justice.step1[i], &justice_val));
    }
}

fn liveness_state_matches(pool: &SlotPool, saved_state: &LivenessSavedState) -> Bool {
    let mut parts = Vec::new();
    for (ent, slot, field, saved_var) in &saved_state.fields {
        if let Some(current) = pool.field_at(ent, *slot, field, 1) {
            if let Ok(eq) = smt::smt_eq(saved_var, current) {
                parts.push(eq);
            }
        }
    }
    for (ent, slot, saved_act) in &saved_state.active {
        if let (Some(SmtValue::Bool(current)), SmtValue::Bool(saved_bool)) =
            (pool.active_at(ent, *slot, 1), saved_act)
        {
            parts.push(smt::bool_eq(saved_bool, current));
        }
    }
    bool_and_owned(&parts)
}

fn prove_liveness_by_ic3(
    ir: &IRProgram,
    system: &transition::TransitionSystemSpec<'_>,
    liveness: &transition::TransitionLivenessSpec<'_>,
    config: &VerifyConfig,
) -> Option<bool> {
    let has_quantified = liveness.has_quantified_patterns()
        || liveness
            .recipes()
            .iter()
            .any(|recipe| recipe.is_quantified());
    if has_quantified {
        let symmetric =
            quantified_liveness_symmetry_holds(ir, liveness.patterns(), system.relevant_systems());
        return symmetric.then_some(false);
    }
    debug_assert!(
        liveness
            .recipes()
            .iter()
            .all(|recipe| !recipe.is_quantified()),
        "quantified liveness recipes must not reach the IC3/BAS proof path"
    );
    for (recipe_index, recipe) in liveness.recipes().iter().enumerate() {
        for target_slot_idx in 0..recipe.slot_count() {
            let target_slot = recipe.is_quantified().then_some(target_slot_idx);
            let ic3_result = transition::solve_transition_obligation(liveness.obligation(
                recipe_index,
                target_slot,
                config.ic3_timeout_ms / 2,
            ));
            if !matches!(ic3_result, transition::TransitionResult::Proved) {
                return Some(false);
            }
        }
    }
    Some(true)
}

fn prove_liveness_safety_obligations(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
    safety_obligations: &[IRExpr],
) -> bool {
    if safety_obligations.is_empty() {
        return true;
    }
    let safety_verify = IRVerify {
        depth: None,
        name: verify_block.name.clone(),
        systems: verify_block.systems.clone(),
        stores: verify_block.stores.clone(),
        assumption_set: verify_block.assumption_set.clone(),
        activations: vec![],
        initial_constraints: vec![],
        asserts: safety_obligations.to_vec(),
        span: verify_block.span,
        file: verify_block.file.clone(),
    };
    let safety_proved =
        try_induction_on_verify(ir, vctx, defs, &safety_verify, config).or_else(|| {
            if config.no_ic3 {
                None
            } else {
                try_ic3_on_verify(ir, vctx, defs, &safety_verify, config)
            }
        });
    matches!(safety_proved, Some(VerificationResult::Proved { .. }))
}

fn liveness_reduction_result(
    ir: &IRProgram,
    verify_block: &IRVerify,
    method: &str,
    elapsed: u64,
) -> VerificationResult {
    VerificationResult::Proved {
        name: verify_block.name.clone(),
        method: method.to_owned(),
        time_ms: elapsed,
        assumptions: build_assumptions_for_system_scope(
            ir,
            &verify_block
                .systems
                .iter()
                .map(|s| s.name.clone())
                .collect::<Vec<_>>(),
            &verify_block.assumption_set,
            &[],
        ),
        span: None,
        file: None,
    }
}

fn bool_or_owned(vars: &[Bool]) -> Bool {
    if vars.len() == 1 {
        vars[0].clone()
    } else {
        smt::bool_or(&vars.iter().collect::<Vec<_>>())
    }
}

fn bool_and_owned(vars: &[Bool]) -> Bool {
    if vars.is_empty() {
        smt::bool_const(true)
    } else {
        smt::bool_and(&vars.iter().collect::<Vec<_>>())
    }
}

/// Try to prove a verify block using IC3/PDR via Z3's Spacer engine.
///
/// IC3 is more powerful than 1-induction: it automatically discovers
/// strengthening invariants, proving properties that aren't directly
/// inductive. Returns `Some(Proved)` if all asserts are proved, `None`
/// if any assert fails or can't be encoded.
fn try_ic3_on_verify(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    try_ic3_on_verify_with_diagnostics(ir, vctx, defs, verify_block, config).result
}

struct VerifyBackendAttempt {
    result: Option<VerificationResult>,
    diagnostics: Vec<BackendDiagnostic>,
}

fn try_ic3_on_verify_with_diagnostics(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerifyBackendAttempt {
    let start = Instant::now();

    // shared scope helper. IC3 also widens
    // slots based on quantifier depth, layered on top of the canonical scope.
    let Some(safety) = transition::TransitionSafetySpec::for_verify(ir, vctx, verify_block, defs)
    else {
        return VerifyBackendAttempt {
            result: None,
            diagnostics: vec![BackendDiagnostic::ic3_unknown(
                "verify block did not produce a transition-system obligation".to_owned(),
            )],
        };
    };
    let mut diagnostics = Vec::new();

    // Try IC3 on each assert — all must pass for PROVED
    // Try IC3 on each assert — all must pass for PROVED.
    // IC3 Violated always falls to BMC for verify blocks: BMC produces
    // confirmed counterexamples from concrete solver models, while IC3
    // traces come from the over-approximated CHC encoding (ForAll
    // per-slot independence can produce spurious intermediate states).
    for (property_index, _) in safety.step_properties().iter().enumerate() {
        let result = transition::solve_transition_obligation(
            safety.obligation(property_index, config.ic3_timeout_ms),
        );
        match result {
            transition::TransitionResult::Proved => {} // this assert proved, continue
            transition::TransitionResult::Violated(_) => {
                return VerifyBackendAttempt {
                    result: None,
                    diagnostics,
                };
            }
            transition::TransitionResult::Unknown(reason) => {
                diagnostics.push(BackendDiagnostic::ic3_unknown(reason));
                return VerifyBackendAttempt {
                    result: None,
                    diagnostics,
                };
            }
        }
    }

    let elapsed = elapsed_ms(&start);
    VerifyBackendAttempt {
        result: Some(VerificationResult::Proved {
            name: verify_block.name.clone(),
            method: "IC3/PDR".to_owned(),
            time_ms: elapsed,
            assumptions: build_assumptions_for_system_scope(
                ir,
                &verify_block
                    .systems
                    .iter()
                    .map(|s| s.name.clone())
                    .collect::<Vec<_>>(),
                &verify_block.assumption_set,
                &[],
            ),
            span: None,
            file: None,
        }),
        diagnostics,
    }
}

// ── BMC check for a single verify block ─────────────────────────────

/// Run bounded model checking on a single verify block.
///
/// 1. Build scope: `entity_name` → slot count from verify systems
/// 2. Create `SlotPool` with scope and bound
/// 3. Assert initial state, domain, and transition constraints
/// 4. Encode properties at every step
/// 5. Negate to search for counterexample
/// 6. UNSAT → CHECKED, SAT → COUNTEREXAMPLE
fn check_verify_block_with_depth_search(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    if !config.bmc_iterative_deepening {
        return check_verify_block(ir, vctx, defs, verify_block, config);
    }

    let Some(safety) = transition::TransitionSafetySpec::for_verify(ir, vctx, verify_block, defs)
    else {
        return check_verify_block(ir, vctx, defs, verify_block, config);
    };
    let final_bound = safety.system().bound();
    if final_bound <= 1 {
        return check_verify_block(ir, vctx, defs, verify_block, config);
    }

    for depth in 1..final_bound {
        let mut shallow_block = verify_block.clone();
        shallow_block.depth = Some(depth);
        let result = check_verify_block(ir, vctx, defs, &shallow_block, config);
        match result {
            VerificationResult::Counterexample { .. } | VerificationResult::Deadlock { .. } => {
                return result;
            }
            VerificationResult::Checked { .. } => {}
            _ => return result,
        }
    }

    check_verify_block(ir, vctx, defs, verify_block, config)
}

fn bmc_unknown_result(
    verify_block: &IRVerify,
    config: &VerifyConfig,
    solver_reason: &str,
) -> VerificationResult {
    let hint = if config.bmc_timeout_ms > 0 {
        let timeout_display = if config.bmc_timeout_ms >= 1000 {
            format!("{}s", config.bmc_timeout_ms / 1000)
        } else {
            format!("{}ms", config.bmc_timeout_ms)
        };
        format!(
            "Z3 timed out after {timeout_display} — try reducing bound, increasing --bmc-timeout, or simplifying property"
        )
    } else if solver_reason.is_empty() {
        crate::messages::BMC_UNKNOWN.to_owned()
    } else {
        format!("{}: {solver_reason}", crate::messages::BMC_UNKNOWN)
    };

    VerificationResult::Unprovable {
        name: verify_block.name.clone(),
        hint,
        span: None,
        file: None,
    }
}

fn check_verify_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    let start = Instant::now();
    let Some(safety) = bmc_safety_spec(ir, vctx, defs, verify_block) else {
        return verify_unprovable(
            verify_block,
            "verify block did not produce a transition-system obligation".to_owned(),
            verify_block.span,
        );
    };
    let system = safety.system();
    let bound = system.bound();

    if let Some(result) = relational::try_check_verify_block_relational(
        ir,
        verify_block,
        bound,
        config.witness_semantics,
        config.relational_symmetry_breaking,
    ) {
        return materialize_relational_verify_outcome(ir, verify_block, bound, result);
    }

    if let Some(result) = validate_bmc_inputs(verify_block, &safety) {
        return result;
    }

    let encoding = match bmc_transition_encoding(system, bound) {
        Ok(encoding) => encoding,
        Err(msg) => {
            return verify_unprovable(
                verify_block,
                format!("transition encoding error: {msg}"),
                None,
            )
        }
    };
    let pool = encoding.pool();
    let fire_tracking = encoding.fire_tracking();
    let solver = bmc_solver(config, &encoding);

    if let Some(result) = detect_bmc_deadlock(
        DeadlockBmcCtx {
            ir,
            vctx,
            system,
            verify_block,
            bound,
            config,
        },
        &solver,
    ) {
        return result;
    }

    let property_at_all_steps = match bmc_properties_all_steps(pool, vctx, defs, &safety) {
        Ok(prop) => prop,
        Err(msg) => return verify_unprovable(verify_block, format!("encoding error: {msg}"), None),
    };
    solver.assert(smt::bool_not(&property_at_all_steps));

    bmc_solver_result(
        BmcResultCtx {
            ir,
            vctx,
            system,
            verify_block,
            config,
            bound,
            started_at: start,
        },
        &solver,
        pool,
        fire_tracking,
    )
}

fn bmc_safety_spec<'a>(
    ir: &'a IRProgram,
    vctx: &'a VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
) -> Option<transition::TransitionSafetySpec<'a>> {
    transition::TransitionSafetySpec::for_verify(ir, vctx, verify_block, defs)
}

fn validate_bmc_inputs(
    verify_block: &IRVerify,
    safety: &transition::TransitionSafetySpec<'_>,
) -> Option<VerificationResult> {
    validate_bmc_asserts(verify_block, safety)
        .or_else(|| validate_bmc_transitions(verify_block, safety.system()))
        .or_else(|| validate_bmc_events(verify_block, safety.system()))
}

fn validate_bmc_asserts(
    verify_block: &IRVerify,
    safety: &transition::TransitionSafetySpec<'_>,
) -> Option<VerificationResult> {
    for (assert_expr, property) in verify_block.asserts.iter().zip(safety.step_properties()) {
        if let Some(kind) = find_unsupported_scene_expr(property) {
            return Some(verify_unprovable(
                verify_block,
                format!("unsupported expression kind in verify assert: {kind}"),
                expr_span(assert_expr),
            ));
        }
    }
    None
}

fn validate_bmc_transitions(
    verify_block: &IRVerify,
    system: &transition::TransitionSystemSpec<'_>,
) -> Option<VerificationResult> {
    for entity in system.relevant_entities() {
        for transition in &entity.transitions {
            if let Some(kind) = find_unsupported_scene_expr(&transition.guard) {
                return Some(verify_unprovable(
                    verify_block,
                    format!(
                        "unsupported expression in {}.{} guard: {kind}",
                        entity.name, transition.name
                    ),
                    None,
                ));
            }
            for update in &transition.updates {
                if let Some(kind) = find_unsupported_scene_expr(&update.value) {
                    return Some(verify_unprovable(
                        verify_block,
                        format!(
                            "unsupported expression in {}.{} update of {}: {kind}",
                            entity.name, transition.name, update.field
                        ),
                        None,
                    ));
                }
            }
        }
    }
    None
}

fn validate_bmc_events(
    verify_block: &IRVerify,
    system: &transition::TransitionSystemSpec<'_>,
) -> Option<VerificationResult> {
    for system in system.relevant_systems() {
        for event in &system.actions {
            if let Some(kind) = find_unsupported_scene_expr(&event.guard) {
                if kind != crate::messages::PRECHECK_UNRESOLVED_FN {
                    return Some(verify_unprovable(
                        verify_block,
                        format!(
                            "unsupported expression in {}.{} event guard: {kind}",
                            system.name, event.name
                        ),
                        None,
                    ));
                }
            }
            if let Some(kind) = find_unsupported_in_actions(&event.body) {
                return Some(verify_unprovable(
                    verify_block,
                    format!(
                        "unsupported expression in {}.{} event body: {kind}",
                        system.name, event.name
                    ),
                    None,
                ));
            }
        }
    }
    None
}

fn bmc_transition_encoding<'a>(
    system: &'a transition::TransitionSystemSpec<'a>,
    bound: usize,
) -> Result<transition::TransitionSmtEncoding<'a>, String> {
    transition::TransitionSmtEncoding::from_plan(transition::TransitionExecutionPlan::for_bmc(
        system.clone(),
        bound,
    ))
}

fn bmc_solver(
    config: &VerifyConfig,
    encoding: &transition::TransitionSmtEncoding<'_>,
) -> AbideSolver {
    let solver = AbideSolver::new();
    if config.bmc_timeout_ms > 0 {
        solver.set_timeout(config.bmc_timeout_ms);
    }
    for c in encoding.initial_constraints() {
        solver.assert(c);
    }
    for c in encoding.system_initial_constraints() {
        solver.assert(c);
    }
    for c in encoding.symmetry_constraints() {
        solver.assert(c);
    }
    for c in encoding.domain_constraints() {
        solver.assert(c);
    }
    for c in &encoding.fire_tracking().constraints {
        solver.assert(c);
    }
    solver
}

struct DeadlockBmcCtx<'a> {
    ir: &'a IRProgram,
    vctx: &'a VerifyContext,
    system: &'a transition::TransitionSystemSpec<'a>,
    verify_block: &'a IRVerify,
    bound: usize,
    config: &'a VerifyConfig,
}

fn detect_bmc_deadlock(
    ctx: DeadlockBmcCtx<'_>,
    solver: &AbideSolver,
) -> Option<VerificationResult> {
    if ctx.verify_block.assumption_set.stutter {
        return None;
    }
    match solver.check() {
        SatResult::Sat | SatResult::Unknown(_) => None,
        SatResult::Unsat => Some(localize_bmc_deadlock(ctx)),
    }
}

fn localize_bmc_deadlock(ctx: DeadlockBmcCtx<'_>) -> VerificationResult {
    let assert_span = single_assert_span(ctx.verify_block);
    if let Some((deadlock_step, evidence, evidence_extraction_error, event_diagnostics)) =
        find_deadlock_step(DeadlockProbeCtx {
            ir: ctx.ir,
            relevant_entities: ctx.system.relevant_entities(),
            relevant_systems: ctx.system.relevant_systems(),
            vctx: ctx.vctx,
            scope: ctx.system.slots_per_entity(),
            store_ranges: ctx.system.store_ranges(),
            verify_block: ctx.verify_block,
            bound: ctx.bound,
            config: ctx.config,
            witness_semantics: ctx.config.witness_semantics,
        })
    {
        return VerificationResult::Deadlock {
            name: ctx.verify_block.name.clone(),
            evidence,
            evidence_extraction_error,
            step: deadlock_step,
            reason: format!(
                "the system deadlocks at step {deadlock_step} — no events are enabled and stutter is opted out"
            ),
            event_diagnostics,
            assumptions: verify_assumptions(ctx.ir, ctx.verify_block),
            span: assert_span,
            file: None,
        };
    }
    verify_unprovable(
        ctx.verify_block,
        "the full-bound trace is unsatisfiable (possible reaching-state deadlock) but the solver could not localize the exact step".to_owned(),
        assert_span,
    )
}

fn bmc_properties_all_steps(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    safety: &transition::TransitionSafetySpec<'_>,
) -> Result<Bool, String> {
    let system = safety.system();
    encode_step_properties_all_steps(
        pool,
        vctx,
        defs,
        safety.step_properties(),
        system.bound(),
        system.store_ranges(),
        system.relevant_systems(),
    )
}

struct BmcResultCtx<'a> {
    ir: &'a IRProgram,
    vctx: &'a VerifyContext,
    system: &'a transition::TransitionSystemSpec<'a>,
    verify_block: &'a IRVerify,
    config: &'a VerifyConfig,
    bound: usize,
    started_at: Instant,
}

fn bmc_solver_result(
    ctx: BmcResultCtx<'_>,
    solver: &AbideSolver,
    pool: &SlotPool,
    fire_tracking: &harness::FireTracking,
) -> VerificationResult {
    match solver.check() {
        SatResult::Unsat => {
            let elapsed = elapsed_ms(&ctx.started_at);
            VerificationResult::Checked {
                name: ctx.verify_block.name.clone(),
                depth: ctx.bound,
                method: None,
                time_ms: elapsed,
                assumptions: verify_assumptions(ctx.ir, ctx.verify_block),
                backend_diagnostics: vec![],
                span: None,
                file: None,
            }
        }
        SatResult::Sat => bmc_counterexample(ctx, solver, pool, fire_tracking),
        SatResult::Unknown(reason) => bmc_unknown_result(ctx.verify_block, ctx.config, &reason),
    }
}

fn bmc_counterexample(
    ctx: BmcResultCtx<'_>,
    solver: &AbideSolver,
    pool: &SlotPool,
    fire_tracking: &harness::FireTracking,
) -> VerificationResult {
    let (evidence, replay) = match ctx.config.witness_semantics {
        WitnessSemantics::Operational => match extract_operational_counterexample_with_fire(
            solver,
            pool,
            ctx.vctx,
            ctx.system.relevant_entities(),
            ctx.system.relevant_systems(),
            fire_tracking,
            ctx.bound,
        ) {
            Ok(witness) => (
                operational_evidence(witness.clone()),
                Some(replay_counterexample_witness(
                    ctx.ir,
                    ctx.verify_block,
                    &witness,
                )),
            ),
            Err(err) => (Err(err), None),
        },
        WitnessSemantics::Relational => (
            extract_relational_counterexample(
                solver,
                pool,
                ctx.vctx,
                ctx.system.relevant_entities(),
                ctx.system.relevant_systems(),
                ctx.bound,
            )
            .and_then(relational_evidence),
            None,
        ),
    };
    let (evidence, evidence_extraction_error) = match evidence {
        Ok(evidence) => (Some(evidence), None),
        Err(err) => (None, Some(err)),
    };
    VerificationResult::Counterexample {
        name: ctx.verify_block.name.clone(),
        evidence,
        replay,
        evidence_extraction_error,
        assumptions: verify_assumptions(ctx.ir, ctx.verify_block),
        span: single_assert_span(ctx.verify_block),
        file: None,
    }
}

fn verify_unprovable(
    verify_block: &IRVerify,
    hint: String,
    span: Option<crate::span::Span>,
) -> VerificationResult {
    VerificationResult::Unprovable {
        name: verify_block.name.clone(),
        hint,
        span,
        file: None,
    }
}

fn single_assert_span(verify_block: &IRVerify) -> Option<crate::span::Span> {
    (verify_block.asserts.len() == 1)
        .then(|| expr_span(&verify_block.asserts[0]))
        .flatten()
}

fn verify_assumptions(ir: &IRProgram, verify_block: &IRVerify) -> Vec<TrustedAssumption> {
    build_assumptions_for_system_scope(
        ir,
        &verify_block
            .systems
            .iter()
            .map(|s| s.name.clone())
            .collect::<Vec<_>>(),
        &verify_block.assumption_set,
        &[],
    )
}

// ── Scene checking (SAT) ────────────────────────────────────────────
//
// Check a scene block by encoding given/when/then as a SAT problem.
// Scenes are existential: "does there exist an execution matching
// given+when that satisfies then?" This is the dual of verify blocks
// (which are universal).

// ── Lasso BMC for liveness properties ────────────────────────────────

/// Lasso-shaped BMC for liveness verification with fairness.
///
/// A lasso is a trace: s₀ → s₁ →... → `s_l` →... → `s_N` → `s_l` (loop back).
/// The solver searches for a lasso where the liveness property is violated
/// on the loop (P never holds at any step in the loop). If SAT, this is a
/// true infinite counterexample. If UNSAT, no violation exists at this bound.
///
/// Fairness: for each fair event, if it is enabled somewhere in the loop,
/// it must fire somewhere in the loop. This excludes degenerate stutter loops.
fn check_verify_block_lasso(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    let start = Instant::now();
    let Some(obligation) =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)
    else {
        return verify_unprovable(
            verify_block,
            "verify block did not produce a transition-system obligation".to_owned(),
            verify_block.span,
        );
    };
    let system = obligation.system();

    if system.slots_per_entity().is_empty() {
        // No entities — lasso BMC requires entity state for loop-back.
        // Fall back to linear BMC.
        return check_verify_block(ir, vctx, defs, verify_block, config);
    }
    let bound = system.bound();

    let encoding = match transition::TransitionSmtEncoding::from_plan(obligation.lasso_plan()) {
        Ok(encoding) => encoding,
        Err(msg) => {
            return verify_unprovable(
                verify_block,
                format!("lasso transition encoding error: {msg}"),
                None,
            )
        }
    };
    let pool = encoding.pool();
    let fire_tracking = encoding.fire_tracking();
    let solver = lasso_solver(config, &encoding);

    let Some(lasso) = encoding.lasso() else {
        return verify_unprovable(
            verify_block,
            "internal verifier error while encoding lasso loop".to_owned(),
            verify_block.span,
        );
    };
    for c in &lasso.constraints {
        solver.assert(c);
    }
    for c in encoding.fairness_constraints() {
        solver.assert(c);
    }

    let ctx = LassoCheckCtx {
        ir,
        vctx,
        defs,
        system,
        verify_block,
        config,
        bound,
        pool,
        fire_tracking,
        lasso,
    };
    if let Some(result) = check_lasso_asserts(&ctx, &solver) {
        return result;
    }

    VerificationResult::Checked {
        name: verify_block.name.clone(),
        depth: bound,
        method: None,
        time_ms: elapsed_ms(&start),
        assumptions: verify_assumptions(ir, verify_block),
        backend_diagnostics: vec![],
        span: None,
        file: None,
    }
}

fn lasso_solver(
    config: &VerifyConfig,
    encoding: &transition::TransitionSmtEncoding<'_>,
) -> AbideSolver {
    let solver = AbideSolver::new();
    if config.bmc_timeout_ms > 0 {
        solver.set_timeout(config.bmc_timeout_ms);
    }
    for c in encoding.initial_constraints() {
        solver.assert(c);
    }
    for c in encoding.system_initial_constraints() {
        solver.assert(c);
    }
    for c in encoding.symmetry_constraints() {
        solver.assert(c);
    }
    for c in encoding.domain_constraints() {
        solver.assert(c);
    }
    for c in &encoding.fire_tracking().constraints {
        solver.assert(c);
    }
    solver
}

struct LassoCheckCtx<'a> {
    ir: &'a IRProgram,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    system: &'a transition::TransitionSystemSpec<'a>,
    verify_block: &'a IRVerify,
    config: &'a VerifyConfig,
    bound: usize,
    pool: &'a SlotPool,
    fire_tracking: &'a harness::FireTracking,
    lasso: &'a harness::LassoLoop,
}

fn check_lasso_asserts(
    ctx: &LassoCheckCtx<'_>,
    solver: &AbideSolver,
) -> Option<VerificationResult> {
    for assert_expr in &ctx.verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, ctx.defs);
        let violation = match encode_lasso_liveness_violation(
            ctx.pool,
            ctx.vctx,
            ctx.defs,
            &expanded,
            &ctx.lasso.loop_indicators,
            ctx.bound,
        ) {
            Ok(violation) => violation,
            Err(msg) => {
                return Some(verify_unprovable(
                    ctx.verify_block,
                    format!("lasso encoding error: {msg}"),
                    expr_span(assert_expr),
                ));
            }
        };

        solver.push();
        solver.assert(&violation);
        let result = match solver.check() {
            SatResult::Sat => Some(lasso_violation_result(ctx, solver, assert_expr)),
            SatResult::Unknown(_) => Some(verify_unprovable(
                ctx.verify_block,
                crate::messages::BMC_UNKNOWN.to_owned(),
                expr_span(assert_expr),
            )),
            SatResult::Unsat => None,
        };
        solver.pop();
        if result.is_some() {
            return result;
        }
    }
    None
}

fn lasso_violation_result(
    ctx: &LassoCheckCtx<'_>,
    solver: &AbideSolver,
    assert_expr: &IRExpr,
) -> VerificationResult {
    let Some(loop_start) = lasso_model_loop_start(solver, &ctx.lasso.loop_indicators) else {
        return verify_unprovable(
            ctx.verify_block,
            "solver reported sat for liveness check but did not provide a model".to_owned(),
            expr_span(assert_expr),
        );
    };
    let evidence = lasso_evidence(ctx, solver, loop_start);
    let (evidence, evidence_extraction_error) = match evidence {
        Ok(evidence) => (Some(evidence), None),
        Err(err) => (None, Some(err)),
    };
    VerificationResult::LivenessViolation {
        name: ctx.verify_block.name.clone(),
        evidence,
        evidence_extraction_error,
        loop_start,
        fairness_analysis: extract_fairness_analysis(FairnessAnalysisCtx {
            witness: lasso_witness_ctx(ctx, solver),
            fire_tracking: ctx.fire_tracking,
            loop_start,
            bound: ctx.bound,
            assumption_set: &ctx.verify_block.assumption_set,
        }),
        assumptions: verify_assumptions(ctx.ir, ctx.verify_block),
        span: expr_span(assert_expr),
        file: None,
    }
}

fn lasso_model_loop_start(solver: &AbideSolver, loop_indicators: &[Bool]) -> Option<usize> {
    let model = solver.get_model()?;
    for (loop_start, indicator) in loop_indicators.iter().enumerate() {
        if let Some(true) = model
            .eval(indicator, true)
            .and_then(|value| value.as_bool())
        {
            return Some(loop_start);
        }
    }
    Some(0)
}

fn lasso_evidence(
    ctx: &LassoCheckCtx<'_>,
    solver: &AbideSolver,
    loop_start: usize,
) -> Result<EvidenceEnvelope, String> {
    match ctx.config.witness_semantics {
        WitnessSemantics::Operational => extract_operational_liveness_with_fire(
            &lasso_witness_ctx(ctx, solver),
            ctx.fire_tracking,
            ctx.bound,
            loop_start,
        )
        .and_then(operational_evidence),
        WitnessSemantics::Relational => extract_relational_liveness(
            solver,
            ctx.pool,
            ctx.vctx,
            ctx.system.relevant_entities(),
            ctx.system.relevant_systems(),
            ctx.bound,
            loop_start,
        )
        .and_then(relational_evidence),
    }
}

fn lasso_witness_ctx<'a>(
    ctx: &'a LassoCheckCtx<'a>,
    solver: &'a AbideSolver,
) -> WitnessExtractionCtx<'a> {
    WitnessExtractionCtx {
        solver,
        pool: ctx.pool,
        vctx: ctx.vctx,
        entities: ctx.system.relevant_entities(),
        systems: ctx.system.relevant_systems(),
    }
}

/// Encode a liveness violation condition for the lasso loop.
///
/// Recursively handles:
/// - `eventually P`: violation = P never holds on loop
/// - `always body`: strips Always, examines body for response patterns
/// - Entity quantifiers `all o: E | body`: expands over active slots
/// - `P implies eventually Q`: response pattern — P triggers, Q never responds
/// - Safety properties (no `eventually`): returns `false` (no lasso violation)
fn encode_lasso_liveness_violation(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    assert_expr: &IRExpr,
    loop_indicators: &[Bool],
    bound: usize,
) -> Result<Bool, String> {
    let ctx = PropertyCtx::new();
    encode_lasso_violation_inner(pool, vctx, defs, assert_expr, loop_indicators, bound, &ctx)
}

/// Inner recursive helper for lasso liveness violation encoding.
/// Carries a `PropertyCtx` for entity quantifier bindings.
fn encode_lasso_violation_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    expr: &IRExpr,
    loop_indicators: &[Bool],
    bound: usize,
    ctx: &PropertyCtx,
) -> Result<Bool, String> {
    // Entity quantifier: `all o: Entity | body` — expand over active slots
    // and check each for liveness violations (disjunction: ANY slot violated).
    // The active guard per step is handled inside the inner encoding
    // (response pattern guards P(t) with active(slot, t)).
    if let IRExpr::Forall {
        var,
        domain: crate::ir::types::IRType::Entity { name: entity_name },
        body,
        ..
    } = expr
    {
        let n_slots = pool.slots_for(entity_name);
        let mut slot_violations = Vec::new();
        for slot in 0..n_slots {
            let inner_ctx = ctx.with_binding(var, entity_name, slot);
            let v = encode_lasso_violation_inner(
                pool,
                vctx,
                defs,
                body,
                loop_indicators,
                bound,
                &inner_ctx,
            )?;
            let active_somewhere = {
                let mut active_terms = Vec::new();
                for step in 0..=bound {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(entity_name, slot, step) {
                        active_terms.push(active.clone());
                    }
                }
                if active_terms.is_empty() {
                    smt::bool_const(false)
                } else {
                    let refs: Vec<&Bool> = active_terms.iter().collect();
                    smt::bool_or(&refs)
                }
            };
            slot_violations.push(smt::bool_and(&[&active_somewhere, &v]));
        }
        if slot_violations.is_empty() {
            return Ok(smt::bool_const(false));
        }
        let refs: Vec<&Bool> = slot_violations.iter().collect();
        return Ok(smt::bool_or(&refs));
    }

    if contains_liveness(expr) {
        let violation_expr = negate_temporal_expr(expr);
        let compiled = CompiledTemporalFormula::from_expanded(violation_expr);
        if let Some(buchi) = compiled.buchi() {
            return encode_buchi_lasso_violation(
                pool,
                vctx,
                defs,
                buchi,
                loop_indicators,
                bound,
                ctx,
            );
        }
    }

    match expr {
        // `eventually P` — violation: P never holds on the loop
        IRExpr::Eventually { body, .. } => {
            let mut loop_violations = Vec::new();
            for (l, loop_ind) in loop_indicators.iter().enumerate() {
                let mut p_never = Vec::new();
                for step in l..=bound {
                    let p = encode_prop_expr(pool, vctx, defs, ctx, body, step)?;
                    p_never.push(smt::bool_not(&p));
                }
                let p_never_refs: Vec<&Bool> = p_never.iter().collect();
                let violation_at_l = smt::bool_and(&[loop_ind, &smt::bool_and(&p_never_refs)]);
                loop_violations.push(violation_at_l);
            }
            if loop_violations.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = loop_violations.iter().collect();
            Ok(smt::bool_or(&refs))
        }

        // `always body` — strip always, examine body for liveness patterns
        IRExpr::Always { body, .. } => {
            encode_lasso_violation_inner(pool, vctx, defs, body, loop_indicators, bound, ctx)
        }

        // `P implies eventually Q` — response pattern
        //
        // Violation on a lasso with loop l..bound:
        // P triggers at some step t (anywhere in trace) AND
        // Q never holds on the LOOP (steps l..bound).
        //
        // Since the loop repeats forever, Q absent from the loop means Q
        // never holds in the infinite future — regardless of where P triggered.
        // The trigger can be in the prefix (t < l) or on the loop (t >= l).
        //
        // Entity-bound triggers are guarded by the entity's active flag.
        //
        // Correct encoding: for each trigger step t, Q must be absent from
        // step t through the end of the trace [t, bound]. Since the trace
        // after step bound loops back to step l, and [t, bound] includes
        // the entire loop [l, bound], Q absent from [t, bound] means Q
        // never holds in the infinite future from the trigger point.
        //
        // Encoding: ∃l. loop_l ∧ ∃t ∈ [0,bound]. active(t) ∧ P(t) ∧ (∀s ∈ [t,bound]. ¬Q(s))
        IRExpr::BinOp {
            op,
            left: trigger,
            right: response_box,
            ..
        } if op == "OpImplies" => {
            if let IRExpr::Eventually { body: response, .. } = response_box.as_ref() {
                let mut loop_violations = Vec::new();
                for (l, loop_ind) in loop_indicators.iter().enumerate() {
                    // Precompute Q absence on the full loop [l, bound].
                    // Reused for all triggers at t ≥ l (loop-internal triggers
                    // wrap around: future is [t,bound] ∪ [l,t-1] = [l,bound]).
                    let mut q_loop_never = Vec::new();
                    for s in l..=bound {
                        let q = encode_prop_expr(pool, vctx, defs, ctx, response, s)?;
                        q_loop_never.push(smt::bool_not(&q));
                    }
                    let q_loop_refs: Vec<&Bool> = q_loop_never.iter().collect();
                    let q_absent_on_loop = smt::bool_and(&q_loop_refs);

                    // For each possible trigger step t in the full trace
                    let mut per_trigger = Vec::new();
                    for t in 0..=bound {
                        // Guard with entity active flags at step t
                        let mut guards = Vec::new();
                        for (entity_name, slot) in ctx.bindings.values() {
                            if let Some(SmtValue::Bool(act)) = pool.active_at(entity_name, *slot, t)
                            {
                                guards.push(act.clone());
                            }
                        }
                        let p = encode_prop_expr(pool, vctx, defs, ctx, trigger, t)?;
                        let p_guarded = if guards.is_empty() {
                            p
                        } else {
                            let guard_refs: Vec<&Bool> = guards.iter().collect();
                            smt::bool_and(&[&smt::bool_and(&guard_refs), &p])
                        };

                        // Q absent from the infinite future starting at step t.
                        //
                        // On the lasso s₀..s_l..s_bound → s_l:
                        // - Trigger in prefix (t < l): future = [t,l-1] ∪ loop.
                        // Q absent from [t, bound] covers both (since [t,bound] ⊇ loop).
                        // - Trigger on loop (t ≥ l): future wraps: [t,bound] ∪ [l,t-1].
                        // Q must be absent from the entire loop [l, bound].
                        //
                        // Combined: Q absent from [min(t, l), bound].
                        let q_absent = if t <= l {
                            // Prefix trigger: need Q absent from [t, l-1] AND on loop
                            if t < l {
                                let mut q_prefix = Vec::new();
                                for s in t..l {
                                    let q = encode_prop_expr(pool, vctx, defs, ctx, response, s)?;
                                    q_prefix.push(smt::bool_not(&q));
                                }
                                let prefix_refs: Vec<&Bool> = q_prefix.iter().collect();
                                smt::bool_and(&[&smt::bool_and(&prefix_refs), &q_absent_on_loop])
                            } else {
                                // t == l: just the loop
                                q_absent_on_loop.clone()
                            }
                        } else {
                            // Loop-internal trigger: Q absent on entire loop
                            q_absent_on_loop.clone()
                        };

                        per_trigger.push(smt::bool_and(&[&p_guarded, &q_absent]));
                    }
                    let trigger_refs: Vec<&Bool> = per_trigger.iter().collect();
                    let some_trigger_violated = smt::bool_or(&trigger_refs);

                    loop_violations.push(smt::bool_and(&[loop_ind, &some_trigger_violated]));
                }
                if loop_violations.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = loop_violations.iter().collect();
                return Ok(smt::bool_or(&refs));
            }
            // P implies Q (no eventually) — safety, not liveness
            Ok(smt::bool_const(false))
        }

        // Safety properties or other patterns — no lasso violation
        _ => Ok(smt::bool_const(false)),
    }
}

fn negate_temporal_expr(expr: &IRExpr) -> IRExpr {
    IRExpr::UnOp {
        op: "OpNot".to_owned(),
        operand: Box::new(expr.clone()),
        ty: crate::ir::types::IRType::Bool,
        span: expr_span(expr),
    }
}

fn encode_buchi_lasso_violation(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    buchi: &CompiledBuchiFormula,
    loop_indicators: &[Bool],
    bound: usize,
    ctx: &PropertyCtx,
) -> Result<Bool, String> {
    let automaton = buchi.automaton();
    if automaton.state_count() == 0 {
        return Ok(smt::bool_const(false));
    }

    let var_prefix = buchi_state_var_prefix(ctx);
    let state_vars = (0..=bound)
        .map(|step| {
            (0..automaton.state_count())
                .map(|state| smt::bool_named(&format!("{var_prefix}_s{state}_t{step}")))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut constraints = Vec::new();

    for step_vars in &state_vars {
        constraints.push(exactly_one_bool(step_vars));
    }

    let initial_refs = automaton
        .initial_states()
        .iter()
        .map(|state| &state_vars[0][*state])
        .collect::<Vec<_>>();
    constraints.push(smt::bool_or(&initial_refs));

    for (step, vars_at_step) in state_vars.iter().enumerate() {
        for (state_id, state_var) in vars_at_step.iter().enumerate() {
            let state_atoms = automaton.state_atoms(state_id);
            for atom in 0..buchi.atoms() {
                let Some(atom_expr) = buchi.atom_expr(atom) else {
                    return Err(format!(
                        "Büchi atom p{atom} is missing its source expression"
                    ));
                };
                let atom_value = encode_prop_expr(pool, vctx, defs, ctx, atom_expr, step)?;
                let required = if state_atoms.contains(&atom) {
                    atom_value
                } else {
                    smt::bool_not(&atom_value)
                };
                constraints.push(smt::bool_implies(state_var, &required));
            }
        }
    }

    for step in 0..bound {
        for (source, targets) in automaton.transitions().iter().enumerate() {
            let target_refs = targets
                .iter()
                .map(|target| &state_vars[step + 1][*target])
                .collect::<Vec<_>>();
            let target_disjunction = smt::bool_or(&target_refs);
            constraints.push(smt::bool_implies(
                &state_vars[step][source],
                &target_disjunction,
            ));
        }
    }

    for (loop_start, loop_ind) in loop_indicators.iter().enumerate() {
        for (source, targets) in automaton.transitions().iter().enumerate() {
            let target_refs = targets
                .iter()
                .map(|target| &state_vars[loop_start][*target])
                .collect::<Vec<_>>();
            let target_disjunction = smt::bool_or(&target_refs);
            let source_on_loop = smt::bool_and(&[loop_ind, &state_vars[bound][source]]);
            constraints.push(smt::bool_implies(&source_on_loop, &target_disjunction));
        }

        for acceptance_id in 0..automaton.acceptance_set_count() {
            let mut accepting_hits = Vec::new();
            for step_vars in state_vars.iter().take(bound + 1).skip(loop_start) {
                for (state, state_var) in step_vars.iter().enumerate() {
                    if automaton.state_satisfies_acceptance(state, acceptance_id) {
                        accepting_hits.push(state_var);
                    }
                }
            }
            let acceptance_seen = smt::bool_or(&accepting_hits);
            constraints.push(smt::bool_implies(loop_ind, &acceptance_seen));
        }
    }

    let refs = constraints.iter().collect::<Vec<_>>();
    Ok(smt::bool_and(&refs))
}

fn buchi_state_var_prefix(ctx: &PropertyCtx) -> String {
    let mut bindings = ctx
        .bindings
        .iter()
        .map(|(var, (entity, slot))| format!("{var}_{entity}_{slot}"))
        .collect::<Vec<_>>();
    bindings.sort();
    if bindings.is_empty() {
        "ltl_buchi".to_owned()
    } else {
        format!("ltl_buchi_{}", bindings.join("_"))
    }
}

fn exactly_one_bool(vars: &[Bool]) -> Bool {
    if vars.is_empty() {
        return smt::bool_const(false);
    }

    let mut constraints = Vec::new();
    let at_least_one = smt::bool_or(&vars.iter().collect::<Vec<_>>());
    constraints.push(at_least_one);

    for i in 0..vars.len() {
        for j in i + 1..vars.len() {
            constraints.push(smt::bool_not(&smt::bool_and(&[&vars[i], &vars[j]])));
        }
    }

    let refs = constraints.iter().collect::<Vec<_>>();
    smt::bool_and(&refs)
}

// ── Property encoding for BMC ───────────────────────────────────────

/// Expand an IR expression through the `DefEnv` — replace Var refs matching
/// nullary defs with their bodies, and App chains matching parameterized defs
/// with their beta-reduced bodies. Used to resolve pred/prop references in
/// given constraints before scanning for field references.
pub(super) fn expand_through_defs(expr: &IRExpr, defs: &defenv::DefEnv) -> IRExpr {
    if let Some(expanded) = expand_direct_def(expr, defs) {
        return expand_through_defs(&expanded, defs);
    }
    expand_expr_node(expr, defs)
}

fn expand_direct_def(expr: &IRExpr, defs: &defenv::DefEnv) -> Option<IRExpr> {
    if let IRExpr::Var { name, .. } = expr {
        if let Some(expanded) = defs.expand_var(name) {
            return Some(expanded);
        }
    }
    if let IRExpr::App { .. } = expr {
        if let Some(expanded) = defs.expand_app(expr) {
            return Some(expanded);
        }
    }
    None
}

fn expand_expr_node(expr: &IRExpr, defs: &defenv::DefEnv) -> IRExpr {
    if let Some(expanded) = expand_basic_expr_node(expr, defs) {
        return expanded;
    }
    match expr {
        IRExpr::Field {
            expr: inner,
            field,
            ty,
            ..
        } => {
            // try to expand as an entity-level
            // derived field reference. The receiver's expanded form
            // is what we look up the entity type on, since the inner
            // may itself be a chain that expands.
            let expanded_inner = expand_through_defs(inner, defs);
            if let Some(expanded) = defs.expand_entity_derived(&expanded_inner, field) {
                return expand_through_defs(&expanded, defs);
            }
            IRExpr::Field {
                expr: Box::new(expanded_inner),
                field: field.clone(),
                ty: ty.clone(),
                span: None,
            }
        }
        IRExpr::Prime { expr: inner, .. } => IRExpr::Prime {
            expr: Box::new(expand_through_defs(inner, defs)),
            span: None,
        },
        IRExpr::App { func, arg, ty, .. } => IRExpr::App {
            func: Box::new(expand_through_defs(func, defs)),
            arg: Box::new(expand_through_defs(arg, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Let { bindings, body, .. } => IRExpr::Let {
            bindings: bindings
                .iter()
                .map(|b| crate::ir::types::LetBinding {
                    name: b.name.clone(),
                    ty: b.ty.clone(),
                    expr: expand_through_defs(&b.expr, defs),
                })
                .collect(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Lam {
            param,
            param_type,
            body,
            ..
        } => IRExpr::Lam {
            param: param.clone(),
            param_type: param_type.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Match {
            scrutinee, arms, ..
        } => IRExpr::Match {
            scrutinee: Box::new(expand_through_defs(scrutinee, defs)),
            arms: arms
                .iter()
                .map(|arm| crate::ir::types::IRMatchArm {
                    pattern: arm.pattern.clone(),
                    guard: arm.guard.as_ref().map(|g| expand_through_defs(g, defs)),
                    body: expand_through_defs(&arm.body, defs),
                })
                .collect(),
            span: None,
        },
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            ..
        } => IRExpr::MapUpdate {
            map: Box::new(expand_through_defs(map, defs)),
            key: Box::new(expand_through_defs(key, defs)),
            value: Box::new(expand_through_defs(value, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Index { map, key, ty, .. } => IRExpr::Index {
            map: Box::new(expand_through_defs(map, defs)),
            key: Box::new(expand_through_defs(key, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Card { expr: inner, .. } => IRExpr::Card {
            expr: Box::new(expand_through_defs(inner, defs)),
            span: None,
        },
        IRExpr::SetComp {
            var,
            domain,
            source,
            filter,
            projection,
            ty,
            ..
        } => IRExpr::SetComp {
            var: var.clone(),
            domain: domain.clone(),
            source: source
                .as_ref()
                .map(|source| Box::new(expand_through_defs(source, defs))),
            filter: Box::new(expand_through_defs(filter, defs)),
            projection: projection
                .as_ref()
                .map(|p| Box::new(expand_through_defs(p, defs))),
            ty: ty.clone(),
            span: None,
        },
        // / — saw operator: expand defs in args.
        IRExpr::Saw {
            system_name,
            event_name,
            args,
            span,
        } => IRExpr::Saw {
            system_name: system_name.clone(),
            event_name: event_name.clone(),
            args: args
                .iter()
                .map(|a| a.as_ref().map(|e| Box::new(expand_through_defs(e, defs))))
                .collect(),
            span: *span,
        },
        _ => expr.clone(),
    }
}

fn expand_basic_expr_node(expr: &IRExpr, defs: &defenv::DefEnv) -> Option<IRExpr> {
    Some(match expr {
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => IRExpr::BinOp {
            op: op.clone(),
            left: expand_box(left, defs),
            right: expand_box(right, defs),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::UnOp {
            op, operand, ty, ..
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: expand_box(operand, defs),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Forall {
            var, domain, body, ..
        } => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Exists {
            var, domain, body, ..
        } => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::One {
            var, domain, body, ..
        } => IRExpr::One {
            var: var.clone(),
            domain: domain.clone(),
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Lone {
            var, domain, body, ..
        } => IRExpr::Lone {
            var: var.clone(),
            domain: domain.clone(),
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Always { body, .. } => IRExpr::Always {
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Eventually { body, .. } => IRExpr::Eventually {
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Until { left, right, .. } => IRExpr::Until {
            left: expand_box(left, defs),
            right: expand_box(right, defs),
            span: None,
        },
        IRExpr::Historically { body, .. } => IRExpr::Historically {
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Once { body, .. } => IRExpr::Once {
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Previously { body, .. } => IRExpr::Previously {
            body: expand_box(body, defs),
            span: None,
        },
        IRExpr::Since { left, right, .. } => IRExpr::Since {
            left: expand_box(left, defs),
            right: expand_box(right, defs),
            span: None,
        },
        IRExpr::Prime { expr: inner, .. } => IRExpr::Prime {
            expr: expand_box(inner, defs),
            span: None,
        },
        _ => return None,
    })
}

fn expand_box(expr: &IRExpr, defs: &defenv::DefEnv) -> Box<IRExpr> {
    Box::new(expand_through_defs(expr, defs))
}

/// Collect variable names referenced in an IR expression (for scene var tracking).
/// Looks for `Field(Var(name), _)` patterns — `res.id` means `res` is referenced.
fn collect_var_refs_in_expr(expr: &IRExpr, refs: &mut HashSet<String>) {
    match expr {
        IRExpr::Field { expr: inner, .. } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                refs.insert(name.clone());
            }
            collect_var_refs_in_expr(inner, refs);
        }
        IRExpr::BinOp { left, right, .. } => {
            collect_var_refs_in_expr(left, refs);
            collect_var_refs_in_expr(right, refs);
        }
        IRExpr::UnOp { operand, .. } => collect_var_refs_in_expr(operand, refs),
        IRExpr::App { func, arg, .. } => {
            collect_var_refs_in_expr(func, refs);
            collect_var_refs_in_expr(arg, refs);
        }
        _ => {}
    }
}

/// Scan action bodies for unsupported expression forms.
///
/// Walks Choose/ForAll/Apply/Create/CrossCall/ExprStmt and checks guards,
/// filters, create field values for unsupported expressions.
pub(super) fn find_unsupported_in_actions(actions: &[IRAction]) -> Option<&'static str> {
    for action in actions {
        match action {
            IRAction::Choose { filter, ops, .. } => {
                if let Some(kind) = find_unsupported_scene_expr(filter) {
                    return Some(kind);
                }
                if let Some(kind) = find_unsupported_in_actions(ops) {
                    return Some(kind);
                }
            }
            IRAction::ForAll { ops, .. } => {
                if let Some(kind) = find_unsupported_in_actions(ops) {
                    return Some(kind);
                }
            }
            IRAction::Create { fields, .. } => {
                for f in fields {
                    if let Some(kind) = find_unsupported_scene_expr(&f.value) {
                        return Some(kind);
                    }
                }
            }
            IRAction::ExprStmt { expr } => {
                if let Some(kind) = find_unsupported_scene_expr(expr) {
                    return Some(kind);
                }
            }
            IRAction::Apply { args, .. }
            | IRAction::CrossCall { args, .. }
            | IRAction::LetCrossCall { args, .. } => {
                for arg in args {
                    if let Some(kind) = find_unsupported_scene_expr(arg) {
                        return Some(kind);
                    }
                }
            }
            IRAction::Match { arms, .. } => {
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        if let Some(kind) = find_unsupported_scene_expr(guard) {
                            return Some(kind);
                        }
                    }
                    if let Some(kind) = find_unsupported_in_actions(&arm.body) {
                        return Some(kind);
                    }
                }
            }
        }
    }
    None
}

// ── Assumption formatting ────────────────────────────────────────────

/// Format an assumption list for display in verdict annotations.
/// Order: stutter first, then WF (alphabetical), then SF (alphabetical),
/// then lemmas, then axioms.
/// Returns empty string if the list is empty.
fn format_assumptions(assumptions: &[TrustedAssumption]) -> String {
    if assumptions.is_empty() {
        return String::new();
    }
    let mut parts: Vec<String> = Vec::new();

    // Stutter mode first
    if assumptions
        .iter()
        .any(|a| matches!(a, TrustedAssumption::DefaultStutter))
    {
        parts.push("default stutter".to_owned());
    } else if assumptions
        .iter()
        .any(|a| matches!(a, TrustedAssumption::Stutter))
    {
        parts.push("stutter".to_owned());
    } else if assumptions
        .iter()
        .any(|a| matches!(a, TrustedAssumption::NoStutter))
    {
        parts.push("no stutter".to_owned());
    }

    // Weak fairness (alphabetical, deduplicated)
    let mut wf: Vec<String> = assumptions
        .iter()
        .filter_map(|a| match a {
            TrustedAssumption::WeakFairness { system, command } => {
                Some(format!("WF {system}::{command}"))
            }
            TrustedAssumption::PerTupleWeakFairness { system, command } => {
                Some(format!("WF per-tuple {system}::{command}"))
            }
            _ => None,
        })
        .collect();
    wf.sort();
    wf.dedup();
    parts.extend(wf);

    // Strong fairness (alphabetical, deduplicated)
    let mut sf: Vec<String> = assumptions
        .iter()
        .filter_map(|a| match a {
            TrustedAssumption::StrongFairness { system, command } => {
                Some(format!("SF {system}::{command}"))
            }
            TrustedAssumption::PerTupleStrongFairness { system, command } => {
                Some(format!("SF per-tuple {system}::{command}"))
            }
            _ => None,
        })
        .collect();
    sf.sort();
    sf.dedup();
    parts.extend(sf);

    // Lemmas (deduplicated)
    let mut lemmas: Vec<&String> = assumptions
        .iter()
        .filter_map(|a| match a {
            TrustedAssumption::Lemma { name } => Some(name),
            _ => None,
        })
        .collect();
    lemmas.sort();
    lemmas.dedup();
    for l in lemmas {
        parts.push(format!("by {l}"));
    }

    // Axioms (deduplicated)
    let mut axioms: Vec<String> = assumptions
        .iter()
        .filter_map(|a| match a {
            TrustedAssumption::Axiom {
                name,
                proof_artifact,
            } => Some(match proof_artifact {
                Some(proof_artifact) if proof_artifact.is_checked() => {
                    format!(
                        "axiom {name} by \"{}\" (checked proof artifact)",
                        proof_artifact.locator()
                    )
                }
                Some(proof_artifact) => format!(
                    "axiom {name} by \"{}\" (unchecked trusted reference)",
                    proof_artifact.locator()
                ),
                None => format!("axiom {name}"),
            }),
            _ => None,
        })
        .collect();
    axioms.sort();
    axioms.dedup();
    parts.extend(axioms);

    let mut extern_assumes: Vec<String> = assumptions
        .iter()
        .filter_map(|a| match a {
            TrustedAssumption::ExternAssume { external, detail } => {
                Some(format!("extern {external} {detail}"))
            }
            _ => None,
        })
        .collect();
    extern_assumes.sort();
    extern_assumes.dedup();
    parts.extend(extern_assumes);

    if parts.is_empty() {
        String::new()
    } else {
        format!(" under {}", parts.join(", "))
    }
}

pub(super) fn proof_artifact_ref_for_locator(
    locator: &str,
    label: Option<&str>,
) -> Result<ProofArtifactRef, String> {
    let mut proof_artifact = ProofArtifactRef::new(locator)
        .map_err(|err| format!("invalid proof artifact locator `{locator}`: {err}"))?
        .checked(false);
    if let Some(label) = label {
        proof_artifact = proof_artifact.label(label.to_owned());
    }
    if let Some(backend) = infer_proof_artifact_backend(locator) {
        proof_artifact = proof_artifact.backend(backend);
    }
    Ok(proof_artifact)
}

pub(super) fn infer_proof_artifact_backend(locator: &str) -> Option<&'static str> {
    let ext = Path::new(locator).extension()?.to_str()?;
    match ext {
        "agda" | "agdai" => Some("agda"),
        "lean" | "olean" => Some("lean"),
        "v" | "vo" | "rocq" => Some("rocq"),
        "tlaps" => Some("tlaps"),
        _ => None,
    }
}

fn behavior_system_count(behavior: &op::Behavior) -> usize {
    let mut systems = HashSet::new();
    for state in behavior.states() {
        systems.extend(state.system_fields().keys().map(String::as_str));
    }
    for transition in behavior.transitions() {
        systems.extend(transition.atomic_steps().iter().map(op::AtomicStep::system));
    }
    systems.len()
}

fn write_trace_steps(
    f: &mut std::fmt::Formatter<'_>,
    steps: &[TraceStep],
    indent: &str,
) -> std::fmt::Result {
    for step in steps {
        if step.step == 0 {
            writeln!(f, "{indent}step 0: (initial)")?;
        } else if let Some(event) = &step.event {
            writeln!(f, "{indent}step {}: event {event}", step.step)?;
        } else {
            writeln!(f, "{indent}step {}:", step.step)?;
        }
        for (entity, field, value) in &step.assignments {
            writeln!(f, "{indent}  {entity}.{field} = {value}")?;
        }
    }
    Ok(())
}

fn format_relation_id(id: &rel::RelationId) -> String {
    match id {
        rel::RelationId::StoreExtent { store } => format!("store {store}"),
        rel::RelationId::Field { owner, field } => format!("{owner}.{field}"),
        rel::RelationId::Named { name } => name.clone(),
        rel::RelationId::Derived { name } => format!("derived {name}"),
    }
}

fn write_relational_state(
    f: &mut std::fmt::Formatter<'_>,
    state: &rel::RelationalState,
    indent: &str,
) -> std::fmt::Result {
    for relation in state.relation_instances() {
        writeln!(
            f,
            "{indent}relation {} (arity {}):",
            format_relation_id(relation.id()),
            relation.relation().arity()
        )?;
        for tuple in relation.relation().tuples() {
            let tuple_values = tuple
                .values()
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(f, "{indent}  ({tuple_values})")?;
        }
    }
    for (name, value) in state.evaluations() {
        writeln!(f, "{indent}eval {name} = {}", render_witness_value(value))?;
    }
    Ok(())
}

fn write_counterexample_evidence(
    f: &mut std::fmt::Formatter<'_>,
    evidence: Option<&EvidenceEnvelope>,
) -> std::fmt::Result {
    match evidence {
        Some(evidence) => {
            if let Some(countermodel) = evidence.as_countermodel() {
                if let Some(summary) = countermodel.summary_text() {
                    writeln!(f, "  countermodel: {summary}")?;
                }
                if let Some(backend) = countermodel.backend_name() {
                    writeln!(f, "  backend: {backend}")?;
                }
                for binding in countermodel.bindings() {
                    writeln!(
                        f,
                        "    {} = {}",
                        binding.name(),
                        render_witness_value(binding.value())
                    )?;
                }
                return Ok(());
            }
            if let Some(proof_artifact_ref) = evidence.as_proof_artifact_ref() {
                writeln!(f, "  proof artifact: {}", proof_artifact_ref.locator())?;
                if let Some(backend) = proof_artifact_ref.backend_name() {
                    writeln!(f, "  backend: {backend}")?;
                }
                if let Some(label) = proof_artifact_ref.label_text() {
                    writeln!(f, "  label: {label}")?;
                }
                if proof_artifact_ref.is_checked() {
                    writeln!(f, "  checked: true")?;
                } else {
                    writeln!(
                        f,
                        "  checked: false (unchecked trusted proof artifact reference)"
                    )?;
                }
                return Ok(());
            }
            if let Some(witness) = evidence.as_witness() {
                if let Some(operational) = witness.as_operational() {
                    let trace = behavior_to_trace_steps(
                        operational.behavior(),
                        behavior_system_count(operational.behavior()),
                    );
                    return write_trace_steps(f, &trace, "  ");
                }
                if let Some(relational) = witness.as_relational() {
                    match relational {
                        rel::RelationalWitness::Snapshot(state) => {
                            writeln!(f, "  state 0:")?;
                            write_relational_state(f, state, "    ")?;
                        }
                        rel::RelationalWitness::Temporal(witness) => {
                            for (idx, state) in witness.states().iter().enumerate() {
                                writeln!(f, "  state {idx}:")?;
                                write_relational_state(f, state, "    ")?;
                            }
                            if let Some(loop_start) = witness.loop_start() {
                                writeln!(f, "  [loops back to state {loop_start}]")?;
                            }
                        }
                    }
                    return Ok(());
                }
            }
            writeln!(f, "  [no native evidence available]")
        }
        None => writeln!(f, "  [no native evidence available]"),
    }
}

// ── Display ─────────────────────────────────────────────────────────

impl std::fmt::Display for VerificationResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationResult::Proved {
                name,
                method,
                time_ms,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                write!(f, "PROVED  {name} (method: {method}, {time_ms}ms{under})")
            }
            VerificationResult::Admitted {
                name,
                reason,
                time_ms,
                evidence,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                writeln!(f, "ADMITTED {name} ({reason}, {time_ms}ms{under})")?;
                if let Some(proof_artifact_ref) = evidence
                    .as_ref()
                    .and_then(EvidenceEnvelope::as_proof_artifact_ref)
                {
                    writeln!(f, "  proof artifact: {}", proof_artifact_ref.locator())?;
                    if let Some(backend) = proof_artifact_ref.backend_name() {
                        writeln!(f, "  backend: {backend}")?;
                    }
                    if let Some(label) = proof_artifact_ref.label_text() {
                        writeln!(f, "  label: {label}")?;
                    }
                    if proof_artifact_ref.is_checked() {
                        writeln!(f, "  checked: true")?;
                    } else {
                        writeln!(
                            f,
                            "  checked: false (unchecked trusted proof artifact reference)"
                        )?;
                    }
                }
                Ok(())
            }
            VerificationResult::Checked {
                name,
                depth,
                method,
                time_ms,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                if let Some(method) = method {
                    write!(
                        f,
                        "CHECKED {name} (method: {method}, bounded trace-prefix depth: {depth}, {time_ms}ms, depth may include stutter steps, not exhaustive reachable-state/all-instance coverage{under})"
                    )
                } else {
                    write!(
                        f,
                        "CHECKED {name} (bounded trace-prefix depth: {depth}, {time_ms}ms, depth may include stutter steps, not exhaustive reachable-state/all-instance coverage{under})"
                    )
                }
            }
            VerificationResult::Counterexample {
                name,
                evidence,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                writeln!(f, "COUNTEREXAMPLE {name}{under}")?;
                write_counterexample_evidence(f, evidence.as_ref())
            }
            VerificationResult::ScenePass { name, time_ms, .. } => {
                write!(f, "PASS    {name} ({time_ms}ms)")
            }
            VerificationResult::SceneFail { name, reason, .. } => {
                write!(f, "FAIL    {name}: {reason}")
            }
            VerificationResult::SceneUnknown { name, reason, .. } => {
                write!(f, "UNKNOWN {name}: {reason}")
            }
            VerificationResult::Unprovable { name, hint, .. } => {
                write!(f, "UNPROVABLE {name}: {hint}")
            }
            VerificationResult::FnContractProved { name, time_ms, .. } => {
                write!(f, "PROVED  fn {name} (contract, {time_ms}ms)")
            }
            VerificationResult::FnContractAdmitted {
                name,
                reason,
                time_ms,
                ..
            } => {
                write!(f, "ADMITTED fn {name} ({reason}, {time_ms}ms)")
            }
            VerificationResult::FnContractFailed {
                name,
                counterexample,
                ..
            } => {
                writeln!(f, "FAILED  fn {name} (contract violated)")?;
                for (param, value) in counterexample {
                    writeln!(f, "    {param} = {value}")?;
                }
                Ok(())
            }
            VerificationResult::LivenessViolation {
                name,
                evidence,
                loop_start,
                fairness_analysis,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                writeln!(f, "LIVENESS_VIOLATION {name}{under}")?;
                if let Some(operational) = evidence
                    .as_ref()
                    .and_then(EvidenceEnvelope::as_witness)
                    .and_then(WitnessEnvelope::as_operational)
                {
                    let trace = behavior_to_trace_steps(
                        operational.behavior(),
                        behavior_system_count(operational.behavior()),
                    );
                    let split_at = (*loop_start).min(trace.len());
                    if split_at > 0 {
                        writeln!(f, "  prefix (steps 0..{loop_start}):")?;
                        write_trace_steps(f, &trace[..split_at], "    ")?;
                    }
                    writeln!(f, "  loop (repeats forever):")?;
                    write_trace_steps(f, &trace[split_at..], "    ")?;
                    writeln!(f, "    [loops back to step {loop_start}]")?;
                } else if let Some(relational) = evidence
                    .as_ref()
                    .and_then(EvidenceEnvelope::as_witness)
                    .and_then(WitnessEnvelope::as_relational)
                {
                    if let Some(temporal) = relational.as_temporal() {
                        let split_at = (*loop_start).min(temporal.states().len());
                        if split_at > 0 {
                            writeln!(f, "  prefix (states 0..{loop_start}):")?;
                            for (idx, state) in temporal.states()[..split_at].iter().enumerate() {
                                writeln!(f, "    state {idx}:")?;
                                write_relational_state(f, state, "      ")?;
                            }
                        }
                        writeln!(f, "  loop (repeats forever):")?;
                        for (offset, state) in temporal.states()[split_at..].iter().enumerate() {
                            let idx = split_at + offset;
                            writeln!(f, "    state {idx}:")?;
                            write_relational_state(f, state, "      ")?;
                        }
                        writeln!(f, "    [loops back to state {loop_start}]")?;
                    } else {
                        writeln!(f, "  [native liveness evidence is not temporal]")?;
                    }
                } else {
                    writeln!(f, "  [no native evidence available]")?;
                }
                if !fairness_analysis.is_empty() {
                    writeln!(f, "  Loop fairness analysis:")?;
                    for fa in fairness_analysis {
                        let kind_str = match fa.kind {
                            FairnessKind::Weak => "WF",
                            FairnessKind::Strong => "SF",
                        };
                        let status_str = match fa.status {
                            FairnessStatus::EnabledAndFired => "ENABLED + FIRED",
                            FairnessStatus::EnabledButStarved => "ENABLED + NEVER FIRED",
                            FairnessStatus::NeverEnabled => "NEVER ENABLED",
                        };
                        writeln!(
                            f,
                            "    {kind_str} {}::{}: {status_str}",
                            fa.system, fa.event
                        )?;
                    }
                }
                Ok(())
            }
            VerificationResult::Deadlock {
                name,
                evidence,
                step,
                reason,
                event_diagnostics,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                writeln!(f, "DEADLOCK {name} (at step {step}: {reason}{under})")?;
                if let Some(operational) = evidence
                    .as_ref()
                    .and_then(EvidenceEnvelope::as_witness)
                    .and_then(WitnessEnvelope::as_operational)
                {
                    let trace = behavior_to_trace_steps(
                        operational.behavior(),
                        behavior_system_count(operational.behavior()),
                    );
                    write_trace_steps(f, &trace, "  ")?;
                } else if let Some(relational) = evidence
                    .as_ref()
                    .and_then(EvidenceEnvelope::as_witness)
                    .and_then(WitnessEnvelope::as_relational)
                {
                    match relational {
                        rel::RelationalWitness::Snapshot(state) => {
                            writeln!(f, "  state 0:")?;
                            write_relational_state(f, state, "    ")?;
                        }
                        rel::RelationalWitness::Temporal(witness) => {
                            for (idx, state) in witness.states().iter().enumerate() {
                                writeln!(f, "  state {idx}:")?;
                                write_relational_state(f, state, "    ")?;
                            }
                        }
                    }
                } else {
                    writeln!(f, "  [no native evidence available]")?;
                }
                writeln!(
                    f,
                    "  [no events enabled at step {step}; stutter is opted out]"
                )?;
                if !event_diagnostics.is_empty() {
                    writeln!(f, "  Event diagnostics:")?;
                    for diag in event_diagnostics {
                        writeln!(f, "    {}::{}: {}", diag.system, diag.event, diag.reason)?;
                    }
                }
                Ok(())
            }
        }
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests;
