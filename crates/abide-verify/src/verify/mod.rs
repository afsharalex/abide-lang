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
pub mod context;
pub mod defenv;
mod explicit;
pub mod harness;
pub mod ic3;
pub mod smt;
mod sygus;
mod temporal;
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
mod theorem;
#[allow(clippy::wildcard_imports)]
use theorem::*;
mod scene;
#[allow(clippy::wildcard_imports)]
use scene::*;
mod relational;
pub mod solver;

use std::collections::{HashMap, HashSet};
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;
use std::thread;
use std::time::{Duration, Instant};

use abide_witness::{op, rel, Countermodel, EvidenceEnvelope, ProofArtifactRef, WitnessEnvelope};
use serde::{Deserialize, Serialize};

use self::smt::{AbideSolver, Bool, SatResult};

use crate::ir::types::{IRAction, IRExpr, IRProgram, IRSystem, IRType, IRVerify};

pub use self::chc::ChcSelection;
use self::context::VerifyContext;
use self::harness::{
    create_slot_pool_with_systems, domain_constraints, initial_state_constraints, SlotPool,
};
use self::smt::SmtValue;
use self::solver::{
    active_solver_family, is_solver_family_available, set_active_solver_family, SolverFamily,
};
// ── Verification results ────────────────────────────────────────────

/// Per-event fairness analysis for lasso counterexamples ().
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

/// Weak or strong fairness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FairnessKind {
    Weak,
    Strong,
}

/// Fairness analysis for a single event in a lasso counterexample.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FairnessEventAnalysis {
    pub system: String,
    pub event: String,
    pub kind: FairnessKind,
    pub status: FairnessStatus,
}

/// Per-event diagnostic for a deadlocked state ().
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockEventDiag {
    pub system: String,
    pub event: String,
    pub reason: String,
}

/// An assumption that a verification verdict depends on.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TrustedAssumption {
    /// Stuttering assumption (`assume { stutter }`).
    Stutter,
    /// Weak fairness (`assume { fair Sys::cmd }`).
    WeakFairness { system: String, command: String },
    /// Strong fairness (`assume { strong fair Sys::cmd }`).
    StrongFairness { system: String, command: String },
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
    if set.stutter {
        out.push(TrustedAssumption::Stutter);
    }
    for wf in &set.weak_fair {
        out.push(TrustedAssumption::WeakFairness {
            system: wf.system.clone(),
            command: wf.command.clone(),
        });
    }
    for sf in &set.strong_fair {
        out.push(TrustedAssumption::StrongFairness {
            system: sf.system.clone(),
            command: sf.command.clone(),
        });
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

        for step in &system.steps {
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
            span: None,
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

/// Result of checking a single verification target.
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
        time_ms: u64,
        assumptions: Vec<TrustedAssumption>,
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
        evidence_extraction_error: Option<String>,
        assumptions: Vec<TrustedAssumption>,
        span: Option<crate::span::Span>,
        file: Option<String>,
    },
    /// Scene passed — the scenario is satisfiable and assertions hold.
    ScenePass {
        name: String,
        time_ms: u64,
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
                time_ms,
                assumptions,
                span,
                file,
            } => Self::Checked {
                name,
                depth,
                time_ms,
                assumptions,
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
                evidence_extraction_error,
                assumptions,
                span,
                file,
            } => Self::Counterexample {
                name,
                evidence,
                evidence_extraction_error,
                assumptions,
                span: span.or(block_span),
                file: file.or(block_file),
            },
            Self::ScenePass {
                name,
                time_ms,
                span,
                file,
            } => Self::ScenePass {
                name,
                time_ms,
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

    /// Is this a failure (counterexample, scene fail, fn contract fail, liveness violation, deadlock, or unprovable)?
    pub fn is_failure(&self) -> bool {
        matches!(
            self,
            Self::Counterexample { .. }
                | Self::SceneFail { .. }
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
            | Self::Unprovable { file, .. }
            | Self::FnContractProved { file, .. }
            | Self::FnContractAdmitted { file, .. }
            | Self::LivenessViolation { file, .. }
            | Self::FnContractFailed { file, .. }
            | Self::Deadlock { file, .. } => file.as_deref(),
        }
    }

    /// Result-level evidence payload, when available.
    pub fn evidence(&self) -> Option<&EvidenceEnvelope> {
        match self {
            Self::Admitted { evidence, .. }
            | Self::Counterexample { evidence, .. }
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
            | Self::Unprovable { .. }
            | Self::FnContractProved { .. }
            | Self::FnContractAdmitted { .. }
            | Self::FnContractFailed { .. } => &[],
        }
    }
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

// ── Configuration ───────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverSelection {
    Z3,
    Cvc5,
    Auto,
    Both,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WitnessSemantics {
    Operational,
    Relational,
}

/// Configuration for the verification pipeline.
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
    /// End-to-end timeout for the full verification command, in milliseconds.
    pub overall_timeout_ms: u64,
    /// Default BMC depth for auto-verified props (which lack explicit `[0..N]`).
    pub prop_bmc_depth: usize,
    /// Timeout for IC3/PDR attempts, in milliseconds.
    pub ic3_timeout_ms: u64,
    /// Skip IC3/PDR verification (for speed).
    pub no_ic3: bool,
    /// Skip automatic prop verification.
    pub no_prop_verify: bool,
    /// Skip function contract verification.
    pub no_fn_verify: bool,
    /// Print progress messages to stderr.
    pub progress: bool,
    /// Native witness family to prefer when multiple extraction paths exist.
    pub witness_semantics: WitnessSemantics,
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
            overall_timeout_ms: 1_200_000,
            prop_bmc_depth: 10,
            ic3_timeout_ms: 1_200_000,
            no_ic3: false,
            no_prop_verify: false,
            no_fn_verify: false,
            progress: false,
            witness_semantics: WitnessSemantics::Operational,
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

// ── Top-level verification entry point ──────────────────────────────

/// Verify all targets in an IR program.
///
/// Processes verify blocks (tiered: induction → IC3 → BMC), scene blocks (SAT),
/// and theorem blocks (IC3 → induction).
/// Returns one result per target, each carrying source location for diagnostic rendering.
#[allow(clippy::too_many_lines)]
pub fn verify_all(ir: &IRProgram, config: &VerifyConfig) -> Vec<VerificationResult> {
    let resolved_chc_family = match chc::resolve_chc_family(config.chc_selection) {
        Ok(family) => family,
        Err(hint) => {
            return vec![unavailable_solver_result("chc_backend", hint)];
        }
    };

    match config.solver_selection {
        SolverSelection::Z3 => verify_all_single(
            ir,
            config,
            SolverFamily::Z3,
            SolverFamily::Z3,
            resolved_chc_family,
        ),
        SolverSelection::Cvc5 => {
            if !is_solver_family_available(SolverFamily::Cvc5) {
                return vec![unavailable_solver_result(
                    "verification",
                    "requested solver `cvc5` is not available in this build".to_owned(),
                )];
            }
            verify_all_single(
                ir,
                config,
                SolverFamily::Cvc5,
                SolverFamily::Cvc5,
                resolved_chc_family,
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
            )
        }
        SolverSelection::Both => {
            if !is_solver_family_available(SolverFamily::Cvc5) {
                return vec![unavailable_solver_result(
                    "solver_backend_comparison",
                    "requested solver `both` requires the cvc5 backend to be available in this build"
                        .to_owned(),
                )];
            }
            let ir_z3 = ir.clone();
            let ir_cvc5 = ir.clone();
            let mut z3_config = config.clone();
            z3_config.solver_selection = SolverSelection::Z3;
            let mut cvc5_config = config.clone();
            cvc5_config.solver_selection = SolverSelection::Cvc5;

            let z3 = thread::spawn(move || {
                verify_all_single(
                    &ir_z3,
                    &z3_config,
                    SolverFamily::Z3,
                    SolverFamily::Z3,
                    resolved_chc_family,
                )
            });
            let cvc5 = thread::spawn(move || {
                verify_all_single(
                    &ir_cvc5,
                    &cvc5_config,
                    SolverFamily::Cvc5,
                    SolverFamily::Cvc5,
                    resolved_chc_family,
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

#[allow(clippy::too_many_lines)]
fn verify_all_single(
    ir: &IRProgram,
    config: &VerifyConfig,
    solver_family: SolverFamily,
    scene_solver_family: SolverFamily,
    chc_family: SolverFamily,
) -> Vec<VerificationResult> {
    match panic::catch_unwind(AssertUnwindSafe(|| {
        verify_all_single_impl(ir, config, solver_family, scene_solver_family, chc_family)
    })) {
        Ok(results) => results,
        Err(payload) => vec![VerificationResult::Unprovable {
            name: "verification".to_owned(),
            hint: internal_verifier_hint(
                &format!("running {} backend", solver_label(solver_family)),
                &panic_message(payload),
            ),
            span: None,
            file: None,
        }],
    }
}

#[allow(clippy::too_many_lines)]
fn verify_all_single_impl(
    ir: &IRProgram,
    config: &VerifyConfig,
    solver_family: SolverFamily,
    scene_solver_family: SolverFamily,
    chc_family: SolverFamily,
) -> Vec<VerificationResult> {
    if let Err(hint) = set_active_solver_family(solver_family) {
        return vec![unavailable_solver_result("verification", hint)];
    }
    if let Err(hint) = chc::set_active_chc_family(chc_family) {
        return vec![unavailable_solver_result("chc_backend", hint)];
    }
    let vctx = context::VerifyContext::from_ir(ir);
    let mut defs = defenv::DefEnv::from_ir(ir);
    let mut results = Vec::new();
    let deadline = verification_deadline(config);

    // Collect axiom names — axioms are trusted facts that apply globally,
    // so every verification result that depends on the DefEnv (which now
    // includes axiom bodies) should disclose them.
    let axiom_assumptions = build_axiom_assumptions(&ir.axioms);

    // ── Verify lemmas ─────────────────────────────────────────────
    // Lemmas are system-independent properties. Each body expression
    // must be a tautology. Processed first so proved lemmas are
    // available to verify blocks, scenes, and theorems via DefEnv.
    for lemma_block in &ir.lemmas {
        let Some(effective_config) = clamp_config_to_deadline(config, deadline) else {
            results.push(
                VerificationResult::Unprovable {
                    name: lemma_block.name.clone(),
                    hint: verification_timeout_hint(config),
                    span: lemma_block.span,
                    file: lemma_block.file.clone(),
                }
                .with_source(lemma_block.span, lemma_block.file.clone()),
            );
            continue;
        };
        if let Err(hint) = set_active_solver_family(solver_family) {
            results.push(
                unavailable_solver_result(&lemma_block.name, hint)
                    .with_source(lemma_block.span, lemma_block.file.clone()),
            );
            continue;
        }
        if config.progress {
            eprint!("Proving lemma {}...", lemma_block.name);
        }
        let result = catch_verification_panic(
            &lemma_block.name,
            lemma_block.span,
            lemma_block.file.clone(),
            "proving lemma",
            || {
                check_lemma_block(&vctx, &defs, lemma_block, &effective_config)
                    .with_source(lemma_block.span, lemma_block.file.clone())
            },
        );
        if config.progress {
            eprintln!(" done");
        }
        // If the lemma proved, add its body to DefEnv under its declared
        // name so later verify/scene/theorem blocks can reference it.
        if matches!(&result, VerificationResult::Proved { .. }) {
            defs.add_lemma_fact(&lemma_block.name, &lemma_block.body);
        }
        results.push(result);
    }

    for verify_block in &ir.verifies {
        let Some(effective_config) = clamp_config_to_deadline(config, deadline) else {
            results.push(VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: verify_block.span,
                file: verify_block.file.clone(),
            });
            continue;
        };
        if let Err(hint) = set_active_solver_family(solver_family) {
            results.push(
                unavailable_solver_result(&verify_block.name, hint)
                    .with_source(verify_block.span, verify_block.file.clone()),
            );
            continue;
        }
        if config.progress {
            eprint!("Checking {}...", verify_block.name);
        }
        clear_prop_precondition_obligations();
        clear_path_guard_stack();
        let result = catch_verification_panic(
            &verify_block.name,
            verify_block.span,
            verify_block.file.clone(),
            "checking verify block",
            || {
                check_verify_block_tiered(
                    ir,
                    &vctx,
                    &defs,
                    verify_block,
                    &effective_config,
                    deadline,
                )
                .with_source(verify_block.span, verify_block.file.clone())
            },
        );
        if config.progress {
            eprintln!(" done");
        }
        if let Some(violation) = check_prop_precondition_obligations() {
            results.push(VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: violation,
                span: verify_block.span,
                file: verify_block.file.clone(),
            });
        } else {
            results.push(result);
        }
    }

    for scene_block in &ir.scenes {
        let Some(effective_config) = clamp_config_to_deadline(config, deadline) else {
            results.push(VerificationResult::Unprovable {
                name: scene_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: scene_block.span,
                file: scene_block.file.clone(),
            });
            continue;
        };
        if config.progress {
            eprint!("Checking scene {}...", scene_block.name);
        }
        let result = catch_verification_panic(
            &scene_block.name,
            scene_block.span,
            scene_block.file.clone(),
            "checking scene block",
            || {
                if let Some(result) = relational::try_check_scene_block_relational(ir, scene_block)
                {
                    result.with_source(scene_block.span, scene_block.file.clone())
                } else {
                    if let Err(hint) = set_active_solver_family(scene_solver_family) {
                        return unavailable_solver_result(&scene_block.name, hint)
                            .with_source(scene_block.span, scene_block.file.clone());
                    }
                    check_scene_block(ir, &vctx, &defs, scene_block, &effective_config, deadline)
                        .with_source(scene_block.span, scene_block.file.clone())
                }
            },
        );
        if config.progress {
            eprintln!(" done");
        }
        results.push(result);
    }

    for theorem_block in &ir.theorems {
        let Some(effective_config) = clamp_config_to_deadline(config, deadline) else {
            results.push(VerificationResult::Unprovable {
                name: theorem_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: theorem_block.span,
                file: theorem_block.file.clone(),
            });
            continue;
        };
        if let Err(hint) = set_active_solver_family(solver_family) {
            results.push(
                unavailable_solver_result(&theorem_block.name, hint)
                    .with_source(theorem_block.span, theorem_block.file.clone()),
            );
            continue;
        }
        if config.progress {
            eprint!("Proving {}...", theorem_block.name);
        }
        clear_prop_precondition_obligations();
        clear_path_guard_stack();
        let result = catch_verification_panic(
            &theorem_block.name,
            theorem_block.span,
            theorem_block.file.clone(),
            "proving theorem",
            || {
                check_theorem_block(ir, &vctx, &defs, theorem_block, &effective_config, deadline)
                    .with_source(theorem_block.span, theorem_block.file.clone())
            },
        );
        if config.progress {
            eprintln!(" done");
        }
        if let Some(violation) = check_prop_precondition_obligations() {
            results.push(VerificationResult::Unprovable {
                name: theorem_block.name.clone(),
                hint: violation,
                span: theorem_block.span,
                file: theorem_block.file.clone(),
            });
        } else {
            results.push(result);
        }
    }

    // ── Verify function contracts ───────────────────────────────────
    // For each fn with ensures, prove that the body satisfies the
    // postcondition given the precondition.
    if !config.no_fn_verify {
        if let Err(hint) = set_active_solver_family(solver_family) {
            results.push(unavailable_solver_result("fn_verification", hint));
        } else {
            verify_fn_contracts(ir, &vctx, &defs, config, deadline, &mut results);
        }
    }

    // ── Auto-verify props ───────────────────────────────────────────
    // Props with a target system are implicit theorems: declaring a prop
    // means asserting it must hold (Dafny model).
    if !config.no_prop_verify {
        // Collect prop names already covered by explicit theorems/verify blocks.
        // Collect from both unexpanded (direct name refs like `Var("prop_name")`)
        // AND expanded forms (transitive refs: if p2's body references p1,
        // a theorem proving p2 also covers p1).
        let mut covered: HashSet<String> = HashSet::new();
        for thm in &ir.theorems {
            // Direct references
            collect_def_refs_in_exprs(&thm.shows, &mut covered);
            collect_def_refs_in_exprs(&thm.invariants, &mut covered);
            // Transitive references (after def expansion)
            let expanded: Vec<IRExpr> = thm
                .shows
                .iter()
                .chain(thm.invariants.iter())
                .map(|e| expand_through_defs(e, &defs))
                .collect();
            collect_def_refs_in_exprs(&expanded, &mut covered);
        }
        for vb in &ir.verifies {
            collect_def_refs_in_exprs(&vb.asserts, &mut covered);
            let expanded: Vec<IRExpr> = vb
                .asserts
                .iter()
                .map(|e| expand_through_defs(e, &defs))
                .collect();
            collect_def_refs_in_exprs(&expanded, &mut covered);
        }

        for func in &ir.functions {
            let Some(effective_config) = clamp_config_to_deadline(config, deadline) else {
                results.push(
                    VerificationResult::Unprovable {
                        name: format!("prop_{}", func.name),
                        hint: verification_timeout_hint(config),
                        span: func.span,
                        file: func.file.clone(),
                    }
                    .with_source(func.span, func.file.clone()),
                );
                continue;
            };
            // Props: have prop_target AND return Bool
            let Some(ref target_system) = func.prop_target else {
                continue;
            };
            if let Err(hint) = set_active_solver_family(solver_family) {
                results.push(
                    unavailable_solver_result(&format!("prop_{}", func.name), hint)
                        .with_source(func.span, func.file.clone()),
                );
                continue;
            }
            if func.ty != IRType::Bool {
                results.push(
                    VerificationResult::Unprovable {
                        name: format!("prop_{}", func.name),
                        hint: format!(
                            "internal error: prop `{}` has non-Bool return type {:?}",
                            func.name, func.ty
                        ),
                        span: None,
                        file: None,
                    }
                    .with_source(func.span, func.file.clone()),
                );
                continue;
            }
            if covered.contains(&func.name) {
                continue; // already checked via an explicit theorem/verify
            }

            if config.progress {
                eprint!("Verifying prop {}...", func.name);
            }
            let result = catch_verification_panic(
                &format!("prop_{}", func.name),
                func.span,
                func.file.clone(),
                "verifying prop",
                || {
                    let synthetic_theorem = crate::ir::types::IRTheorem {
                        name: format!("prop_{}", func.name),
                        systems: vec![target_system.clone()],
                        // Synthetic theorem for a top-level prop. Props are
                        // verified via the theorem path, so they get the
                        // theorem construct default (stutter on). Backends
                        // should treat this like any other theorem assumption set.
                        assumption_set:
                            crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
                        invariants: vec![],
                        shows: vec![IRExpr::Always {
                            body: Box::new(func.body.clone()),
                            span: None,
                        }],
                        by_file: None,
                        by_lemmas: vec![],
                        span: func.span,
                        file: func.file.clone(),
                    };
                    check_theorem_block(
                        ir,
                        &vctx,
                        &defs,
                        &synthetic_theorem,
                        &effective_config,
                        deadline,
                    )
                    .with_source(func.span, func.file.clone())
                },
            );
            if config.progress {
                eprintln!(" done");
            }
            results.push(result);
        }
    }

    // Amend all results with axiom assumptions — axioms are global trusted
    // facts that every verification result implicitly depends on.
    if !axiom_assumptions.is_empty() {
        results = results
            .into_iter()
            .map(|r| r.with_axioms(&axiom_assumptions))
            .collect();
    }

    results
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
        | IRExpr::MapLit { span, .. }
        | IRExpr::SetComp { span, .. }
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
fn find_deadlock_step(
    ir: &IRProgram,
    relevant_entities: &[crate::ir::types::IREntity],
    relevant_systems: &[IRSystem],
    vctx: &VerifyContext,
    scope: &HashMap<String, usize>,
    verify_block: &IRVerify,
    bound: usize,
    config: &VerifyConfig,
    witness_semantics: WitnessSemantics,
) -> Option<DeadlockProbeOutcome> {
    // We know step 0 is fine (check_for_deadlock passed).
    // Probe K = 1, 2,... until UNSAT.
    let mut last_sat_solver: Option<AbideSolver> = None;
    let mut last_sat_steps: Option<usize> = None;
    let mut deadlock_step: Option<usize> = None;

    for k in 1..=bound {
        let system = transition::TransitionSystemSpec::from_selected(
            ir,
            vctx,
            relevant_systems
                .iter()
                .map(|sys| sys.name.clone())
                .collect(),
            relevant_entities.to_vec(),
            relevant_systems.to_vec(),
            scope.clone(),
            k,
            HashMap::new(),
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
                relevant_systems
                    .iter()
                    .map(|sys| sys.name.clone())
                    .collect(),
                relevant_entities.to_vec(),
                relevant_systems.to_vec(),
                scope.clone(),
                sat_steps,
                HashMap::new(),
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
                relevant_systems
                    .iter()
                    .map(|sys| sys.name.clone())
                    .collect(),
                relevant_entities.to_vec(),
                relevant_systems.to_vec(),
                scope.clone(),
                sat_steps,
                HashMap::new(),
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
            depth: None,
            systems: verify_block.systems.clone(),
            stores: verify_block.stores.clone(),
            assumption_set: verify_block.assumption_set.clone(),
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

    if let Some(result) =
        explicit::try_check_verify_block_explicit(ir, vctx, defs, effective_block, config, deadline)
    {
        return result;
    }

    if !has_liveness && !config.unbounded_only {
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
        ) {
            return materialize_relational_verify_outcome(ir, effective_block, bound, result);
        }
    }

    // / revised: when stutter is opted out, check for
    // a global deadlock BEFORE running any proof technique. Without
    // this gate, both 1-induction and IC3 can vacuously prove `always
    // P` from a contradictory transition relation (`P ∧ false → P'`
    // is trivially true). The relational backend gets first refusal
    // above because its supported fragment may legally enable same-step
    // create/apply behavior that the generic SMT deadlock probe does
    // not model.
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

    if !config.bounded_only && !has_liveness {
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

    // Tier 1a: Try induction (unless bounded-only or liveness)
    if !config.bounded_only && !has_liveness {
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

    // Tier 1b: Try IC3/PDR (unless bounded-only, no-ic3, or liveness)
    if !config.bounded_only && !config.no_ic3 && !has_liveness {
        let Some(ic3_config) = clamp_config_to_deadline(config, deadline) else {
            return VerificationResult::Unprovable {
                name: effective_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: effective_block.span,
                file: effective_block.file.clone(),
            };
        };
        if let Some(result) = try_ic3_on_verify(ir, vctx, defs, effective_block, &ic3_config) {
            return result;
        }
        // IC3 failed — fall through to Tier 2
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

        if has_fair_events {
            // Tier 2a: Try lasso BMC first — finds violations quickly
            let Some(bmc_config) = clamp_config_to_deadline(config, deadline) else {
                return VerificationResult::Unprovable {
                    name: effective_block.name.clone(),
                    hint: verification_timeout_hint(config),
                    span: effective_block.span,
                    file: effective_block.file.clone(),
                };
            };
            let lasso_result =
                check_verify_block_lasso(ir, vctx, defs, effective_block, &bmc_config);
            match &lasso_result {
                VerificationResult::LivenessViolation { .. } => return lasso_result,
                VerificationResult::Checked { .. } => {
                    // No violation found at this depth. Try reduction for PROVED.
                    if !config.bounded_only {
                        let Some(reduction_config) = clamp_config_to_deadline(config, deadline)
                        else {
                            return VerificationResult::Unprovable {
                                name: effective_block.name.clone(),
                                hint: verification_timeout_hint(config),
                                span: effective_block.span,
                                file: effective_block.file.clone(),
                            };
                        };
                        if let Some(proved) = try_liveness_reduction(
                            ir,
                            vctx,
                            defs,
                            effective_block,
                            &reduction_config,
                        ) {
                            return proved;
                        }
                    }
                    // Reduction failed — return CHECKED from lasso
                    return lasso_result;
                }
                _ => return lasso_result,
            }
        }
        // No fair events — fall through to linear BMC.
    }

    let Some(bmc_config) = clamp_config_to_deadline(config, deadline) else {
        return VerificationResult::Unprovable {
            name: effective_block.name.clone(),
            hint: verification_timeout_hint(config),
            span: effective_block.span,
            file: effective_block.file.clone(),
        };
    };
    check_verify_block(ir, vctx, defs, effective_block, &bmc_config)
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
        sygus::try_cvc5_sygus_system_safety(
            &root_system,
            &combined_property,
            config.induction_timeout_ms,
        )
    } else if !system.relevant_entities().is_empty() {
        let mut entities = system.relevant_entities().to_vec();
        for entity in &mut entities {
            entity.invariants.clear();
        }
        sygus::try_cvc5_sygus_multi_system_pooled_safety(
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
        transition::TransitionResult::Violated(_) | transition::TransitionResult::Unknown(_) => {
            None
        }
    }
}

/// Attempt to prove a verify block's asserts by 1-induction.
///
/// Returns `Some(Proved)` if all asserts are inductive.
/// Returns `None` if induction fails, times out, or can't be applied.
#[allow(clippy::too_many_lines)]
fn try_induction_on_verify(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();

    let Some(obligation) =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)
    else {
        return None;
    };
    let safety = obligation.safety();
    let system = safety.system();

    // Pre-check: reject unsupported expressions in asserts AND transitions
    for expr in safety.step_properties() {
        if find_unsupported_scene_expr(expr).is_some() {
            return None;
        }
    }
    for entity in system.relevant_entities() {
        for trans in &entity.transitions {
            if find_unsupported_scene_expr(&trans.guard).is_some() {
                return None;
            }
            for upd in &trans.updates {
                if find_unsupported_scene_expr(&upd.value).is_some() {
                    return None;
                }
            }
        }
    }
    for sys in system.relevant_systems() {
        for event in &sys.steps {
            if find_unsupported_scene_expr(&event.guard).is_some() {
                return None;
            }
            if find_unsupported_in_actions(&event.body).is_some() {
                return None;
            }
        }
    }

    // ── Base case: P holds at step 0 ───────────────────────────────
    {
        let pool = create_slot_pool_with_systems(
            system.relevant_entities(),
            system.slots_per_entity(),
            0,
            system.relevant_systems(),
        );
        let solver = AbideSolver::new();
        solver.set_timeout(config.induction_timeout_ms);

        for c in initial_state_constraints(&pool) {
            solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, system.relevant_entities()) {
            solver.assert(&c);
        }

        let mut negated = Vec::new();
        for expr in safety.step_properties() {
            let Ok(prop) = encode_property_at_step(
                &pool,
                vctx,
                defs,
                expr,
                0,
                system.store_ranges(),
                system.relevant_systems(),
            ) else {
                return None;
            };
            negated.push(smt::bool_not(&prop));
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(smt::bool_or(&neg_refs));
        }

        match solver.check() {
            SatResult::Unsat => {} // base holds
            _ => return None,      // base fails or timeout — fall back
        }
    }

    // ── Step case: P(k) ∧ transition(k→k+1) → P(k+1) ─────────────
    {
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

        // Assume P at step 0
        for expr in safety.step_properties() {
            let Ok(prop) = encode_property_at_step(
                &pool,
                vctx,
                defs,
                expr,
                0,
                system.store_ranges(),
                system.relevant_systems(),
            ) else {
                return None;
            };
            solver.assert(&prop);
        }

        // One transition with command fire tracking. Bounded witness paths use
        // the command-level fire indicators as native provenance instead of
        // reconstructing events heuristically from state deltas.
        for c in &fire_tracking.constraints {
            solver.assert(c);
        }

        // when stutter is opted out, the transition relation
        // can be unsatisfiable from the initial state (no events
        // enabled, no stutter to fall back on). Without this guard,
        // induction would prove the property "vacuously" — `P ∧ false
        // → P'` is trivially true — and silently mask the deadlock.
        // Bail out to BMC, which has explicit deadlock detection.
        if !system.assumptions().stutter() {
            match solver.check() {
                SatResult::Unsat => return None,
                SatResult::Sat | SatResult::Unknown(_) => {}
            }
        }

        // Assert NOT P at step 1
        let mut negated = Vec::new();
        for expr in safety.step_properties() {
            let Ok(prop) = encode_property_at_step(
                &pool,
                vctx,
                defs,
                expr,
                1,
                system.store_ranges(),
                system.relevant_systems(),
            ) else {
                return None;
            };
            negated.push(smt::bool_not(&prop));
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(smt::bool_or(&neg_refs));
        }

        match solver.check() {
            SatResult::Unsat => {} // step holds
            _ => return None,      // step fails or timeout — fall back
        }
    }

    // Both passed — PROVED
    let elapsed = elapsed_ms(&start);
    Some(VerificationResult::Proved {
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
    })
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
#[allow(clippy::too_many_arguments)]
fn try_symmetry_reduction(
    ir: &IRProgram,
    _vctx: &VerifyContext,
    _defs: &defenv::DefEnv,
    patterns: &[(usize, LivenessPattern)],
    _safety_obligations: &[IRExpr],
    _system_names: &[String],
    _scope: &HashMap<String, usize>,
    _fair_event_keys: &[(String, String)],
    relevant_systems: &[IRSystem],
    _config: &VerifyConfig,
    _start: &Instant,
    _verify_block: &IRVerify,
) -> Option<VerificationResult> {
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
            return None; // symmetry broken
        }
    }

    // Cannot prove quantified liveness unboundedly with current IC3 encoding.
    // Fall through to lasso BMC (CHECKED) or UNPROVABLE.
    None
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
#[allow(clippy::too_many_lines)]
pub(super) fn try_liveness_reduction(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> Option<VerificationResult> {
    let start = Instant::now();

    // read fairness from the verification site's normalized
    // assumption set (populated by ). Liveness reduction can
    // only prove eventualities under fairness — without any fair events
    // declared, there's nothing to discharge against and we bail out.
    if !verify_block.assumption_set.has_fair_events() {
        return None; // can't prove liveness without fairness
    }

    // parameterized fair events default to per-tuple
    // semantics. The unbounded reduction path here builds one justice
    // bit per (system, event), not per (event, args) tuple, so it
    // cannot discharge per-tuple obligations as the user wrote them.
    // Per and, sound unbounded per-tuple liveness
    // requires k-liveness (). Until then, fall through to
    // bounded lasso BMC and report CHECKED — never PROVED — when any
    // fair event in scope is parameterized.
    if !verify_block.assumption_set.per_tuple.is_empty() {
        return None;
    }

    let Some(obligation) =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)
    else {
        return None;
    };
    let Some(liveness) = obligation.liveness() else {
        return None;
    };
    let system = obligation.system();
    let fair_event_keys = obligation.fair_event_keys();
    let patterns = liveness.patterns();
    let recipes = liveness.recipes();
    let safety_obligations = liveness.safety_obligations().to_vec();

    // Pre-validate expressions
    for entity in system.relevant_entities() {
        for trans in &entity.transitions {
            if find_unsupported_scene_expr(&trans.guard).is_some() {
                return None;
            }
            for upd in &trans.updates {
                if find_unsupported_scene_expr(&upd.value).is_some() {
                    return None;
                }
            }
        }
    }
    for sys in system.relevant_systems() {
        for event in &sys.steps {
            if find_unsupported_scene_expr(&event.guard).is_some() {
                return None;
            }
            if find_unsupported_in_actions(&event.body).is_some() {
                return None;
            }
        }
    }

    // ── Inductive step (the core of the proof) ──────────────────────
    // For each liveness assert, build a monitor and check
    // `not accepting(k+1)` given `not accepting(k)` and one transition.
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

    // Build a monitor per liveness assert.
    //
    // For QUANTIFIED patterns (all o: E |... eventually...):
    // Build one monitor PER entity slot. This gives universal semantics:
    // each slot must independently satisfy the liveness property.
    // If ANY slot's monitor can accept, the property is violated.
    //
    // For NON-QUANTIFIED patterns: one monitor per assert (as before).
    let mut accepting_vars_step1: Vec<Bool> = Vec::new();
    let true_lit = IRExpr::Lit {
        ty: IRType::Bool,
        value: crate::ir::types::LitVal::Bool { value: true },
        span: None,
    };

    for recipe in recipes {
        let (quant_var, quant_entity) = recipe.quantified_binding();
        let slot_count = recipe.slot_count();

        for target_slot in 0..slot_count {
            // Unique prefix per (assert, slot) to avoid variable name collisions
            let prefix = if quant_entity.is_some() {
                format!("mon{}_s{target_slot}", recipe.assert_index())
            } else {
                format!("mon{}", recipe.assert_index())
            };

            let pending_0 = smt::bool_named(&format!("{prefix}_pending_t0"));
            let pending_1 = smt::bool_named(&format!("{prefix}_pending_t1"));

            // Saved state: one copy per entity/slot/field (constants — captured at trigger)
            let mut saved_fields: Vec<(String, usize, String, SmtValue)> = Vec::new();
            let mut saved_active: Vec<(String, usize, SmtValue)> = Vec::new();
            for entity in system.relevant_entities() {
                let n_slots = pool.slots_for(&entity.name);
                for slot in 0..n_slots {
                    for field in &entity.fields {
                        let name =
                            format!("{prefix}_saved_{}_s{}_{}", entity.name, slot, field.name);
                        let var = match &field.ty {
                            IRType::Bool => smt::bool_var(&name),
                            IRType::Real | IRType::Float => smt::real_var(&name),
                            _ => smt::int_var(&name),
                        };
                        saved_fields.push((entity.name.clone(), slot, field.name.clone(), var));
                    }
                    let act_name = format!("{prefix}_saved_{}_s{}_active", entity.name, slot);
                    saved_active.push((entity.name.clone(), slot, smt::bool_var(&act_name)));
                }
            }

            // Justice counters: one per fair event, at steps 0 and 1
            let mut justice_0: Vec<Bool> = Vec::new();
            let mut justice_1: Vec<Bool> = Vec::new();
            for (i, _key) in fair_event_keys.iter().enumerate() {
                justice_0.push(smt::bool_named(&format!("{prefix}_justice{i}_t0")));
                justice_1.push(smt::bool_named(&format!("{prefix}_justice{i}_t1")));
            }

            // Build property context: bind quantified variable to this specific slot
            let ctx = if let (Some(var), Some(ent_name)) = (quant_var, quant_entity) {
                PropertyCtx::new().with_binding(var, ent_name, target_slot)
            } else {
                PropertyCtx::new()
            };

            let trigger_0 =
                encode_prop_expr(&pool, vctx, defs, &ctx, recipe.trigger(&true_lit), 0).ok()?;
            let response_0 =
                encode_prop_expr(&pool, vctx, defs, &ctx, recipe.response(), 0).ok()?;

            // Monitor transition: step 0 → step 1
            //
            // trigger_fires = NOT pending_0 AND P(0) AND NOT Q(0)
            let trigger_fires = smt::bool_and(&[
                &smt::bool_not(&pending_0),
                &trigger_0,
                &smt::bool_not(&response_0),
            ]);
            // discharge = pending_0 AND Q(0)
            let discharge = smt::bool_and(&[&pending_0, &response_0]);

            // pending_1 = ITE(trigger_fires, true, ITE(discharge, false, pending_0))
            let pending_1_val = smt::bool_ite(
                &trigger_fires,
                &smt::bool_const(true),
                &smt::bool_ite(&discharge, &smt::bool_const(false), &pending_0),
            );
            solver.assert(smt::bool_eq(&pending_1, &pending_1_val));

            // Saved state capture: on trigger, save current state
            for (ent, slot, field, saved_var) in &saved_fields {
                if let Some(current) = pool.field_at(ent, *slot, field, 0) {
                    let saved_val = smt::smt_ite(&trigger_fires, current, saved_var);
                    if let Ok(eq) = smt::smt_eq(&saved_val, saved_var) {
                        solver.assert(&eq);
                    }
                }
            }
            for (ent, slot, saved_act) in &saved_active {
                if let Some(SmtValue::Bool(current)) = pool.active_at(ent, *slot, 0) {
                    let saved_val = smt::bool_ite(
                        &trigger_fires,
                        current,
                        match saved_act {
                            SmtValue::Bool(b) => b,
                            _ => continue,
                        },
                    );
                    if let SmtValue::Bool(s) = saved_act {
                        solver.assert(smt::bool_eq(s, &saved_val));
                    }
                }
            }

            // Justice tracking: on trigger_fires, reset to just this step's fire.
            // Otherwise, accumulate: justice_1 = justice_0 OR fire_at_0
            for (i, key) in fair_event_keys.iter().enumerate() {
                let fired_at_0 = fire_tracking
                    .fire_vars
                    .get(key)
                    .and_then(|v| v.first())
                    .cloned()
                    .unwrap_or_else(|| smt::bool_const(false));

                let justice_val = smt::bool_ite(
                    &trigger_fires,
                    &fired_at_0,
                    &smt::bool_or(&[&justice_0[i], &fired_at_0]),
                );
                solver.assert(smt::bool_eq(&justice_1[i], &justice_val));
            }

            // Loop detection: accepting_1 = pending_1 AND state_matches AND all_justice
            let mut state_match_parts: Vec<Bool> = Vec::new();
            for (ent, slot, field, saved_var) in &saved_fields {
                if let Some(current) = pool.field_at(ent, *slot, field, 1) {
                    if let Ok(eq) = smt::smt_eq(saved_var, current) {
                        state_match_parts.push(eq);
                    }
                }
            }
            for (ent, slot, saved_act) in &saved_active {
                if let Some(SmtValue::Bool(current)) = pool.active_at(ent, *slot, 1) {
                    if let SmtValue::Bool(s) = saved_act {
                        state_match_parts.push(smt::bool_eq(s, current));
                    }
                }
            }

            let state_matches = if state_match_parts.is_empty() {
                smt::bool_const(true)
            } else {
                let refs: Vec<&Bool> = state_match_parts.iter().collect();
                smt::bool_and(&refs)
            };

            let all_justice = if justice_1.is_empty() {
                smt::bool_const(true)
            } else {
                let refs: Vec<&Bool> = justice_1.iter().collect();
                smt::bool_and(&refs)
            };

            let accepting_1 = smt::bool_and(&[&pending_1, &state_matches, &all_justice]);
            accepting_vars_step1.push(accepting_1);
        } // end for target_slot
    }

    // Inductive hypothesis: no monitor is accepting at step 0
    // (Since we don't assert accepting_0 explicitly, the solver is free to
    // choose any value. We assert NOT accepting_0 as the hypothesis.)
    // Actually, we need to assert: none of the monitors are accepting at step 0.
    // The accepting_0 is not materialized — we just don't constrain it.
    // The hypothesis is that the safety property holds at step k.
    // For simplicity, assert that no accepting condition holds at step 0.
    //
    // Note: we don't need separate accepting_0 variables. The hypothesis
    // is implicit: we're checking whether accepting can become true after
    // one transition from ANY state where it's not true.
    //
    // We assert: the negation of the safety property at step 1 (any accepting_1 is true)
    let any_accepting = if accepting_vars_step1.len() == 1 {
        accepting_vars_step1[0].clone()
    } else {
        let refs: Vec<&Bool> = accepting_vars_step1.iter().collect();
        smt::bool_or(&refs)
    };
    solver.assert(&any_accepting);

    // Check: UNSAT means no transition can make any monitor accepting → PROVED
    if solver.check() == SatResult::Unsat {
        // Liveness part proved. Now verify safety obligations (if any).
        if safety_obligations.is_empty() {
            let elapsed = elapsed_ms(&start);
            return Some(VerificationResult::Proved {
                name: verify_block.name.clone(),
                method: crate::messages::LIVENESS_REDUCTION_METHOD.to_owned(),
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
            });
        }
        let safety_verify = IRVerify {
            name: verify_block.name.clone(),
            depth: None,
            systems: verify_block.systems.clone(),
            stores: verify_block.stores.clone(),
            // Inherit the parent verify's assumption set so safety checks
            // see the same fairness/stutter context.
            assumption_set: verify_block.assumption_set.clone(),
            asserts: safety_obligations.clone(),
            span: verify_block.span,
            file: verify_block.file.clone(),
        };
        // Try induction first, then IC3 for safety
        let safety_proved = try_induction_on_verify(ir, vctx, defs, &safety_verify, config)
            .or_else(|| {
                if config.no_ic3 {
                    None
                } else {
                    try_ic3_on_verify(ir, vctx, defs, &safety_verify, config)
                }
            });
        if let Some(VerificationResult::Proved { .. }) = safety_proved {
            let elapsed = elapsed_ms(&start);
            return Some(VerificationResult::Proved {
                name: verify_block.name.clone(),
                method: crate::messages::LIVENESS_REDUCTION_METHOD.to_owned(),
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
            });
        }
        // safety couldn't be proved — fall through to IC3
    }
    // 1-induction failed — try IC3 below

    // ── IC3/PDR on the reduced safety property ──────────────────────
    // 1-induction is too weak for most liveness reductions. IC3 can
    // automatically discover the strengthening invariants needed.
    // ALL patterns must be proved by IC3. If any fails, the block is not proved.
    //
    // For QUANTIFIED patterns: IC3 with coarse justice tracking on the full
    // multi-slot system is unsound (events firing on other slots satisfy
    // justice for the wrong slot). Instead, try symmetry reduction: prove
    // the property on a 1-slot system where coarse justice IS sound (there's
    // only one slot, so any event on that slot is the target), then
    // generalize by entity symmetry.
    let has_quantified = liveness.has_quantified_patterns();
    if has_quantified {
        // Try symmetry reduction before falling back to lasso BMC
        if let Some(result) = try_symmetry_reduction(
            ir,
            vctx,
            defs,
            patterns,
            &safety_obligations,
            system.system_names(),
            system.slots_per_entity(),
            &fair_event_keys,
            system.relevant_systems(),
            config,
            &start,
            verify_block,
        ) {
            return Some(result);
        }
        return None; // symmetry failed — fall back to lasso BMC (CHECKED)
    }

    let mut all_proved = true;
    'pattern_loop: for (recipe_index, recipe) in recipes.iter().enumerate() {
        let slot_count = recipe.slot_count();

        for target_slot_idx in 0..slot_count {
            let target_slot = if recipe.is_quantified() {
                Some(target_slot_idx)
            } else {
                None // non-quantified: no per-slot restriction
            };

            let ic3_result = transition::solve_transition_obligation(liveness.obligation(
                recipe_index,
                target_slot,
                config.ic3_timeout_ms / 2,
            ));

            if let transition::TransitionResult::Proved = ic3_result {
                // This slot proved — continue to check remaining slots
            } else {
                // Any slot failing means the pattern (and block) is not proved
                all_proved = false;
                break 'pattern_loop;
            }
        }
    }

    if all_proved {
        // Liveness proved via IC3. Now verify safety obligations (if any).
        if !safety_obligations.is_empty() {
            let safety_verify = IRVerify {
                depth: None,
                name: verify_block.name.clone(),
                systems: verify_block.systems.clone(),
                stores: verify_block.stores.clone(),
                // Inherit the parent verify's assumption set.
                assumption_set: verify_block.assumption_set.clone(),
                asserts: safety_obligations,
                span: verify_block.span,
                file: verify_block.file.clone(),
            };
            let safety_proved = try_induction_on_verify(ir, vctx, defs, &safety_verify, config)
                .or_else(|| {
                    if config.no_ic3 {
                        None
                    } else {
                        try_ic3_on_verify(ir, vctx, defs, &safety_verify, config)
                    }
                });
            match safety_proved {
                Some(VerificationResult::Proved { .. }) => {
                    let elapsed = elapsed_ms(&start);
                    return Some(VerificationResult::Proved {
                        name: verify_block.name.clone(),
                        method: "liveness-to-safety (IC3/PDR)".to_owned(),
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
                    });
                }
                _ => return None, // safety couldn't be proved — whole block not proved
            }
        }

        let elapsed = elapsed_ms(&start);
        return Some(VerificationResult::Proved {
            name: verify_block.name.clone(),
            method: "liveness-to-safety (IC3/PDR)".to_owned(),
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
        });
    }

    None
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
    let start = Instant::now();

    // shared scope helper. IC3 also widens
    // slots based on quantifier depth, layered on top of the canonical scope.
    let Some(safety) = transition::TransitionSafetySpec::for_verify(ir, vctx, verify_block, defs)
    else {
        return None;
    };
    if config.progress {
        eprint!(" (trying IC3/PDR)");
    }

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
            transition::TransitionResult::Violated(_)
            | transition::TransitionResult::Unknown(_) => {
                return None; // fall back to BMC for confirmed trace
            }
        }
    }

    let elapsed = elapsed_ms(&start);
    Some(VerificationResult::Proved {
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
    })
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
#[allow(clippy::too_many_lines)]
fn check_verify_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &VerifyConfig,
) -> VerificationResult {
    let start = Instant::now();

    let Some(safety) = transition::TransitionSafetySpec::for_verify(ir, vctx, verify_block, defs)
    else {
        return VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: "verify block did not produce a transition-system obligation".to_owned(),
            span: verify_block.span,
            file: verify_block.file.clone(),
        };
    };
    let system = safety.system();
    let bound = system.bound();

    if let Some(result) = relational::try_check_verify_block_relational(
        ir,
        verify_block,
        bound,
        config.witness_semantics,
    ) {
        return materialize_relational_verify_outcome(ir, verify_block, bound, result);
    }

    // 2c. Pre-validate unsupported expression forms.
    // Catches forms like Card(field), SetComp with non-entity domain, etc.
    // that would panic during encoding. Scans both assert expressions AND
    // transition/event bodies (guards, updates, create fields).
    for (assert_expr, property) in verify_block.asserts.iter().zip(safety.step_properties()) {
        if let Some(kind) = find_unsupported_scene_expr(property) {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: format!("unsupported expression kind in verify assert: {kind}"),
                span: expr_span(assert_expr),
                file: None,
            };
        }
    }
    // Scan transition guards and update values for unsupported forms
    for entity in system.relevant_entities() {
        for trans in &entity.transitions {
            if let Some(kind) = find_unsupported_scene_expr(&trans.guard) {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} guard: {kind}",
                        entity.name, trans.name
                    ),
                    span: None,
                    file: None,
                };
            }
            for upd in &trans.updates {
                if let Some(kind) = find_unsupported_scene_expr(&upd.value) {
                    return VerificationResult::Unprovable {
                        name: verify_block.name.clone(),
                        hint: format!(
                            "unsupported expression in {}.{} update of {}: {kind}",
                            entity.name, trans.name, upd.field
                        ),
                        span: None,
                        file: None,
                    };
                }
            }
        }
    }
    // Scan event guards and action bodies
    for sys in system.relevant_systems() {
        for event in &sys.steps {
            if let Some(kind) = find_unsupported_scene_expr(&event.guard) {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event guard: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
            if let Some(kind) = find_unsupported_in_actions(&event.body) {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event body: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── 3. Create compiled bounded transition encoding ────────────
    let encoding = match transition::TransitionSmtEncoding::from_plan(
        transition::TransitionExecutionPlan::for_bmc(system.clone(), bound),
    ) {
        Ok(encoding) => encoding,
        Err(msg) => {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: format!("transition encoding error: {msg}"),
                span: None,
                file: None,
            };
        }
    };
    let pool = encoding.pool();
    let fire_tracking = encoding.fire_tracking();

    // ── 4. Build solver and assert constraints ─────────────────────
    let solver = AbideSolver::new();
    if config.bmc_timeout_ms > 0 {
        solver.set_timeout(config.bmc_timeout_ms);
    }

    // Initial state: all slots inactive at step 0
    for c in encoding.initial_constraints() {
        solver.assert(c);
    }
    for c in encoding.system_initial_constraints() {
        solver.assert(c);
    }

    // Symmetry breaking: slots activated in order to reduce search space
    for c in encoding.symmetry_constraints() {
        solver.assert(c);
    }

    // Domain constraints at every step
    for c in encoding.domain_constraints() {
        solver.assert(c);
    }

    // Transition constraints at every step 0..bound-1 with command fire
    // tracking. Native operational witnesses are extracted directly from these
    // indicators, and `saw` encoding also depends on the same named booleans.
    for c in &fire_tracking.constraints {
        solver.assert(c);
    }

    // ── 4b. Direct deadlock detection ( / revised) ──
    //
    // When stutter is opted out, the transition relation reduces to
    // `event_1 ∨ … ∨ event_N`. If at some reachable step every event
    // is disabled, that disjunction is unsatisfiable and the BMC's
    // initial+transition constraints alone become UNSAT — no valid
    // trace of length `bound` exists. Without an explicit check, the
    // verifier would silently report CHECKED (no counterexample) and
    // hide the deadlock. We probe for this by running an explicit SAT
    // check on the trace constraints before adding the property.
    if !verify_block.assumption_set.stutter {
        match solver.check() {
            SatResult::Unsat => {
                let elapsed = elapsed_ms(&start);
                let _ = elapsed; // unused but kept for symmetry with the property path
                let assert_span = if verify_block.asserts.len() == 1 {
                    expr_span(&verify_block.asserts[0])
                } else {
                    None
                };
                // Multi-step deadlock detection: find the exact step
                // where the system deadlocks and extract a trace prefix.
                if let Some((
                    deadlock_step,
                    evidence,
                    evidence_extraction_error,
                    event_diagnostics,
                )) = find_deadlock_step(
                    ir,
                    system.relevant_entities(),
                    system.relevant_systems(),
                    vctx,
                    system.slots_per_entity(),
                    verify_block,
                    bound,
                    config,
                    config.witness_semantics,
                ) {
                    return VerificationResult::Deadlock {
                        name: verify_block.name.clone(),
                        evidence,
                        evidence_extraction_error,
                        step: deadlock_step,
                        reason: format!(
                            "the system deadlocks at step {deadlock_step} — no events \
                             are enabled and stutter is opted out"
                        ),
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
                    };
                }
                // Could not localize the deadlock (solver timeouts).
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: "the full-bound trace is unsatisfiable (possible \
                           reaching-state deadlock) but the solver could not \
                           localize the exact step"
                        .to_owned(),
                    span: assert_span,
                    file: None,
                };
            }
            SatResult::Sat | SatResult::Unknown(_) => {
                // SAT: a valid trace exists, proceed with property check.
                // Unknown: be conservative and proceed with property check;
                // if the property check also returns Unknown the verifier
                // will report TIMEOUT/UNPROVABLE in the standard path.
            }
        }
    }

    // ── 5. Encode properties and search for counterexample ─────────
    // For `always P`: check that P holds at every step 0..bound.
    // We negate: assert exists some step where P does NOT hold.
    // If UNSAT → property holds at all steps (CHECKED).
    // If SAT → counterexample found.
    let property_at_all_steps = match encode_step_properties_all_steps(
        &pool,
        vctx,
        defs,
        safety.step_properties(),
        bound,
        system.store_ranges(),
        system.relevant_systems(),
    ) {
        Ok(prop) => prop,
        Err(msg) => {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: format!("encoding error: {msg}"),
                span: None,
                file: None,
            };
        }
    };

    // Negate the conjunction of all properties across all steps
    solver.assert(smt::bool_not(&property_at_all_steps));

    // ── 6. Check and return result ─────────────────────────────────
    let elapsed = elapsed_ms(&start);

    match solver.check() {
        SatResult::Unsat => VerificationResult::Checked {
            name: verify_block.name.clone(),
            depth: bound,
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
        },
        SatResult::Sat => {
            let evidence = match config.witness_semantics {
                WitnessSemantics::Operational => extract_operational_counterexample_with_fire(
                    &solver,
                    &pool,
                    vctx,
                    system.relevant_entities(),
                    system.relevant_systems(),
                    &fire_tracking,
                    bound,
                )
                .and_then(operational_evidence),
                WitnessSemantics::Relational => extract_relational_counterexample(
                    &solver,
                    &pool,
                    vctx,
                    system.relevant_entities(),
                    system.relevant_systems(),
                    bound,
                )
                .and_then(relational_evidence),
            };
            let (evidence, evidence_extraction_error) = match evidence {
                Ok(evidence) => (Some(evidence), None),
                Err(err) => (None, Some(err)),
            };
            // Use the first assert's span when there's only one (common case).
            // For multi-assert blocks, with_source fills in the block span.
            let assert_span = if verify_block.asserts.len() == 1 {
                expr_span(&verify_block.asserts[0])
            } else {
                None
            };
            VerificationResult::Counterexample {
                name: verify_block.name.clone(),
                evidence,
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
                span: assert_span,
                file: None,
            }
        }
        SatResult::Unknown(_) => {
            let hint = if config.bmc_timeout_ms > 0 {
                let timeout_display = if config.bmc_timeout_ms >= 1000 {
                    format!("{}s", config.bmc_timeout_ms / 1000)
                } else {
                    format!("{}ms", config.bmc_timeout_ms)
                };
                format!(
                    "Z3 timed out after {timeout_display} — try reducing bound, increasing --bmc-timeout, or simplifying property"
                )
            } else {
                crate::messages::BMC_UNKNOWN.to_owned()
            };
            VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint,
                span: None,
                file: None,
            }
        }
    }
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
#[allow(clippy::too_many_lines)]
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
        return VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: "verify block did not produce a transition-system obligation".to_owned(),
            span: verify_block.span,
            file: verify_block.file.clone(),
        };
    };
    let system = obligation.system();

    if system.slots_per_entity().is_empty() {
        // No entities — lasso BMC requires entity state for loop-back.
        // Fall back to linear BMC.
        return check_verify_block(ir, vctx, defs, verify_block, config);
    }
    let bound = system.bound();

    // ── 2. Create pool and solver ───────────────────────────────────
    let encoding = match transition::TransitionSmtEncoding::from_plan(obligation.lasso_plan()) {
        Ok(encoding) => encoding,
        Err(msg) => {
            return VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: format!("lasso transition encoding error: {msg}"),
                span: None,
                file: None,
            };
        }
    };
    let pool = encoding.pool();
    let fire_tracking = encoding.fire_tracking();
    let solver = AbideSolver::new();
    if config.bmc_timeout_ms > 0 {
        solver.set_timeout(config.bmc_timeout_ms);
    }

    // Initial state
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
    for c in &fire_tracking.constraints {
        solver.assert(c);
    }

    // ── 4. Lasso loop-back ──────────────────────────────────────────
    let Some(lasso) = encoding.lasso() else {
        return VerificationResult::Unprovable {
            name: verify_block.name.clone(),
            hint: "internal verifier error while encoding lasso loop".to_owned(),
            span: verify_block.span,
            file: verify_block.file.clone(),
        };
    };
    for c in &lasso.constraints {
        solver.assert(c);
    }

    // ── 5. Fairness constraints ─────────────────────────────────────
    for c in encoding.fairness_constraints() {
        solver.assert(c);
    }

    // ── 6. Check each liveness assert independently ────────────────
    // Each assert is checked separately — if ANY assert is violated,
    // the verify block fails. This matches standard semantics: each
    // assert is an independent obligation.
    for assert_expr in &verify_block.asserts {
        let expanded = expand_through_defs(assert_expr, defs);
        let violation = match encode_lasso_liveness_violation(
            &pool,
            vctx,
            defs,
            &expanded,
            &lasso.loop_indicators,
            bound,
        ) {
            Ok(v) => v,
            Err(msg) => {
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: format!("lasso encoding error: {msg}"),
                    span: expr_span(assert_expr),
                    file: None,
                };
            }
        };

        // Skip non-liveness asserts (violation is false)
        // Check: push violation, check SAT, pop
        solver.push();
        solver.assert(&violation);

        match solver.check() {
            SatResult::Sat => {
                // Found a lasso violating this assert
                let Some(model) = solver.get_model() else {
                    solver.pop();
                    return VerificationResult::Unprovable {
                        name: verify_block.name.clone(),
                        hint: "solver reported sat for liveness check but did not provide a model"
                            .to_owned(),
                        span: expr_span(assert_expr),
                        file: None,
                    };
                };
                let mut loop_start = 0;
                for (l, ind) in lasso.loop_indicators.iter().enumerate() {
                    if let Some(true) = model.eval(ind, true).and_then(|v| v.as_bool()) {
                        loop_start = l;
                        break;
                    }
                }

                let evidence = match config.witness_semantics {
                    WitnessSemantics::Operational => extract_operational_liveness_with_fire(
                        &solver,
                        &pool,
                        vctx,
                        system.relevant_entities(),
                        system.relevant_systems(),
                        &fire_tracking,
                        bound,
                        loop_start,
                    )
                    .and_then(operational_evidence),
                    WitnessSemantics::Relational => extract_relational_liveness(
                        &solver,
                        &pool,
                        vctx,
                        system.relevant_entities(),
                        system.relevant_systems(),
                        bound,
                        loop_start,
                    )
                    .and_then(relational_evidence),
                };
                let (evidence, evidence_extraction_error) = match evidence {
                    Ok(evidence) => (Some(evidence), None),
                    Err(err) => (None, Some(err)),
                };
                let fairness_analysis = extract_fairness_analysis(
                    &solver,
                    &pool,
                    vctx,
                    system.relevant_entities(),
                    system.relevant_systems(),
                    &fire_tracking,
                    loop_start,
                    bound,
                    &verify_block.assumption_set,
                );

                return VerificationResult::LivenessViolation {
                    name: verify_block.name.clone(),
                    evidence,
                    evidence_extraction_error,
                    loop_start,
                    fairness_analysis,
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
                    span: expr_span(assert_expr),
                    file: None,
                };
            }
            SatResult::Unknown(_) => {
                solver.pop();
                return VerificationResult::Unprovable {
                    name: verify_block.name.clone(),
                    hint: crate::messages::BMC_UNKNOWN.to_owned(),
                    span: expr_span(assert_expr),
                    file: None,
                };
            }
            SatResult::Unsat => {
                solver.pop();
                // This assert passes — continue to next
            }
        }
    }

    // All asserts passed
    let elapsed = elapsed_ms(&start);
    VerificationResult::Checked {
        name: verify_block.name.clone(),
        depth: bound,
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

        // Entity quantifier: `all o: Entity | body` — expand over active slots
        // and check each for liveness violations (disjunction: ANY slot violated).
        // The active guard per step is handled inside the inner encoding
        // (response pattern guards P(t) with active(slot, t)).
        IRExpr::Forall {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
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
                slot_violations.push(v);
            }
            if slot_violations.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = slot_violations.iter().collect();
            Ok(smt::bool_or(&refs))
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

// ── Property encoding for BMC ───────────────────────────────────────

/// Expand an IR expression through the `DefEnv` — replace Var refs matching
/// nullary defs with their bodies, and App chains matching parameterized defs
/// with their beta-reduced bodies. Used to resolve pred/prop references in
/// given constraints before scanning for field references.
#[allow(clippy::too_many_lines)]
pub(super) fn expand_through_defs(expr: &IRExpr, defs: &defenv::DefEnv) -> IRExpr {
    if let IRExpr::Var { name, .. } = expr {
        if let Some(expanded) = defs.expand_var(name) {
            return expand_through_defs(&expanded, defs);
        }
    }
    if let IRExpr::App { .. } = expr {
        if let Some(expanded) = defs.expand_app(expr) {
            return expand_through_defs(&expanded, defs);
        }
    }
    match expr {
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(expand_through_defs(left, defs)),
            right: Box::new(expand_through_defs(right, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::UnOp {
            op, operand, ty, ..
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(expand_through_defs(operand, defs)),
            ty: ty.clone(),
            span: None,
        },
        IRExpr::Forall {
            var, domain, body, ..
        } => IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Exists {
            var, domain, body, ..
        } => IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::One {
            var, domain, body, ..
        } => IRExpr::One {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Lone {
            var, domain, body, ..
        } => IRExpr::Lone {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Always { body, .. } => IRExpr::Always {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Eventually { body, .. } => IRExpr::Eventually {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Until { left, right, .. } => IRExpr::Until {
            left: Box::new(expand_through_defs(left, defs)),
            right: Box::new(expand_through_defs(right, defs)),
            span: None,
        },
        // / — past-time temporal operators recurse
        // through `expand_through_defs` so prop/pred references inside
        // them are visible to the BMC encoder.
        IRExpr::Historically { body, .. } => IRExpr::Historically {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Once { body, .. } => IRExpr::Once {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Previously { body, .. } => IRExpr::Previously {
            body: Box::new(expand_through_defs(body, defs)),
            span: None,
        },
        IRExpr::Since { left, right, .. } => IRExpr::Since {
            left: Box::new(expand_through_defs(left, defs)),
            right: Box::new(expand_through_defs(right, defs)),
            span: None,
        },
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
            filter,
            projection,
            ty,
            ..
        } => IRExpr::SetComp {
            var: var.clone(),
            domain: domain.clone(),
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
            IRAction::ForAll { var, ops, .. } => {
                let apply_count = ops
                    .iter()
                    .filter(|op| matches!(op, IRAction::Apply { target, .. } if target == var))
                    .count();
                if apply_count > 1 {
                    return Some(
                        "multiple Apply actions on the same entity in one ForAll block \
                         (sequential composition not yet supported — split into separate events)",
                    );
                }
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

    // Stutter first
    if assumptions
        .iter()
        .any(|a| matches!(a, TrustedAssumption::Stutter))
    {
        parts.push("stutter".to_owned());
    }

    // Weak fairness (alphabetical, deduplicated)
    let mut wf: Vec<String> = assumptions
        .iter()
        .filter_map(|a| match a {
            TrustedAssumption::WeakFairness { system, command } => {
                Some(format!("WF {system}::{command}"))
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
                Some(proof_artifact) => {
                    format!("axiom {name} by \"{}\"", proof_artifact.locator())
                }
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
                writeln!(f, "  checked: {}", proof_artifact_ref.is_checked())?;
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
                    writeln!(f, "  checked: {}", proof_artifact_ref.is_checked())?;
                }
                Ok(())
            }
            VerificationResult::Checked {
                name,
                depth,
                time_ms,
                assumptions,
                ..
            } => {
                let under = format_assumptions(assumptions);
                write!(f, "CHECKED {name} (depth: {depth}, {time_ms}ms{under})")
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
