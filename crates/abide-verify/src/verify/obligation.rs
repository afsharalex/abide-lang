use std::collections::HashSet;

use super::{
    body_contains_assert, body_contains_assume, body_contains_sorry, body_contains_todo,
    collect_def_refs_in_exprs, expand_through_defs, should_prepare_lemma_dependency,
    should_run_target, target_kind_matches, ChcSelection, SolverSelection, VerifyConfig,
    VerifyTargetKind,
};
use crate::ir::types::{IRAssumptionSet, IRExpr, IRFunction, IRProgram};

/// Stable identifier for one scheduled verification obligation.
///
/// The textual form is intentionally kind-qualified (`fn:abs`,
/// `verify:safety`) so future schedulers can distinguish declaration kinds
/// that share a source-level name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VerificationObligationId(String);

impl VerificationObligationId {
    #[must_use]
    pub fn new(kind: VerifyTargetKind, name: impl AsRef<str>) -> Self {
        Self::from_parts(kind.as_str(), name)
    }

    #[must_use]
    pub fn from_parts(kind: impl AsRef<str>, name: impl AsRef<str>) -> Self {
        Self(format!("{}:{}", kind.as_ref(), name.as_ref()))
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Fine-grained kind of proof/checking work represented by an obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationObligationKind {
    /// Function postcondition and assertion verification.
    FunctionPostcondition { function: String },
    /// Function termination/decreases verification.
    FunctionTermination { function: String },
    /// Bounded/tiered `verify` block.
    VerifyBlock { verify: String },
    /// SMT-backed `scene` satisfiability/checking.
    SceneBlock { scene: String },
    /// Standalone lemma proof.
    Lemma { lemma: String },
    /// Theorem proof.
    Theorem { theorem: String },
    /// Auto-verified `prop` declaration lowered from a function.
    Prop {
        prop: String,
        target_system: Option<String>,
    },
}

/// Expected result family produced by an obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationObligationResultKind {
    /// Produces `FnContract*` or a function-scoped `Unprovable`.
    FnContract,
    /// Produces ordinary bounded/proved/counterexample verification results.
    BehavioralCheck,
    /// Produces scene pass/fail/unknown results.
    Scene,
    /// Produces proof/admission/unprovable results.
    Proof,
    /// Produces `prop_*` proof/checking results.
    Prop,
}

/// How trusted or admitted constructs affect an obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationTrustPolicy {
    /// No admission is expected for this obligation.
    Strict,
    /// Function body `sorry`/`todo` admits this obligation.
    AdmitOnSorryOrTodo,
    /// Function body `assume` admits successful postcondition verification.
    AdmitOnAssume,
    /// Obligation may depend on trusted axioms, fairness, stutter, or by-lemmas.
    UsesTrustedAssumptions,
    /// Obligation is itself backed by an external trusted proof artifact.
    ExternalProofArtifact,
}

/// Scheduler/backend constraints for an obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationSchedulerPolicy {
    pub solver_selection: SolverSelection,
    pub chc_selection: Option<ChcSelection>,
    pub can_run_in_parallel: bool,
    pub requires_exclusive_solver: bool,
    pub participates_in_global_deadline: bool,
}

impl VerificationSchedulerPolicy {
    #[must_use]
    pub fn new(solver_selection: SolverSelection) -> Self {
        Self {
            solver_selection,
            chc_selection: None,
            can_run_in_parallel: false,
            requires_exclusive_solver: true,
            participates_in_global_deadline: true,
        }
    }

    #[must_use]
    pub fn with_chc_selection(mut self, chc_selection: ChcSelection) -> Self {
        self.chc_selection = Some(chc_selection);
        self
    }

    #[must_use]
    pub fn allow_parallel(mut self) -> Self {
        self.can_run_in_parallel = true;
        self.requires_exclusive_solver = false;
        self
    }

    #[must_use]
    pub fn outside_global_deadline(mut self) -> Self {
        self.participates_in_global_deadline = false;
        self
    }
}

/// Dependency edge from one verification obligation to another.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationObligationDependency {
    pub obligation: VerificationObligationId,
    pub reason: String,
}

impl VerificationObligationDependency {
    #[must_use]
    pub fn new(obligation: VerificationObligationId, reason: impl Into<String>) -> Self {
        Self {
            obligation,
            reason: reason.into(),
        }
    }
}

/// Why one obligation depends on another.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationDependencyKind {
    /// The target consumes a fact/proof produced by the source obligation.
    Semantic,
    /// Current verifier behavior gates later work on successful fn preflight.
    FailureGate,
}

/// Directed dependency edge between two verification obligations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationDependencyEdge {
    pub from: VerificationObligationId,
    pub to: VerificationObligationId,
    pub kind: VerificationDependencyKind,
    pub reason: String,
}

impl VerificationDependencyEdge {
    #[must_use]
    pub fn new(
        from: VerificationObligationId,
        to: VerificationObligationId,
        kind: VerificationDependencyKind,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            from,
            to,
            kind,
            reason: reason.into(),
        }
    }
}

/// Dependency analysis over a collected obligation set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationDependencyGraph {
    pub obligations: Vec<VerificationObligation>,
    pub edges: Vec<VerificationDependencyEdge>,
}

impl VerificationDependencyGraph {
    #[must_use]
    pub fn incoming_edges(
        &self,
        id: &VerificationObligationId,
    ) -> Vec<&VerificationDependencyEdge> {
        self.edges.iter().filter(|edge| &edge.to == id).collect()
    }

    #[must_use]
    pub fn outgoing_edges(
        &self,
        id: &VerificationObligationId,
    ) -> Vec<&VerificationDependencyEdge> {
        self.edges.iter().filter(|edge| &edge.from == id).collect()
    }

    #[must_use]
    pub fn independent_obligations(&self) -> Vec<&VerificationObligation> {
        self.obligations
            .iter()
            .filter(|obligation| self.incoming_edges(&obligation.id).is_empty())
            .collect()
    }

    #[must_use]
    pub fn has_edge(&self, from: &str, to: &str, kind: VerificationDependencyKind) -> bool {
        self.edges
            .iter()
            .any(|edge| edge.from.as_str() == from && edge.to.as_str() == to && edge.kind == kind)
    }
}

/// Scheduling strategy for dependency-ready obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationSchedulingMode {
    /// Emit exactly one runnable obligation per step in collected order.
    DeterministicSequential,
    /// Emit every currently runnable obligation per step, preserving collected order.
    DependencyBatches,
}

/// One scheduler step. Sequential schedules contain one obligation; batch
/// schedules may contain several independent obligations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationScheduleStep {
    pub obligations: Vec<VerificationObligation>,
}

/// A dependency-aware execution plan for verification obligations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationSchedule {
    pub mode: VerificationSchedulingMode,
    pub steps: Vec<VerificationScheduleStep>,
    pub unscheduled_obligations: Vec<VerificationObligation>,
}

/// Whether a planned lane may execute more than one obligation concurrently.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationLaneConcurrency {
    Serial,
    Parallel,
}

/// Reasons a set of otherwise-runnable obligations must remain serialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationConcurrencyBlocker {
    /// The obligation uses an in-process solver/backend path that is not
    /// isolated enough for same-step execution yet.
    ExclusiveSolver,
    /// `SolverSelection::Both` already owns two backend executions and result
    /// reconciliation for a single obligation.
    SolverComparisonBoth,
    /// CHC/IC3 backends are selected through process/global backend state.
    ChcBackendState,
    /// Current verifier runs share one overall deadline budget.
    GlobalDeadline,
    /// Lemmas mutate the definition environment by adding proved facts.
    LemmaFactMutation,
    /// Function contract failures gate later non-function obligations.
    FunctionPreflightGate,
    /// Result order must remain stable even if future execution is concurrent.
    DeterministicResultOrdering,
}

/// A concrete execution lane within a verification schedule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationParallelLane {
    pub step_index: usize,
    pub obligations: Vec<VerificationObligation>,
    pub concurrency: VerificationLaneConcurrency,
    pub blockers: Vec<VerificationConcurrencyBlocker>,
}

/// Parallel-safety analysis for a verification schedule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationParallelLanePlan {
    pub lanes: Vec<VerificationParallelLane>,
    pub deterministic_result_order: Vec<VerificationObligationId>,
}

/// Execution strategy for a lane plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationExecutionMode {
    /// Execute every lane and obligation on the caller thread.
    Sequential,
    /// Execute parallel-safe lanes with up to `max_workers` scoped workers.
    Parallel { max_workers: usize },
}

/// Output from executing a single obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationExecutionResult<T> {
    pub obligation_id: VerificationObligationId,
    pub output: T,
}

/// Outcome returned by an eventful obligation runner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationExecutionOutcome<T> {
    Completed(T),
    Skipped { reason: String },
    Admitted { reason: String },
    TimedOut { reason: String },
    Failed { reason: String },
}

impl<T> From<T> for VerificationExecutionOutcome<T> {
    fn from(output: T) -> Self {
        Self::Completed(output)
    }
}

/// Lifecycle event emitted by scheduler/executor layers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationSchedulerEvent {
    LaneStarted {
        step_index: usize,
        concurrency: VerificationLaneConcurrency,
        obligation_ids: Vec<VerificationObligationId>,
    },
    LaneCompleted {
        step_index: usize,
        concurrency: VerificationLaneConcurrency,
        obligation_ids: Vec<VerificationObligationId>,
    },
    ObligationStarted {
        step_index: usize,
        obligation_id: VerificationObligationId,
    },
    ObligationCompleted {
        step_index: usize,
        obligation_id: VerificationObligationId,
    },
    ObligationSkipped {
        step_index: usize,
        obligation_id: VerificationObligationId,
        reason: String,
    },
    ObligationAdmitted {
        step_index: usize,
        obligation_id: VerificationObligationId,
        reason: String,
    },
    ObligationTimedOut {
        step_index: usize,
        obligation_id: VerificationObligationId,
        reason: String,
    },
    ObligationFailed {
        step_index: usize,
        obligation_id: VerificationObligationId,
        reason: String,
    },
}

/// First-class scheduler input for one verification target or sub-target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationObligation {
    pub id: VerificationObligationId,
    pub kind: VerificationObligationKind,
    pub target_kind: VerifyTargetKind,
    pub target_name: String,
    pub result_kind: VerificationObligationResultKind,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
    pub dependencies: Vec<VerificationObligationDependency>,
    pub trust_policy: VerificationTrustPolicy,
    pub scheduler_policy: VerificationSchedulerPolicy,
    pub emits_result: bool,
}

impl VerificationObligation {
    #[must_use]
    pub fn new(
        id: VerificationObligationId,
        kind: VerificationObligationKind,
        target_kind: VerifyTargetKind,
        target_name: impl Into<String>,
        result_kind: VerificationObligationResultKind,
    ) -> Self {
        Self {
            id,
            kind,
            target_kind,
            target_name: target_name.into(),
            result_kind,
            span: None,
            file: None,
            dependencies: Vec::new(),
            trust_policy: VerificationTrustPolicy::Strict,
            scheduler_policy: VerificationSchedulerPolicy::new(SolverSelection::Z3),
            emits_result: true,
        }
    }

    #[must_use]
    pub fn with_source(mut self, span: Option<crate::span::Span>, file: Option<String>) -> Self {
        self.span = span;
        self.file = file;
        self
    }

    #[must_use]
    pub fn with_dependency(mut self, dependency: VerificationObligationDependency) -> Self {
        self.dependencies.push(dependency);
        self
    }

    #[must_use]
    pub fn with_trust_policy(mut self, trust_policy: VerificationTrustPolicy) -> Self {
        self.trust_policy = trust_policy;
        self
    }

    #[must_use]
    pub fn with_solver_policy(mut self, scheduler_policy: VerificationSchedulerPolicy) -> Self {
        self.scheduler_policy = scheduler_policy;
        self
    }

    #[must_use]
    pub fn without_result_emission(mut self) -> Self {
        self.emits_result = false;
        self
    }
}

/// Collect the verification work implied by an IR program and config.
///
/// This is the scheduler-facing mirror of today's `verify_all` dispatch order:
/// function preflight, lemmas, verify blocks, scenes, theorems, then props.
/// It does not execute obligations or mutate verifier state.
#[must_use]
pub fn collect_verification_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
) -> Vec<VerificationObligation> {
    let mut out = Vec::new();
    collect_function_obligations(ir, config, &mut out);
    collect_lemma_obligations(ir, config, &mut out);
    collect_verify_block_obligations(ir, config, &mut out);
    collect_scene_obligations(ir, config, &mut out);
    collect_theorem_obligations(ir, config, &mut out);
    collect_prop_obligations(ir, config, &mut out);
    out
}

/// Analyze dependency edges and independently runnable roots for obligations.
#[must_use]
pub fn analyze_verification_dependency_graph(
    obligations: &[VerificationObligation],
) -> VerificationDependencyGraph {
    let mut edges = semantic_dependency_edges(obligations);
    edges.extend(function_preflight_failure_gate_edges(obligations));
    VerificationDependencyGraph {
        obligations: obligations.to_vec(),
        edges,
    }
}

/// Build a deterministic dependency-aware schedule from a dependency graph.
#[must_use]
pub fn schedule_verification_obligations(
    graph: &VerificationDependencyGraph,
    mode: VerificationSchedulingMode,
) -> VerificationSchedule {
    let mut scheduled = HashSet::new();
    let mut steps = Vec::new();

    loop {
        let runnable = runnable_unscheduled_obligation_indices(graph, &scheduled);
        if runnable.is_empty() {
            break;
        }

        let step_indices: Vec<_> = match mode {
            VerificationSchedulingMode::DeterministicSequential => {
                runnable.into_iter().take(1).collect()
            }
            VerificationSchedulingMode::DependencyBatches => runnable,
        };
        let obligations: Vec<_> = step_indices
            .iter()
            .map(|index| graph.obligations[*index].clone())
            .collect();
        for obligation in &obligations {
            scheduled.insert(obligation.id.as_str().to_owned());
        }
        steps.push(VerificationScheduleStep { obligations });
    }

    let unscheduled_obligations = graph
        .obligations
        .iter()
        .filter(|obligation| !scheduled.contains(obligation.id.as_str()))
        .cloned()
        .collect();

    VerificationSchedule {
        mode,
        steps,
        unscheduled_obligations,
    }
}

/// Classify a schedule into safe serial/parallel lanes without executing it.
#[must_use]
pub fn classify_verification_parallel_lanes(
    schedule: &VerificationSchedule,
) -> VerificationParallelLanePlan {
    let mut lanes = Vec::new();
    let mut deterministic_result_order = Vec::new();

    for (step_index, step) in schedule.steps.iter().enumerate() {
        deterministic_result_order.extend(
            step.obligations
                .iter()
                .map(|obligation| obligation.id.clone()),
        );

        let step_blockers = concurrency_blockers_for_step(&step.obligations);
        if step_blockers.is_empty() {
            lanes.push(VerificationParallelLane {
                step_index,
                obligations: step.obligations.clone(),
                concurrency: if step.obligations.len() > 1 {
                    VerificationLaneConcurrency::Parallel
                } else {
                    VerificationLaneConcurrency::Serial
                },
                blockers: Vec::new(),
            });
            continue;
        }

        for obligation in &step.obligations {
            let mut blockers = concurrency_blockers_for_obligation(obligation);
            if step.obligations.len() > 1 {
                push_blocker(
                    &mut blockers,
                    VerificationConcurrencyBlocker::DeterministicResultOrdering,
                );
            }
            lanes.push(VerificationParallelLane {
                step_index,
                obligations: vec![obligation.clone()],
                concurrency: VerificationLaneConcurrency::Serial,
                blockers,
            });
        }
    }

    VerificationParallelLanePlan {
        lanes,
        deterministic_result_order,
    }
}

/// Execute a parallel-lane plan with a caller-provided obligation runner.
///
/// Current verifier integrations can use `Sequential` while future isolated
/// solver/process runners can opt into bounded parallel lanes. Results are
/// always returned in the plan's deterministic obligation order.
pub fn execute_verification_lane_plan<T, F>(
    plan: &VerificationParallelLanePlan,
    mode: VerificationExecutionMode,
    runner: F,
) -> Vec<VerificationExecutionResult<T>>
where
    T: Send,
    F: Fn(&VerificationObligation) -> T + Sync,
{
    let mut results = Vec::new();
    for lane in &plan.lanes {
        match mode {
            VerificationExecutionMode::Parallel { max_workers }
                if lane.concurrency == VerificationLaneConcurrency::Parallel
                    && lane.obligations.len() > 1
                    && max_workers > 1 =>
            {
                results.extend(execute_parallel_lane(lane, max_workers, &runner));
            }
            VerificationExecutionMode::Sequential | VerificationExecutionMode::Parallel { .. } => {
                results.extend(execute_serial_lane(lane, &runner));
            }
        }
    }
    results
}

/// Execute a lane plan while emitting scheduler lifecycle events.
pub fn execute_verification_lane_plan_with_events<T, R, F, E>(
    plan: &VerificationParallelLanePlan,
    mode: VerificationExecutionMode,
    mut event_sink: E,
    runner: F,
) -> Vec<VerificationExecutionResult<T>>
where
    T: Send,
    R: Into<VerificationExecutionOutcome<T>>,
    F: Fn(&VerificationObligation) -> R + Sync,
    E: FnMut(&VerificationSchedulerEvent),
{
    let mut results = Vec::new();
    for lane in &plan.lanes {
        emit_lane_event(lane, &mut event_sink, true);
        for obligation in &lane.obligations {
            event_sink(&VerificationSchedulerEvent::ObligationStarted {
                step_index: lane.step_index,
                obligation_id: obligation.id.clone(),
            });
        }

        let outcomes = match mode {
            VerificationExecutionMode::Parallel { max_workers }
                if lane.concurrency == VerificationLaneConcurrency::Parallel
                    && lane.obligations.len() > 1
                    && max_workers > 1 =>
            {
                execute_parallel_lane_outcomes(lane, max_workers, &runner)
            }
            VerificationExecutionMode::Sequential | VerificationExecutionMode::Parallel { .. } => {
                execute_serial_lane_outcomes(lane, &runner)
            }
        };

        for (obligation_id, outcome) in outcomes {
            match outcome {
                VerificationExecutionOutcome::Completed(output) => {
                    event_sink(&VerificationSchedulerEvent::ObligationCompleted {
                        step_index: lane.step_index,
                        obligation_id: obligation_id.clone(),
                    });
                    results.push(VerificationExecutionResult {
                        obligation_id,
                        output,
                    });
                }
                VerificationExecutionOutcome::Skipped { reason } => {
                    event_sink(&VerificationSchedulerEvent::ObligationSkipped {
                        step_index: lane.step_index,
                        obligation_id,
                        reason,
                    });
                }
                VerificationExecutionOutcome::Admitted { reason } => {
                    event_sink(&VerificationSchedulerEvent::ObligationAdmitted {
                        step_index: lane.step_index,
                        obligation_id,
                        reason,
                    });
                }
                VerificationExecutionOutcome::TimedOut { reason } => {
                    event_sink(&VerificationSchedulerEvent::ObligationTimedOut {
                        step_index: lane.step_index,
                        obligation_id,
                        reason,
                    });
                }
                VerificationExecutionOutcome::Failed { reason } => {
                    event_sink(&VerificationSchedulerEvent::ObligationFailed {
                        step_index: lane.step_index,
                        obligation_id,
                        reason,
                    });
                }
            }
        }
        emit_lane_event(lane, &mut event_sink, false);
    }
    results
}

fn emit_lane_event<E>(lane: &VerificationParallelLane, event_sink: &mut E, started: bool)
where
    E: FnMut(&VerificationSchedulerEvent),
{
    let obligation_ids = lane
        .obligations
        .iter()
        .map(|obligation| obligation.id.clone())
        .collect();
    if started {
        event_sink(&VerificationSchedulerEvent::LaneStarted {
            step_index: lane.step_index,
            concurrency: lane.concurrency,
            obligation_ids,
        });
    } else {
        event_sink(&VerificationSchedulerEvent::LaneCompleted {
            step_index: lane.step_index,
            concurrency: lane.concurrency,
            obligation_ids,
        });
    }
}

fn execute_serial_lane<T, F>(
    lane: &VerificationParallelLane,
    runner: &F,
) -> Vec<VerificationExecutionResult<T>>
where
    F: Fn(&VerificationObligation) -> T,
{
    lane.obligations
        .iter()
        .map(|obligation| VerificationExecutionResult {
            obligation_id: obligation.id.clone(),
            output: runner(obligation),
        })
        .collect()
}

fn execute_serial_lane_outcomes<T, R, F>(
    lane: &VerificationParallelLane,
    runner: &F,
) -> Vec<(VerificationObligationId, VerificationExecutionOutcome<T>)>
where
    R: Into<VerificationExecutionOutcome<T>>,
    F: Fn(&VerificationObligation) -> R,
{
    lane.obligations
        .iter()
        .map(|obligation| (obligation.id.clone(), runner(obligation).into()))
        .collect()
}

fn execute_parallel_lane<T, F>(
    lane: &VerificationParallelLane,
    max_workers: usize,
    runner: &F,
) -> Vec<VerificationExecutionResult<T>>
where
    T: Send,
    F: Fn(&VerificationObligation) -> T + Sync,
{
    let worker_count = max_workers.max(1).min(lane.obligations.len());
    let mut indexed_results = Vec::with_capacity(lane.obligations.len());

    for chunk_start in (0..lane.obligations.len()).step_by(worker_count) {
        let chunk_end = (chunk_start + worker_count).min(lane.obligations.len());
        std::thread::scope(|scope| {
            let handles: Vec<_> = (chunk_start..chunk_end)
                .map(|index| {
                    let obligation = &lane.obligations[index];
                    scope.spawn(move || {
                        (
                            index,
                            VerificationExecutionResult {
                                obligation_id: obligation.id.clone(),
                                output: runner(obligation),
                            },
                        )
                    })
                })
                .collect();
            for handle in handles {
                match handle.join() {
                    Ok(result) => indexed_results.push(result),
                    Err(payload) => std::panic::resume_unwind(payload),
                }
            }
        });
    }

    indexed_results.sort_by_key(|(index, _)| *index);
    indexed_results
        .into_iter()
        .map(|(_, result)| result)
        .collect()
}

fn execute_parallel_lane_outcomes<T, R, F>(
    lane: &VerificationParallelLane,
    max_workers: usize,
    runner: &F,
) -> Vec<(VerificationObligationId, VerificationExecutionOutcome<T>)>
where
    T: Send,
    R: Into<VerificationExecutionOutcome<T>>,
    F: Fn(&VerificationObligation) -> R + Sync,
{
    let worker_count = max_workers.max(1).min(lane.obligations.len());
    let mut indexed_results = Vec::with_capacity(lane.obligations.len());

    for chunk_start in (0..lane.obligations.len()).step_by(worker_count) {
        let chunk_end = (chunk_start + worker_count).min(lane.obligations.len());
        std::thread::scope(|scope| {
            let handles: Vec<_> = (chunk_start..chunk_end)
                .map(|index| {
                    let obligation = &lane.obligations[index];
                    scope.spawn(move || (index, (obligation.id.clone(), runner(obligation).into())))
                })
                .collect();
            for handle in handles {
                match handle.join() {
                    Ok(result) => indexed_results.push(result),
                    Err(payload) => std::panic::resume_unwind(payload),
                }
            }
        });
    }

    indexed_results.sort_by_key(|(index, _)| *index);
    indexed_results
        .into_iter()
        .map(|(_, result)| result)
        .collect()
}

fn concurrency_blockers_for_step(
    obligations: &[VerificationObligation],
) -> Vec<VerificationConcurrencyBlocker> {
    let mut blockers = Vec::new();
    for obligation in obligations {
        for blocker in concurrency_blockers_for_obligation(obligation) {
            push_blocker(&mut blockers, blocker);
        }
    }
    if obligations.len() > 1 && !blockers.is_empty() {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::DeterministicResultOrdering,
        );
    }
    blockers
}

fn concurrency_blockers_for_obligation(
    obligation: &VerificationObligation,
) -> Vec<VerificationConcurrencyBlocker> {
    let mut blockers = Vec::new();
    if obligation.scheduler_policy.requires_exclusive_solver
        || !obligation.scheduler_policy.can_run_in_parallel
    {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::ExclusiveSolver,
        );
    }
    if obligation.scheduler_policy.participates_in_global_deadline {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::GlobalDeadline,
        );
    }
    if obligation.scheduler_policy.solver_selection == SolverSelection::Both {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::SolverComparisonBoth,
        );
    }
    if obligation.scheduler_policy.chc_selection.is_some()
        && matches!(
            obligation.target_kind,
            VerifyTargetKind::Verify | VerifyTargetKind::Theorem | VerifyTargetKind::Prop
        )
    {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::ChcBackendState,
        );
    }
    if matches!(obligation.kind, VerificationObligationKind::Lemma { .. }) {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::LemmaFactMutation,
        );
    }
    if matches!(
        obligation.kind,
        VerificationObligationKind::FunctionPostcondition { .. }
            | VerificationObligationKind::FunctionTermination { .. }
    ) {
        push_blocker(
            &mut blockers,
            VerificationConcurrencyBlocker::FunctionPreflightGate,
        );
    }
    blockers
}

fn push_blocker(
    blockers: &mut Vec<VerificationConcurrencyBlocker>,
    blocker: VerificationConcurrencyBlocker,
) {
    if !blockers.contains(&blocker) {
        blockers.push(blocker);
    }
}

fn runnable_unscheduled_obligation_indices(
    graph: &VerificationDependencyGraph,
    scheduled: &HashSet<String>,
) -> Vec<usize> {
    graph
        .obligations
        .iter()
        .enumerate()
        .filter_map(|(index, obligation)| {
            if scheduled.contains(obligation.id.as_str()) {
                return None;
            }
            let ready = graph
                .incoming_edges(&obligation.id)
                .iter()
                .all(|edge| scheduled.contains(edge.from.as_str()));
            ready.then_some(index)
        })
        .collect()
}

fn semantic_dependency_edges(
    obligations: &[VerificationObligation],
) -> Vec<VerificationDependencyEdge> {
    let available: HashSet<&str> = obligations
        .iter()
        .map(|obligation| obligation.id.as_str())
        .collect();
    let mut edges = Vec::new();
    for obligation in obligations {
        for dependency in &obligation.dependencies {
            if available.contains(dependency.obligation.as_str()) {
                edges.push(VerificationDependencyEdge::new(
                    dependency.obligation.clone(),
                    obligation.id.clone(),
                    VerificationDependencyKind::Semantic,
                    dependency.reason.clone(),
                ));
            }
        }
    }
    edges
}

fn function_preflight_failure_gate_edges(
    obligations: &[VerificationObligation],
) -> Vec<VerificationDependencyEdge> {
    let function_obligations: Vec<_> = obligations
        .iter()
        .filter(|obligation| obligation.target_kind == VerifyTargetKind::Fn)
        .collect();
    if function_obligations.is_empty() {
        return Vec::new();
    }

    let mut edges = Vec::new();
    for function_obligation in function_obligations {
        for obligation in obligations {
            if obligation.target_kind == VerifyTargetKind::Fn {
                continue;
            }
            edges.push(VerificationDependencyEdge::new(
                function_obligation.id.clone(),
                obligation.id.clone(),
                VerificationDependencyKind::FailureGate,
                "current verify_all behavior stops later targets after hard fn preflight failure",
            ));
        }
    }
    edges
}

fn collect_function_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
    out: &mut Vec<VerificationObligation>,
) {
    if config.no_fn_verify {
        return;
    }
    let mut fn_config = config.clone();
    if selected_target_kind(ir, config) != Some(VerifyTargetKind::Fn) {
        fn_config.target = None;
    }
    for func in &ir.functions {
        if !should_collect_function(func, &fn_config) {
            continue;
        }
        if function_has_postcondition_obligation(func) {
            out.push(function_obligation(
                func,
                "postcondition",
                VerificationObligationKind::FunctionPostcondition {
                    function: func.name.clone(),
                },
            ));
        }
        if function_has_termination_obligation(func) {
            out.push(function_obligation(
                func,
                "termination",
                VerificationObligationKind::FunctionTermination {
                    function: func.name.clone(),
                },
            ));
        }
    }
}

fn should_collect_function(func: &IRFunction, config: &VerifyConfig) -> bool {
    func.prop_target.is_none()
        && should_run_target(config, VerifyTargetKind::Fn, &func.name)
        && (function_has_postcondition_obligation(func)
            || function_has_termination_obligation(func))
}

fn function_has_postcondition_obligation(func: &IRFunction) -> bool {
    func.prop_target.is_none()
        && (!func.ensures.is_empty()
            || body_contains_assert(&func.body)
            || body_contains_sorry(&func.body)
            || body_contains_todo(&func.body))
}

fn function_has_termination_obligation(func: &IRFunction) -> bool {
    func.prop_target.is_none()
        && function_has_postcondition_obligation(func)
        && func
            .decreases
            .as_ref()
            .is_some_and(|decreases| !decreases.star)
}

fn function_obligation(
    func: &IRFunction,
    suffix: &str,
    kind: VerificationObligationKind,
) -> VerificationObligation {
    VerificationObligation::new(
        VerificationObligationId::new(VerifyTargetKind::Fn, format!("{}/{suffix}", func.name)),
        kind,
        VerifyTargetKind::Fn,
        func.name.clone(),
        VerificationObligationResultKind::FnContract,
    )
    .with_source(func.span, func.file.clone())
    .with_trust_policy(function_trust_policy(func))
}

fn function_trust_policy(func: &IRFunction) -> VerificationTrustPolicy {
    if body_contains_sorry(&func.body) || body_contains_todo(&func.body) {
        VerificationTrustPolicy::AdmitOnSorryOrTodo
    } else if body_contains_assume(&func.body) {
        VerificationTrustPolicy::AdmitOnAssume
    } else {
        VerificationTrustPolicy::Strict
    }
}

fn collect_lemma_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
    out: &mut Vec<VerificationObligation>,
) {
    for lemma in &ir.lemmas {
        let selected = should_run_target(config, VerifyTargetKind::Lemma, &lemma.name);
        if !selected && !should_prepare_lemma_dependency(config) {
            continue;
        }
        let obligation = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Lemma, &lemma.name),
            VerificationObligationKind::Lemma {
                lemma: lemma.name.clone(),
            },
            VerifyTargetKind::Lemma,
            lemma.name.clone(),
            VerificationObligationResultKind::Proof,
        )
        .with_source(lemma.span, lemma.file.clone())
        .with_trust_policy(assumption_trust_policy(&lemma.assumption_set))
        .with_solver_policy(scheduler_policy(config));
        out.push(if selected {
            obligation
        } else {
            obligation.without_result_emission()
        });
    }
}

fn collect_verify_block_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
    out: &mut Vec<VerificationObligation>,
) {
    for verify in &ir.verifies {
        if !should_run_target(config, VerifyTargetKind::Verify, &verify.name) {
            continue;
        }
        out.push(
            VerificationObligation::new(
                VerificationObligationId::new(VerifyTargetKind::Verify, &verify.name),
                VerificationObligationKind::VerifyBlock {
                    verify: verify.name.clone(),
                },
                VerifyTargetKind::Verify,
                verify.name.clone(),
                VerificationObligationResultKind::BehavioralCheck,
            )
            .with_source(verify.span, verify.file.clone())
            .with_trust_policy(assumption_trust_policy(&verify.assumption_set))
            .with_solver_policy(scheduler_policy(config)),
        );
    }
}

fn collect_scene_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
    out: &mut Vec<VerificationObligation>,
) {
    for scene in &ir.scenes {
        if !should_run_target(config, VerifyTargetKind::Scene, &scene.name) {
            continue;
        }
        out.push(
            VerificationObligation::new(
                VerificationObligationId::new(VerifyTargetKind::Scene, &scene.name),
                VerificationObligationKind::SceneBlock {
                    scene: scene.name.clone(),
                },
                VerifyTargetKind::Scene,
                scene.name.clone(),
                VerificationObligationResultKind::Scene,
            )
            .with_source(scene.span, scene.file.clone())
            .with_solver_policy(scheduler_policy(config)),
        );
    }
}

fn collect_theorem_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
    out: &mut Vec<VerificationObligation>,
) {
    for theorem in &ir.theorems {
        if !should_run_target(config, VerifyTargetKind::Theorem, &theorem.name) {
            continue;
        }
        let mut obligation = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Theorem, &theorem.name),
            VerificationObligationKind::Theorem {
                theorem: theorem.name.clone(),
            },
            VerifyTargetKind::Theorem,
            theorem.name.clone(),
            VerificationObligationResultKind::Proof,
        )
        .with_source(theorem.span, theorem.file.clone())
        .with_trust_policy(if theorem.by_file.is_some() {
            VerificationTrustPolicy::ExternalProofArtifact
        } else {
            assumption_trust_policy(&theorem.assumption_set)
        })
        .with_solver_policy(scheduler_policy(config));
        for lemma in &theorem.by_lemmas {
            obligation = obligation.with_dependency(VerificationObligationDependency::new(
                VerificationObligationId::new(VerifyTargetKind::Lemma, lemma),
                "theorem references lemma via by-clause",
            ));
        }
        out.push(obligation);
    }
}

fn collect_prop_obligations(
    ir: &IRProgram,
    config: &VerifyConfig,
    out: &mut Vec<VerificationObligation>,
) {
    if config.no_prop_verify || !target_kind_matches(config, VerifyTargetKind::Prop) {
        return;
    }
    let covered = covered_prop_names(ir);
    for func in &ir.functions {
        if !should_run_target(config, VerifyTargetKind::Prop, &func.name) {
            continue;
        }
        let Some(target_system) = func.prop_target.as_ref() else {
            continue;
        };
        if config.target.is_none() && covered.contains(&func.name) {
            continue;
        }
        out.push(
            VerificationObligation::new(
                VerificationObligationId::new(VerifyTargetKind::Prop, &func.name),
                VerificationObligationKind::Prop {
                    prop: func.name.clone(),
                    target_system: Some(target_system.clone()),
                },
                VerifyTargetKind::Prop,
                func.name.clone(),
                VerificationObligationResultKind::Prop,
            )
            .with_source(func.span, func.file.clone())
            .with_solver_policy(scheduler_policy(config)),
        );
    }
}

fn covered_prop_names(ir: &IRProgram) -> HashSet<String> {
    let defs = super::defenv::DefEnv::from_ir(ir);
    let mut covered = HashSet::new();
    for theorem in &ir.theorems {
        collect_def_refs_in_exprs(&theorem.shows, &mut covered);
        collect_def_refs_in_exprs(&theorem.invariants, &mut covered);
        let expanded: Vec<IRExpr> = theorem
            .shows
            .iter()
            .chain(theorem.invariants.iter())
            .map(|expr| expand_through_defs(expr, &defs))
            .collect();
        collect_def_refs_in_exprs(&expanded, &mut covered);
    }
    for verify in &ir.verifies {
        collect_def_refs_in_exprs(&verify.asserts, &mut covered);
        let expanded: Vec<IRExpr> = verify
            .asserts
            .iter()
            .map(|expr| expand_through_defs(expr, &defs))
            .collect();
        collect_def_refs_in_exprs(&expanded, &mut covered);
    }
    covered
}

fn selected_target_kind(ir: &IRProgram, config: &VerifyConfig) -> Option<VerifyTargetKind> {
    let selector = config.target.as_ref()?;
    let matches: Vec<_> = super::available_verify_targets(ir)
        .into_iter()
        .filter(|entry| selector.matches(entry.kind, &entry.name))
        .collect();
    match matches.as_slice() {
        [entry] => Some(entry.kind),
        _ => None,
    }
}

fn assumption_trust_policy(set: &IRAssumptionSet) -> VerificationTrustPolicy {
    if set.has_fair_events()
        || !set.stutter
        || set.stutter_provenance != crate::ir::types::IRStutterProvenance::Default
    {
        VerificationTrustPolicy::UsesTrustedAssumptions
    } else {
        VerificationTrustPolicy::Strict
    }
}

fn scheduler_policy(config: &VerifyConfig) -> VerificationSchedulerPolicy {
    VerificationSchedulerPolicy::new(config.solver_selection)
        .with_chc_selection(config.chc_selection)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRAssumptionSet, IRDecreases, IRExpr, IRFunction, IRLemma, IRProgram, IRScene, IRTheorem,
        IRType, IRVerify, LitVal,
    };
    use crate::span::Span;
    use crate::verify::VerifyConfig;

    fn bool_lit(value: bool, start: usize) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: Some(Span {
                start,
                end: start + 4,
            }),
        }
    }

    fn fn_body(name: &str) -> IRExpr {
        let span = Some(Span {
            start: name.len(),
            end: name.len() + 1,
        });
        IRExpr::Lam {
            param: "n".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Var {
                name: "n".to_owned(),
                ty: IRType::Int,
                span: Some(Span { start: 20, end: 21 }),
            }),
            span,
        }
    }

    fn named_fn(name: &str, span_start: usize) -> IRFunction {
        IRFunction {
            name: name.to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Int),
            },
            body: fn_body(name),
            prop_target: None,
            requires: vec![],
            ensures: vec![bool_lit(true, span_start + 1)],
            decreases: Some(IRDecreases {
                measures: vec![IRExpr::Var {
                    name: "n".to_owned(),
                    ty: IRType::Int,
                    span: Some(Span {
                        start: span_start + 2,
                        end: span_start + 3,
                    }),
                }],
                star: false,
            }),
            span: Some(Span {
                start: span_start,
                end: span_start + 10,
            }),
            file: Some("unit.ab".to_owned()),
        }
    }

    fn named_ensures_fn(name: &str, span_start: usize) -> IRFunction {
        let mut func = named_fn(name, span_start);
        func.decreases = None;
        func
    }

    fn prop_fn(name: &str, target_system: &str, span_start: usize) -> IRFunction {
        IRFunction {
            name: name.to_owned(),
            ty: IRType::Bool,
            body: bool_lit(true, span_start),
            prop_target: Some(target_system.to_owned()),
            requires: vec![],
            ensures: vec![],
            decreases: None,
            span: Some(Span {
                start: span_start,
                end: span_start + 10,
            }),
            file: Some("unit.ab".to_owned()),
        }
    }

    fn verify_block(name: &str, asserts: Vec<IRExpr>, span_start: usize) -> IRVerify {
        IRVerify {
            name: name.to_owned(),
            depth: Some(1),
            systems: vec![],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![],
            initial_constraints: vec![],
            asserts,
            span: Some(Span {
                start: span_start,
                end: span_start + 10,
            }),
            file: Some("unit.ab".to_owned()),
        }
    }

    fn lemma_block(name: &str, span_start: usize) -> IRLemma {
        IRLemma {
            name: name.to_owned(),
            assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
            body: vec![bool_lit(true, span_start)],
            span: Some(Span {
                start: span_start,
                end: span_start + 10,
            }),
            file: Some("unit.ab".to_owned()),
        }
    }

    fn theorem_block(name: &str, shows: Vec<IRExpr>, span_start: usize) -> IRTheorem {
        IRTheorem {
            name: name.to_owned(),
            systems: vec!["Sys".to_owned()],
            assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
            invariants: vec![],
            shows,
            by_file: None,
            by_lemmas: vec![],
            span: Some(Span {
                start: span_start,
                end: span_start + 10,
            }),
            file: Some("unit.ab".to_owned()),
        }
    }

    fn scene_block(name: &str, span_start: usize) -> IRScene {
        IRScene {
            name: name.to_owned(),
            systems: vec!["Sys".to_owned()],
            stores: vec![],
            givens: vec![],
            events: vec![],
            ordering: vec![],
            assertions: vec![bool_lit(true, span_start)],
            given_constraints: vec![],
            activations: vec![],
            span: Some(Span {
                start: span_start,
                end: span_start + 10,
            }),
            file: Some("unit.ab".to_owned()),
        }
    }

    fn empty_program() -> IRProgram {
        IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        }
    }

    #[test]
    fn obligation_id_is_stable_and_kind_qualified() {
        let id = VerificationObligationId::new(VerifyTargetKind::Verify, "safety");

        assert_eq!(id.as_str(), "verify:safety");
        assert_eq!(id, VerificationObligationId::from_parts("verify", "safety"));
    }

    #[test]
    fn obligation_carries_scheduler_metadata_without_result_execution() {
        let span = Span { start: 7, end: 13 };
        let dependency = VerificationObligationDependency::new(
            VerificationObligationId::new(VerifyTargetKind::Lemma, "ordered"),
            "theorem imports lemma fact",
        );
        let obligation = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Theorem, "preserves_total"),
            VerificationObligationKind::Theorem {
                theorem: "preserves_total".to_owned(),
            },
            VerifyTargetKind::Theorem,
            "preserves_total",
            VerificationObligationResultKind::Proof,
        )
        .with_source(Some(span), Some("commerce.ab".to_owned()))
        .with_dependency(dependency.clone())
        .with_trust_policy(VerificationTrustPolicy::UsesTrustedAssumptions)
        .with_solver_policy(VerificationSchedulerPolicy::new(SolverSelection::Z3));

        assert_eq!(obligation.span, Some(span));
        assert_eq!(obligation.file.as_deref(), Some("commerce.ab"));
        assert_eq!(obligation.dependencies, vec![dependency]);
        assert_eq!(
            obligation.trust_policy,
            VerificationTrustPolicy::UsesTrustedAssumptions
        );
        assert_eq!(
            obligation.scheduler_policy.solver_selection,
            SolverSelection::Z3
        );
    }

    #[test]
    fn collector_emits_current_dispatch_order_from_ir_program() {
        let mut ir = empty_program();
        ir.functions.push(named_fn("bounded", 10));
        ir.functions.push(prop_fn("visible", "Sys", 20));
        ir.lemmas.push(lemma_block("helper", 30));
        ir.verifies
            .push(verify_block("safety", vec![bool_lit(true, 40)], 40));
        ir.scenes.push(scene_block("witness", 50));
        ir.theorems
            .push(theorem_block("stable", vec![bool_lit(true, 60)], 60));

        let obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let ids: Vec<_> = obligations.iter().map(|id| id.id.as_str()).collect();

        assert_eq!(
            ids,
            vec![
                "fn:bounded/postcondition",
                "fn:bounded/termination",
                "lemma:helper",
                "verify:safety",
                "scene:witness",
                "theorem:stable",
                "prop:visible",
            ]
        );
    }

    #[test]
    fn collector_filters_selected_fn_without_collecting_other_blocks() {
        let mut ir = empty_program();
        ir.functions.push(named_fn("selected", 10));
        ir.functions.push(named_fn("other", 20));
        ir.verifies
            .push(verify_block("safety", vec![bool_lit(true, 40)], 40));
        let mut config = VerifyConfig::default();
        config.target = Some("fn:selected".parse().expect("target"));

        let obligations = collect_verification_obligations(&ir, &config);
        let ids: Vec<_> = obligations.iter().map(|id| id.id.as_str()).collect();

        assert_eq!(
            ids,
            vec!["fn:selected/postcondition", "fn:selected/termination"]
        );
    }

    #[test]
    fn collector_skips_covered_props_until_explicitly_targeted() {
        let mut ir = empty_program();
        ir.functions.push(prop_fn("visible", "Sys", 10));
        ir.verifies.push(verify_block(
            "uses_prop",
            vec![IRExpr::Var {
                name: "visible".to_owned(),
                ty: IRType::Bool,
                span: Some(Span { start: 40, end: 47 }),
            }],
            40,
        ));

        let default_obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let default_ids: Vec<_> = default_obligations
            .iter()
            .map(|id| id.id.as_str())
            .collect();
        assert_eq!(default_ids, vec!["verify:uses_prop"]);

        let mut targeted = VerifyConfig::default();
        targeted.target = Some("prop:visible".parse().expect("target"));
        let targeted_obligations = collect_verification_obligations(&ir, &targeted);
        let targeted_ids: Vec<_> = targeted_obligations
            .iter()
            .map(|id| id.id.as_str())
            .collect();
        assert_eq!(targeted_ids, vec!["prop:visible"]);
    }

    #[test]
    fn dependency_graph_classifies_semantic_edges_and_failure_gates() {
        let mut ir = empty_program();
        ir.functions.push(named_fn("bounded", 10));
        ir.lemmas.push(lemma_block("helper", 30));
        ir.verifies
            .push(verify_block("safety", vec![bool_lit(true, 40)], 40));
        let mut theorem = theorem_block("stable", vec![bool_lit(true, 60)], 60);
        theorem.by_lemmas.push("helper".to_owned());
        ir.theorems.push(theorem);

        let obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let graph = analyze_verification_dependency_graph(&obligations);
        let independent_ids: Vec<_> = graph
            .independent_obligations()
            .iter()
            .map(|obligation| obligation.id.as_str())
            .collect();

        assert_eq!(
            independent_ids,
            vec!["fn:bounded/postcondition", "fn:bounded/termination"]
        );
        assert!(graph.has_edge(
            "lemma:helper",
            "theorem:stable",
            VerificationDependencyKind::Semantic
        ));
        assert!(graph.has_edge(
            "fn:bounded/postcondition",
            "verify:safety",
            VerificationDependencyKind::FailureGate
        ));
        assert!(graph.has_edge(
            "fn:bounded/termination",
            "theorem:stable",
            VerificationDependencyKind::FailureGate
        ));
        assert!(!graph.has_edge(
            "verify:safety",
            "theorem:stable",
            VerificationDependencyKind::Semantic
        ));
    }

    #[test]
    fn scheduler_produces_deterministic_sequential_topological_steps() {
        let mut ir = empty_program();
        ir.functions.push(named_fn("bounded", 10));
        ir.lemmas.push(lemma_block("helper", 30));
        ir.verifies
            .push(verify_block("safety", vec![bool_lit(true, 40)], 40));
        let mut theorem = theorem_block("stable", vec![bool_lit(true, 60)], 60);
        theorem.by_lemmas.push("helper".to_owned());
        ir.theorems.push(theorem);

        let obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let graph = analyze_verification_dependency_graph(&obligations);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DeterministicSequential,
        );
        let step_ids: Vec<Vec<_>> = schedule
            .steps
            .iter()
            .map(|step| {
                step.obligations
                    .iter()
                    .map(|obligation| obligation.id.as_str())
                    .collect()
            })
            .collect();

        assert_eq!(
            step_ids,
            vec![
                vec!["fn:bounded/postcondition"],
                vec!["fn:bounded/termination"],
                vec!["lemma:helper"],
                vec!["verify:safety"],
                vec!["theorem:stable"],
            ]
        );
        assert!(schedule.unscheduled_obligations.is_empty());
    }

    #[test]
    fn scheduler_batches_all_currently_runnable_obligations_for_parallel_extension() {
        let mut ir = empty_program();
        ir.functions.push(named_fn("bounded", 10));
        ir.lemmas.push(lemma_block("helper", 30));
        ir.verifies
            .push(verify_block("safety", vec![bool_lit(true, 40)], 40));
        let mut theorem = theorem_block("stable", vec![bool_lit(true, 60)], 60);
        theorem.by_lemmas.push("helper".to_owned());
        ir.theorems.push(theorem);

        let obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let graph = analyze_verification_dependency_graph(&obligations);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let step_ids: Vec<Vec<_>> = schedule
            .steps
            .iter()
            .map(|step| {
                step.obligations
                    .iter()
                    .map(|obligation| obligation.id.as_str())
                    .collect()
            })
            .collect();

        assert_eq!(
            step_ids,
            vec![
                vec!["fn:bounded/postcondition", "fn:bounded/termination"],
                vec!["lemma:helper", "verify:safety"],
                vec!["theorem:stable"],
            ]
        );
        assert!(schedule.unscheduled_obligations.is_empty());
    }

    #[test]
    fn parallel_lane_classifier_keeps_current_obligations_serial_with_reasons() {
        let mut ir = empty_program();
        ir.functions.push(named_fn("bounded", 10));
        ir.functions.push(named_ensures_fn("other", 20));
        ir.verifies
            .push(verify_block("safety", vec![bool_lit(true, 40)], 40));

        let obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let graph = analyze_verification_dependency_graph(&obligations);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let plan = classify_verification_parallel_lanes(&schedule);
        let lane_ids: Vec<Vec<_>> = plan
            .lanes
            .iter()
            .map(|lane| {
                lane.obligations
                    .iter()
                    .map(|obligation| obligation.id.as_str())
                    .collect()
            })
            .collect();

        assert_eq!(
            lane_ids,
            vec![
                vec!["fn:bounded/postcondition"],
                vec!["fn:bounded/termination"],
                vec!["fn:other/postcondition"],
                vec!["verify:safety"],
            ]
        );
        assert!(plan
            .lanes
            .iter()
            .all(|lane| lane.concurrency == VerificationLaneConcurrency::Serial));
        assert!(plan.lanes.iter().any(|lane| lane
            .blockers
            .contains(&VerificationConcurrencyBlocker::ExclusiveSolver)));
    }

    #[test]
    fn parallel_lane_classifier_groups_explicitly_parallel_safe_obligations() {
        let safe_a = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Scene, "a"),
            VerificationObligationKind::SceneBlock {
                scene: "a".to_owned(),
            },
            VerifyTargetKind::Scene,
            "a",
            VerificationObligationResultKind::Scene,
        )
        .with_solver_policy(
            VerificationSchedulerPolicy::new(SolverSelection::Z3)
                .allow_parallel()
                .outside_global_deadline(),
        );
        let safe_b = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Scene, "b"),
            VerificationObligationKind::SceneBlock {
                scene: "b".to_owned(),
            },
            VerifyTargetKind::Scene,
            "b",
            VerificationObligationResultKind::Scene,
        )
        .with_solver_policy(
            VerificationSchedulerPolicy::new(SolverSelection::Z3)
                .allow_parallel()
                .outside_global_deadline(),
        );
        let graph = analyze_verification_dependency_graph(&[safe_a, safe_b]);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let plan = classify_verification_parallel_lanes(&schedule);

        assert_eq!(plan.lanes.len(), 1);
        assert_eq!(
            plan.lanes[0].concurrency,
            VerificationLaneConcurrency::Parallel
        );
        assert!(plan.lanes[0].blockers.is_empty());
        assert_eq!(
            plan.deterministic_result_order
                .iter()
                .map(|id| id.as_str())
                .collect::<Vec<_>>(),
            vec!["scene:a", "scene:b"]
        );
    }

    #[test]
    fn parallel_lane_executor_runs_parallel_safe_lanes_concurrently() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::{Arc, Condvar, Mutex};
        use std::time::Duration;

        let safe_a = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Scene, "slow"),
            VerificationObligationKind::SceneBlock {
                scene: "slow".to_owned(),
            },
            VerifyTargetKind::Scene,
            "slow",
            VerificationObligationResultKind::Scene,
        )
        .with_solver_policy(
            VerificationSchedulerPolicy::new(SolverSelection::Z3)
                .allow_parallel()
                .outside_global_deadline(),
        );
        let safe_b = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Scene, "fast"),
            VerificationObligationKind::SceneBlock {
                scene: "fast".to_owned(),
            },
            VerifyTargetKind::Scene,
            "fast",
            VerificationObligationResultKind::Scene,
        )
        .with_solver_policy(
            VerificationSchedulerPolicy::new(SolverSelection::Z3)
                .allow_parallel()
                .outside_global_deadline(),
        );
        let graph = analyze_verification_dependency_graph(&[safe_a, safe_b]);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let plan = classify_verification_parallel_lanes(&schedule);
        let active = Arc::new(AtomicUsize::new(0));
        let max_active = Arc::new(AtomicUsize::new(0));
        let entered = Arc::new((Mutex::new(0_usize), Condvar::new()));

        let results = execute_verification_lane_plan(
            &plan,
            VerificationExecutionMode::Parallel { max_workers: 2 },
            {
                let active = Arc::clone(&active);
                let max_active = Arc::clone(&max_active);
                let entered = Arc::clone(&entered);
                move |obligation| {
                    let now = active.fetch_add(1, Ordering::SeqCst) + 1;
                    max_active.fetch_max(now, Ordering::SeqCst);
                    let (lock, cvar) = &*entered;
                    let mut entered_count = lock.lock().expect("entered count lock");
                    *entered_count += 1;
                    cvar.notify_all();
                    let _entered_wait = cvar
                        .wait_timeout_while(
                            entered_count,
                            Duration::from_millis(500),
                            |count| *count < 2,
                        )
                        .expect("entered count wait");
                    active.fetch_sub(1, Ordering::SeqCst);
                    obligation.id.as_str().to_owned()
                }
            },
        );

        assert_eq!(
            results
                .iter()
                .map(|result| result.output.as_str())
                .collect::<Vec<_>>(),
            vec!["scene:slow", "scene:fast"]
        );
        assert!(max_active.load(Ordering::SeqCst) > 1);
    }

    #[test]
    fn parallel_lane_executor_keeps_serial_lanes_non_overlapping() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;

        let mut ir = empty_program();
        ir.functions.push(named_fn("bounded", 10));
        ir.functions.push(named_ensures_fn("other", 20));
        let obligations = collect_verification_obligations(&ir, &VerifyConfig::default());
        let graph = analyze_verification_dependency_graph(&obligations);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let plan = classify_verification_parallel_lanes(&schedule);
        let active = Arc::new(AtomicUsize::new(0));
        let max_active = Arc::new(AtomicUsize::new(0));

        let _results = execute_verification_lane_plan(
            &plan,
            VerificationExecutionMode::Parallel { max_workers: 4 },
            {
                let active = Arc::clone(&active);
                let max_active = Arc::clone(&max_active);
                move |obligation| {
                    let now = active.fetch_add(1, Ordering::SeqCst) + 1;
                    max_active.fetch_max(now, Ordering::SeqCst);
                    active.fetch_sub(1, Ordering::SeqCst);
                    obligation.id.as_str().to_owned()
                }
            },
        );

        assert_eq!(max_active.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn eventful_lane_executor_emits_lifecycle_events_for_completed_obligations() {
        let safe = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Scene, "evented"),
            VerificationObligationKind::SceneBlock {
                scene: "evented".to_owned(),
            },
            VerifyTargetKind::Scene,
            "evented",
            VerificationObligationResultKind::Scene,
        )
        .with_solver_policy(
            VerificationSchedulerPolicy::new(SolverSelection::Z3)
                .allow_parallel()
                .outside_global_deadline(),
        );
        let graph = analyze_verification_dependency_graph(&[safe]);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let plan = classify_verification_parallel_lanes(&schedule);
        let mut events = Vec::new();

        let results = execute_verification_lane_plan_with_events(
            &plan,
            VerificationExecutionMode::Parallel { max_workers: 2 },
            |event| events.push(event.clone()),
            |obligation| obligation.id.as_str().to_owned(),
        );

        assert_eq!(results.len(), 1);
        assert!(matches!(
            &events[0],
            VerificationSchedulerEvent::LaneStarted { step_index: 0, .. }
        ));
        assert!(matches!(
            &events[1],
            VerificationSchedulerEvent::ObligationStarted { obligation_id, .. }
                if obligation_id.as_str() == "scene:evented"
        ));
        assert!(matches!(
            &events[2],
            VerificationSchedulerEvent::ObligationCompleted { obligation_id, .. }
                if obligation_id.as_str() == "scene:evented"
        ));
        assert!(matches!(
            &events[3],
            VerificationSchedulerEvent::LaneCompleted { step_index: 0, .. }
        ));
    }

    #[test]
    fn eventful_lane_executor_exposes_non_completed_outcomes() {
        let skipped = VerificationObligation::new(
            VerificationObligationId::new(VerifyTargetKind::Scene, "skipped"),
            VerificationObligationKind::SceneBlock {
                scene: "skipped".to_owned(),
            },
            VerifyTargetKind::Scene,
            "skipped",
            VerificationObligationResultKind::Scene,
        );
        let graph = analyze_verification_dependency_graph(&[skipped]);
        let schedule = schedule_verification_obligations(
            &graph,
            VerificationSchedulingMode::DependencyBatches,
        );
        let plan = classify_verification_parallel_lanes(&schedule);
        let mut events = Vec::new();

        let results: Vec<VerificationExecutionResult<String>> =
            execute_verification_lane_plan_with_events(
                &plan,
                VerificationExecutionMode::Sequential,
                |event| events.push(event.clone()),
                |_obligation| VerificationExecutionOutcome::Skipped {
                    reason: "disabled by selected target".to_owned(),
                },
            );

        assert!(results.is_empty());
        assert!(events.iter().any(|event| matches!(
            event,
            VerificationSchedulerEvent::ObligationSkipped { obligation_id, reason, .. }
                if obligation_id.as_str() == "scene:skipped"
                    && reason == "disabled by selected target"
        )));
    }
}
