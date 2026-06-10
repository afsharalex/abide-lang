//! QA artifact store — verifier and simulator results addressable by
//! id, name, or kind for later `show` / `draw` / `diff` queries.

use std::collections::{BTreeMap, BTreeSet};

use abide_verify::verify::{ExplicitStateSpace, VerificationResult};
use abide_witness::{
    op, rel, Countermodel, EntitySlotRef, EvidenceEnvelope, EvidencePayload, ProofArtifactRef,
    WitnessEnvelope, WitnessValue,
};
use serde::Serialize;

/// Why a simulation stopped.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum SimulationTermination {
    /// Reached the requested step count.
    StepLimit,
    /// Hit a deadlock state (no enabled commands).
    Deadlock { reasons: Vec<String> },
}

/// Result of one `simulate` invocation. The recorded `behavior` is a
/// concrete operational trace exactly as produced by the simulator.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SimulationArtifact {
    pub systems: Vec<String>,
    pub seed: u64,
    pub steps_requested: usize,
    pub steps_executed: usize,
    pub termination: SimulationTermination,
    pub behavior: op::Behavior,
}

/// Output of `explore` — a bounded explicit state space.
pub type StateSpaceArtifact = ExplicitStateSpace;

/// Payload of a stored [`Artifact`]: verification evidence, simulation
/// trace, or explored state space.
#[derive(Debug, Clone)]
pub enum ArtifactPayload {
    /// Verifier evidence envelope (witness / countermodel / proof ref).
    Evidence(EvidenceEnvelope),
    /// One simulation trace.
    Simulation(SimulationArtifact),
    /// One bounded state-space exploration.
    StateSpace(StateSpaceArtifact),
}

/// A stored artifact with display metadata.
///
/// `result_kind` and `name` together form the human-facing identity;
/// `id` is the numeric selector. `evidence_extraction_error` records
/// any non-fatal degradation during evidence import.
#[derive(Debug, Clone)]
pub struct Artifact {
    pub id: usize,
    pub name: String,
    pub result_kind: &'static str,
    pub payload: ArtifactPayload,
    pub evidence_extraction_error: Option<String>,
}

impl Artifact {
    pub fn summary_line(&self) -> String {
        format!(
            "#{id} {kind} {name} [{evidence_kind}] refs: {name_ref}, {kind_ref}",
            id = self.id,
            kind = self.result_kind,
            name = self.name,
            evidence_kind = payload_kind_label(&self.payload),
            name_ref = self.name_selector(),
            kind_ref = self.kind_name_selector(),
        )
    }

    pub fn render_show(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("Artifact #{}\n", self.id));
        out.push_str(&format!("  source: {} {}\n", self.result_kind, self.name));
        out.push_str(&format!(
            "  payload: {}\n",
            payload_kind_label(&self.payload)
        ));
        out.push_str(&format!("  selectors: {}\n", self.selector_summary()));
        if let Some(err) = &self.evidence_extraction_error {
            out.push_str(&format!("  degraded extraction: {err}\n"));
        }
        match &self.payload {
            ArtifactPayload::Evidence(evidence) => match evidence.payload() {
                EvidencePayload::Witness(witness) => render_witness_summary(&mut out, witness),
                EvidencePayload::Countermodel(countermodel) => {
                    render_countermodel_summary(&mut out, countermodel)
                }
                EvidencePayload::ProofArtifactRef(proof_artifact) => {
                    render_proof_artifact_summary(&mut out, proof_artifact)
                }
                _ => out.push_str("  evidence summary unavailable for this payload kind\n"),
            },
            ArtifactPayload::Simulation(simulation) => {
                out.push_str("  simulation run\n");
                out.push_str(&format!("  systems: {}\n", simulation.systems.join(", ")));
                out.push_str(&format!("  seed: {}\n", simulation.seed));
                out.push_str(&format!(
                    "  steps: {}/{}\n",
                    simulation.steps_executed, simulation.steps_requested
                ));
                match &simulation.termination {
                    SimulationTermination::StepLimit => {
                        out.push_str("  termination: step limit reached\n");
                    }
                    SimulationTermination::Deadlock { reasons } => {
                        out.push_str("  termination: deadlock\n");
                        for reason in reasons {
                            out.push_str(&format!("    - {reason}\n"));
                        }
                    }
                }
                out.push_str(&format!(
                    "  states: {}  transitions: {}\n",
                    simulation.behavior.states().len(),
                    simulation.behavior.transitions().len()
                ));
            }
            ArtifactPayload::StateSpace(state_space) => {
                out.push_str("  bounded state-space exploration\n");
                out.push_str(&format!("  systems: {}\n", state_space.systems.join(", ")));
                out.push_str(&format!("  stutter: {}\n", state_space.stutter));
                match state_space.depth_bound {
                    Some(depth) => out.push_str(&format!("  depth: {depth}\n")),
                    None => out.push_str("  depth: exhaustive\n"),
                }
                if state_space.store_bounds.is_empty() {
                    out.push_str("  store bounds: (none)\n");
                } else {
                    out.push_str("  store bounds:\n");
                    for store in &state_space.store_bounds {
                        out.push_str(&format!(
                            "    - {}: Store<{}>[{}]\n",
                            store.name, store.entity_type, store.slots
                        ));
                    }
                }
                out.push_str(&format!(
                    "  states: {}  transitions: {}  initial: {}\n",
                    state_space.states.len(),
                    state_space.transitions.len(),
                    state_space.initial_state
                ));
            }
        }
        out
    }

    pub fn render_draw(&self) -> Result<String, String> {
        match &self.payload {
            ArtifactPayload::Evidence(evidence) => match evidence.payload() {
                EvidencePayload::Witness(witness) => render_witness_timeline(witness),
                EvidencePayload::Countermodel(_) => {
                    Err("countermodel artifacts do not have a timeline view".to_owned())
                }
                EvidencePayload::ProofArtifactRef(_) => {
                    Err("proof artifact refs do not have a timeline view".to_owned())
                }
                _ => Err("timeline view is not available for this evidence kind".to_owned()),
            },
            ArtifactPayload::Simulation(simulation) => {
                Ok(render_behavior_timeline(&simulation.behavior, None))
            }
            ArtifactPayload::StateSpace(state_space) => Ok(render_state_space_graph(state_space)),
        }
    }

    pub fn render_state(&self, index: usize) -> Result<String, String> {
        match &self.payload {
            ArtifactPayload::Evidence(evidence) => match evidence.payload() {
                EvidencePayload::Witness(witness) => render_witness_state(witness, index),
                EvidencePayload::Countermodel(_) => {
                    Err("countermodel artifacts do not contain indexed states".to_owned())
                }
                EvidencePayload::ProofArtifactRef(_) => {
                    Err("proof artifact refs do not contain indexed states".to_owned())
                }
                _ => Err("state view is not available for this evidence kind".to_owned()),
            },
            ArtifactPayload::Simulation(simulation) => {
                render_behavior_state(&simulation.behavior, index)
            }
            ArtifactPayload::StateSpace(state_space) => {
                render_state_space_state(state_space, index)
            }
        }
    }

    pub fn render_diff(&self, from: usize, to: usize) -> Result<String, String> {
        match &self.payload {
            ArtifactPayload::Evidence(evidence) => match evidence.payload() {
                EvidencePayload::Witness(witness) => render_witness_diff(witness, from, to),
                EvidencePayload::Countermodel(_) => {
                    Err("countermodel artifacts do not contain indexed states".to_owned())
                }
                EvidencePayload::ProofArtifactRef(_) => {
                    Err("proof artifact refs do not contain indexed states".to_owned())
                }
                _ => Err("diff view is not available for this evidence kind".to_owned()),
            },
            ArtifactPayload::Simulation(simulation) => {
                render_behavior_diff(&simulation.behavior, from, to)
            }
            ArtifactPayload::StateSpace(state_space) => {
                render_state_space_diff(state_space, from, to)
            }
        }
    }

    pub fn export_json(&self) -> Result<String, String> {
        match &self.payload {
            ArtifactPayload::Evidence(evidence) => serde_json::to_string_pretty(evidence)
                .map_err(|err| format!("failed to serialize evidence: {err}")),
            ArtifactPayload::Simulation(simulation) => serde_json::to_string_pretty(simulation)
                .map_err(|err| format!("failed to serialize simulation: {err}")),
            ArtifactPayload::StateSpace(state_space) => serde_json::to_string_pretty(state_space)
                .map_err(|err| format!("failed to serialize state space: {err}")),
        }
    }

    pub fn name_selector(&self) -> &str {
        &self.name
    }

    pub fn kind_name_selector(&self) -> String {
        format!("{}:{}", self.result_kind, self.name)
    }

    fn selector_summary(&self) -> String {
        format!(
            "#{}, {}, {}",
            self.id,
            self.name_selector(),
            self.kind_name_selector()
        )
    }
}

/// In-memory store of [`Artifact`]s for the current QA session.
///
/// Identity is per-session: `next_id` is a monotonic counter that
/// resets only on [`Self::invalidate`]. Artifacts can be addressed by
/// id (`#3`), name (`my_verify`), or kind (`verify`).
#[derive(Debug, Default)]
pub struct ArtifactStore {
    next_id: usize,
    artifacts: Vec<Artifact>,
}

impl ArtifactStore {
    pub fn invalidate(&mut self) -> usize {
        let cleared = self.artifacts.len();
        self.artifacts.clear();
        cleared
    }

    pub fn record_verify_results(&mut self, results: &[VerificationResult]) -> usize {
        let mut stored = 0;
        for result in results {
            let Some((name, result_kind, payload, extraction_error)) =
                artifact_parts_from_result_with_name(result, None)
            else {
                continue;
            };
            self.next_id += 1;
            self.artifacts.push(Artifact {
                id: self.next_id,
                name,
                result_kind,
                payload,
                evidence_extraction_error: extraction_error,
            });
            stored += 1;
        }
        stored
    }

    pub fn record_named_verification_result(
        &mut self,
        name: String,
        result: &VerificationResult,
    ) -> usize {
        self.record_named_verification_result_id(name, result)
            .map_or(0, |_| 1)
    }

    pub fn record_named_verification_result_id(
        &mut self,
        name: String,
        result: &VerificationResult,
    ) -> Option<usize> {
        let (name, result_kind, payload, extraction_error) =
            artifact_parts_from_result_with_name(result, Some(name))?;
        self.next_id += 1;
        let id = self.next_id;
        self.artifacts.push(Artifact {
            id,
            name,
            result_kind,
            payload,
            evidence_extraction_error: extraction_error,
        });
        Some(id)
    }

    pub fn record_simulation_result(
        &mut self,
        name: String,
        simulation: SimulationArtifact,
    ) -> usize {
        self.next_id += 1;
        self.artifacts.push(Artifact {
            id: self.next_id,
            name,
            result_kind: "simulation",
            payload: ArtifactPayload::Simulation(simulation),
            evidence_extraction_error: None,
        });
        1
    }

    pub fn record_state_space_result(
        &mut self,
        name: String,
        state_space: StateSpaceArtifact,
    ) -> usize {
        self.next_id += 1;
        self.artifacts.push(Artifact {
            id: self.next_id,
            name,
            result_kind: "state-space",
            payload: ArtifactPayload::StateSpace(state_space),
            evidence_extraction_error: None,
        });
        1
    }

    pub fn is_empty(&self) -> bool {
        self.artifacts.is_empty()
    }

    pub fn artifacts(&self) -> &[Artifact] {
        &self.artifacts
    }

    pub fn artifact(&self, id: usize) -> Option<&Artifact> {
        self.artifacts.iter().find(|artifact| artifact.id == id)
    }

    pub fn resolve(&self, selector: &str) -> Option<&Artifact> {
        if let Ok(id) = selector.parse::<usize>() {
            return self.artifact(id);
        }

        let (kind_filter, name) = selector
            .split_once(':')
            .map_or((None, selector), |(kind, name)| (Some(kind), name));

        self.artifacts.iter().rev().find(|artifact| {
            artifact.name == name && kind_filter.is_none_or(|kind| artifact.result_kind == kind)
        })
    }
}

fn artifact_parts_from_result_with_name(
    result: &VerificationResult,
    name_override: Option<String>,
) -> Option<(String, &'static str, ArtifactPayload, Option<String>)> {
    let name_or = |default: &String| name_override.clone().unwrap_or_else(|| default.clone());
    match result {
        VerificationResult::Admitted { name, evidence, .. } => Some((
            name_or(name),
            "admitted",
            ArtifactPayload::Evidence(evidence.clone()?),
            None,
        )),
        VerificationResult::Counterexample {
            name,
            evidence,
            evidence_extraction_error,
            ..
        } => Some((
            name_or(name),
            "counterexample",
            ArtifactPayload::Evidence(evidence.clone()?),
            evidence_extraction_error.clone(),
        )),
        VerificationResult::LivenessViolation {
            name,
            evidence,
            evidence_extraction_error,
            ..
        } => Some((
            name_or(name),
            "liveness-violation",
            ArtifactPayload::Evidence(evidence.clone()?),
            evidence_extraction_error.clone(),
        )),
        VerificationResult::Deadlock {
            name,
            evidence,
            evidence_extraction_error,
            ..
        } => Some((
            name_or(name),
            "deadlock",
            ArtifactPayload::Evidence(evidence.clone()?),
            evidence_extraction_error.clone(),
        )),
        _ => None,
    }
}

fn payload_kind_label(payload: &ArtifactPayload) -> &'static str {
    match payload {
        ArtifactPayload::Evidence(evidence) => match evidence.payload() {
            EvidencePayload::Witness(witness) => match witness.payload() {
                abide_witness::WitnessPayload::Operational(_) => "operational-witness",
                abide_witness::WitnessPayload::Relational(_) => "relational-witness",
                _ => "witness",
            },
            EvidencePayload::Countermodel(_) => "countermodel",
            EvidencePayload::ProofArtifactRef(_) => "proof-artifact-ref",
            _ => "evidence",
        },
        ArtifactPayload::Simulation(_) => "simulation",
        ArtifactPayload::StateSpace(_) => "state-space",
    }
}

fn render_state_space_graph(state_space: &StateSpaceArtifact) -> String {
    let mut outgoing: BTreeMap<usize, Vec<&str>> = BTreeMap::new();
    let mut edges_by_state: BTreeMap<usize, Vec<(String, usize)>> = BTreeMap::new();
    for transition in &state_space.transitions {
        outgoing
            .entry(transition.from)
            .or_default()
            .push(&transition.label);
        edges_by_state
            .entry(transition.from)
            .or_default()
            .push((transition.label.clone(), transition.to));
    }

    let mut out = String::new();
    for state_index in 0..state_space.states.len() {
        let initial_marker = if state_space.initial_state == state_index {
            "  <initial>"
        } else {
            ""
        };
        out.push_str(&format!("[state {state_index}]{initial_marker}\n"));
        if let Some(edges) = edges_by_state.get(&state_index) {
            for (label, to) in edges {
                out.push_str(&format!("  -- {label} --> [state {to}]\n"));
            }
        }
    }
    out
}

fn render_state_space_state(
    state_space: &StateSpaceArtifact,
    index: usize,
) -> Result<String, String> {
    let state = state_space
        .states
        .get(index)
        .ok_or_else(|| format!("state index {index} is out of bounds"))?;
    Ok(render_operational_state(state, index))
}

fn render_state_space_diff(
    state_space: &StateSpaceArtifact,
    from: usize,
    to: usize,
) -> Result<String, String> {
    let before = state_space_state_lines(state_space, from)?;
    let after = state_space_state_lines(state_space, to)?;
    render_state_diff(before, after, from, to)
}

fn state_space_state_lines(
    state_space: &StateSpaceArtifact,
    index: usize,
) -> Result<Vec<String>, String> {
    let state = state_space
        .states
        .get(index)
        .ok_or_else(|| format!("state index {index} is out of bounds"))?;
    Ok(operational_state_lines(state))
}

fn render_witness_summary(out: &mut String, witness: &WitnessEnvelope) {
    match witness.payload() {
        abide_witness::WitnessPayload::Operational(witness) => match witness {
            op::OperationalWitness::Counterexample { behavior } => {
                out.push_str("  witness kind: counterexample\n");
                out.push_str(&format!(
                    "  states: {}  transitions: {}\n",
                    behavior.states().len(),
                    behavior.transitions().len()
                ));
            }
            op::OperationalWitness::Deadlock { witness } => {
                out.push_str("  witness kind: deadlock\n");
                out.push_str(&format!(
                    "  states: {}  deadlocked_at: {}\n",
                    witness.behavior().states().len(),
                    witness.deadlocked_at()
                ));
            }
            op::OperationalWitness::Liveness { witness } => {
                out.push_str("  witness kind: liveness\n");
                out.push_str(&format!(
                    "  states: {}  loop_start: {}\n",
                    witness.behavior().states().len(),
                    witness.loop_start()
                ));
            }
        },
        abide_witness::WitnessPayload::Relational(witness) => match witness {
            rel::RelationalWitness::Snapshot(state) => {
                out.push_str("  witness kind: relational-snapshot\n");
                out.push_str(&format!(
                    "  relations: {}  evaluations: {}\n",
                    state.relation_instances().len(),
                    state.evaluations().len()
                ));
            }
            rel::RelationalWitness::Temporal(witness) => {
                out.push_str("  witness kind: relational-temporal\n");
                out.push_str(&format!(
                    "  states: {}  loop_start: {}\n",
                    witness.states().len(),
                    witness
                        .loop_start()
                        .map_or_else(|| "-".to_owned(), |v| v.to_string())
                ));
            }
        },
        _ => out.push_str("  witness summary unavailable for this witness family\n"),
    }
}

fn render_countermodel_summary(out: &mut String, countermodel: &Countermodel) {
    out.push_str("  countermodel\n");
    if let Some(backend) = countermodel.backend_name() {
        out.push_str(&format!("  backend: {backend}\n"));
    }
    if let Some(summary) = countermodel.summary_text() {
        out.push_str(&format!("  summary: {summary}\n"));
    }
    out.push_str(&format!("  bindings: {}\n", countermodel.bindings().len()));
}

fn render_proof_artifact_summary(out: &mut String, proof_artifact: &ProofArtifactRef) {
    out.push_str("  proof artifact\n");
    out.push_str(&format!("  locator: {}\n", proof_artifact.locator()));
    if let Some(backend) = proof_artifact.backend_name() {
        out.push_str(&format!("  backend: {backend}\n"));
    }
    if let Some(label) = proof_artifact.label_text() {
        out.push_str(&format!("  label: {label}\n"));
    }
    out.push_str(&format!("  checked: {}\n", proof_artifact.is_checked()));
}

fn render_witness_timeline(witness: &WitnessEnvelope) -> Result<String, String> {
    match witness.payload() {
        abide_witness::WitnessPayload::Operational(witness) => {
            let loop_start = match witness {
                op::OperationalWitness::Liveness { witness } => Some(witness.loop_start()),
                _ => None,
            };
            Ok(render_behavior_timeline(witness.behavior(), loop_start))
        }
        abide_witness::WitnessPayload::Relational(witness) => match witness {
            rel::RelationalWitness::Snapshot(_) => {
                Err("snapshot witnesses do not have a temporal timeline".to_owned())
            }
            rel::RelationalWitness::Temporal(witness) => {
                let mut out = String::new();
                for state_index in 0..witness.states().len() {
                    let loop_marker = if witness.loop_start() == Some(state_index) {
                        "  <loop-start>"
                    } else {
                        ""
                    };
                    out.push_str(&format!("[state {state_index}]{loop_marker}\n"));
                    if state_index + 1 < witness.states().len() {
                        out.push_str("  -- next -->\n");
                    }
                }
                Ok(out)
            }
        },
        _ => Err("timeline view is not available for this witness family".to_owned()),
    }
}

fn render_behavior_timeline(behavior: &op::Behavior, loop_start: Option<usize>) -> String {
    let mut out = String::new();
    for state_index in 0..behavior.states().len() {
        let loop_marker = if loop_start == Some(state_index) {
            "  <loop-start>"
        } else {
            ""
        };
        out.push_str(&format!("[state {state_index}]{loop_marker}\n"));
        if let Some(transition) = behavior.transition_after_state(state_index) {
            let label = if transition.atomic_steps().is_empty() {
                "(stutter)".to_owned()
            } else {
                transition
                    .atomic_steps()
                    .iter()
                    .map(|step| format!("{}::{}", step.system(), step.command()))
                    .collect::<Vec<_>>()
                    .join(" | ")
            };
            out.push_str(&format!("  -- {label} -->\n"));
        }
    }
    out
}

fn render_witness_state(witness: &WitnessEnvelope, index: usize) -> Result<String, String> {
    match witness.payload() {
        abide_witness::WitnessPayload::Operational(witness) => {
            let state = witness
                .behavior()
                .state(index)
                .ok_or_else(|| format!("state index {index} is out of bounds"))?;
            Ok(render_operational_state(state, index))
        }
        abide_witness::WitnessPayload::Relational(witness) => match witness {
            rel::RelationalWitness::Snapshot(state) => {
                if index != 0 {
                    return Err("snapshot witnesses only contain state 0".to_owned());
                }
                Ok(render_relational_state(state, index))
            }
            rel::RelationalWitness::Temporal(witness) => {
                let state = witness
                    .states()
                    .get(index)
                    .ok_or_else(|| format!("state index {index} is out of bounds"))?;
                Ok(render_relational_state(state, index))
            }
        },
        _ => Err("state view is not available for this witness family".to_owned()),
    }
}

fn render_behavior_state(behavior: &op::Behavior, index: usize) -> Result<String, String> {
    let state = behavior
        .state(index)
        .ok_or_else(|| format!("state index {index} is out of bounds"))?;
    Ok(render_operational_state(state, index))
}

fn render_witness_diff(
    witness: &WitnessEnvelope,
    from: usize,
    to: usize,
) -> Result<String, String> {
    let before = witness_state_lines(witness, from)?;
    let after = witness_state_lines(witness, to)?;
    let before_set: BTreeSet<_> = before.iter().cloned().collect();
    let after_set: BTreeSet<_> = after.iter().cloned().collect();
    let removed: Vec<_> = before_set.difference(&after_set).cloned().collect();
    let added: Vec<_> = after_set.difference(&before_set).cloned().collect();

    let mut out = String::new();
    out.push_str(&format!("Diff state {from} -> state {to}\n"));
    if removed.is_empty() && added.is_empty() {
        out.push_str("  (no semantic changes)\n");
        return Ok(out);
    }
    if !removed.is_empty() {
        out.push_str("  removed\n");
        for line in removed {
            out.push_str(&format!("    - {line}\n"));
        }
    }
    if !added.is_empty() {
        out.push_str("  added\n");
        for line in added {
            out.push_str(&format!("    + {line}\n"));
        }
    }
    Ok(out)
}

fn render_behavior_diff(behavior: &op::Behavior, from: usize, to: usize) -> Result<String, String> {
    let before = behavior_state_lines(behavior, from)?;
    let after = behavior_state_lines(behavior, to)?;
    render_state_diff(before, after, from, to)
}

fn witness_state_lines(witness: &WitnessEnvelope, index: usize) -> Result<Vec<String>, String> {
    match witness.payload() {
        abide_witness::WitnessPayload::Operational(witness) => {
            let state = witness
                .behavior()
                .state(index)
                .ok_or_else(|| format!("state index {index} is out of bounds"))?;
            Ok(operational_state_lines(state))
        }
        abide_witness::WitnessPayload::Relational(witness) => match witness {
            rel::RelationalWitness::Snapshot(state) => {
                if index != 0 {
                    return Err("snapshot witnesses only contain state 0".to_owned());
                }
                Ok(relational_state_lines(state))
            }
            rel::RelationalWitness::Temporal(witness) => {
                let state = witness
                    .states()
                    .get(index)
                    .ok_or_else(|| format!("state index {index} is out of bounds"))?;
                Ok(relational_state_lines(state))
            }
        },
        _ => Err("state view is not available for this witness family".to_owned()),
    }
}

fn behavior_state_lines(behavior: &op::Behavior, index: usize) -> Result<Vec<String>, String> {
    let state = behavior
        .state(index)
        .ok_or_else(|| format!("state index {index} is out of bounds"))?;
    Ok(operational_state_lines(state))
}

fn render_state_diff(
    before: Vec<String>,
    after: Vec<String>,
    from: usize,
    to: usize,
) -> Result<String, String> {
    let before_set: BTreeSet<_> = before.iter().cloned().collect();
    let after_set: BTreeSet<_> = after.iter().cloned().collect();
    let removed: Vec<_> = before_set.difference(&after_set).cloned().collect();
    let added: Vec<_> = after_set.difference(&before_set).cloned().collect();

    let mut out = String::new();
    out.push_str(&format!("Diff state {from} -> state {to}\n"));
    if removed.is_empty() && added.is_empty() {
        out.push_str("  (no semantic changes)\n");
        return Ok(out);
    }
    if !removed.is_empty() {
        out.push_str("  removed\n");
        for line in removed {
            out.push_str(&format!("    - {line}\n"));
        }
    }
    if !added.is_empty() {
        out.push_str("  added\n");
        for line in added {
            out.push_str(&format!("    + {line}\n"));
        }
    }
    Ok(out)
}

fn render_operational_state(state: &op::State, index: usize) -> String {
    let mut out = format!("State {index}\n");
    for line in operational_state_lines(state) {
        out.push_str("  ");
        out.push_str(&line);
        out.push('\n');
    }
    out
}

fn operational_state_lines(state: &op::State) -> Vec<String> {
    let mut lines = Vec::new();
    for (slot_ref, entity_state) in state.entity_slots() {
        lines.push(format!(
            "{}#{} active = {}",
            slot_ref.entity(),
            slot_ref.slot(),
            entity_state.active()
        ));
        for (field, value) in entity_state.fields() {
            lines.push(format!(
                "{}#{}.{} = {}",
                slot_ref.entity(),
                slot_ref.slot(),
                field,
                render_witness_value(value)
            ));
        }
    }
    for (system, fields) in state.system_fields() {
        for (field, value) in fields {
            lines.push(format!(
                "{}.{} = {}",
                system,
                field,
                render_witness_value(value)
            ));
        }
    }
    lines
}

fn render_relational_state(state: &rel::RelationalState, index: usize) -> String {
    let mut out = format!("State {index}\n");
    for line in relational_state_lines(state) {
        out.push_str("  ");
        out.push_str(&line);
        out.push('\n');
    }
    out
}

fn relational_state_lines(state: &rel::RelationalState) -> Vec<String> {
    let mut lines = Vec::new();
    for relation in state.relation_instances() {
        lines.push(format!("relation {}:", render_relation_id(relation.id())));
        for tuple in relation.relation().tuples() {
            lines.push(format!(
                "  ({})",
                tuple
                    .values()
                    .iter()
                    .map(render_witness_value)
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }
    for (name, value) in state.evaluations() {
        lines.push(format!("eval {name} = {}", render_witness_value(value)));
    }
    lines
}

fn render_relation_id(id: &rel::RelationId) -> String {
    match id {
        rel::RelationId::StoreExtent { store } => format!("store {store}"),
        rel::RelationId::Field { owner, field } => format!("field {owner}.{field}"),
        rel::RelationId::Named { name } => format!("named {name}"),
        rel::RelationId::Derived { name } => format!("derived {name}"),
    }
}

fn render_witness_value(value: &WitnessValue) -> String {
    match value {
        WitnessValue::Unknown => "?".to_owned(),
        WitnessValue::Int(v) => v.to_string(),
        WitnessValue::Bool(v) => v.to_string(),
        WitnessValue::Real(v) | WitnessValue::Float(v) | WitnessValue::String(v) => v.clone(),
        WitnessValue::Identity(v) => v.clone(),
        WitnessValue::EnumVariant {
            enum_name, variant, ..
        } => format!("{enum_name}::{variant}"),
        WitnessValue::SlotRef(slot_ref) => render_slot_ref(slot_ref),
        WitnessValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Record(fields) => render_record(fields),
        WitnessValue::Set(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Seq(values) => format!(
            "[{}]",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(k, v)| format!("{}: {}", render_witness_value(k), render_witness_value(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Opaque { display, ty } => match ty {
            Some(ty) => format!("{display}:{ty}"),
            None => display.clone(),
        },
    }
}

fn render_slot_ref(slot_ref: &EntitySlotRef) -> String {
    format!("{}#{}", slot_ref.entity(), slot_ref.slot())
}

fn render_record(fields: &BTreeMap<String, WitnessValue>) -> String {
    let mut parts = Vec::new();
    for (field, value) in fields {
        parts.push(format!("{field}: {}", render_witness_value(value)));
    }
    format!("{{{}}}", parts.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use abide_verify::verify::{ExplicitStateSpaceStoreBound, ExplicitStateSpaceTransition};

    fn order_status(variant: &str) -> WitnessValue {
        WitnessValue::EnumVariant {
            enum_name: "OrderStatus".to_owned(),
            variant: variant.to_owned(),
            fields: BTreeMap::new(),
        }
    }

    fn sample_state(status: &str) -> op::State {
        op::State::builder()
            .entity_slot(
                EntitySlotRef::new("Order", 0),
                op::EntityState::builder(true)
                    .field("status", order_status(status))
                    .build(),
            )
            .system_field(
                "Shop",
                "phase",
                WitnessValue::String(format!("phase-{status}")),
            )
            .build()
    }

    fn sample_behavior() -> op::Behavior {
        let transition = op::Transition::builder()
            .atomic_step(
                op::AtomicStep::builder(
                    op::AtomicStepId::new("ship").expect("valid id"),
                    "Shop",
                    "ship",
                )
                .build()
                .expect("valid step"),
            )
            .build()
            .expect("valid transition");

        op::Behavior::builder()
            .state(sample_state("Pending"))
            .transition(transition)
            .state(sample_state("Shipped"))
            .build()
            .expect("valid behavior")
    }

    fn operational_evidence(witness: op::OperationalWitness) -> EvidenceEnvelope {
        EvidenceEnvelope::witness(WitnessEnvelope::operational(witness).expect("valid envelope"))
            .expect("valid evidence")
    }

    fn sample_operational_evidence() -> EvidenceEnvelope {
        operational_evidence(
            op::OperationalWitness::counterexample(sample_behavior()).expect("valid witness"),
        )
    }

    fn sample_liveness_evidence() -> EvidenceEnvelope {
        operational_evidence(
            op::OperationalWitness::liveness(sample_behavior(), 1).expect("valid witness"),
        )
    }

    fn sample_relational_state(open: bool) -> rel::RelationalState {
        rel::RelationalState::builder()
            .extent_member("tickets", EntitySlotRef::new("Ticket", 0))
            .expect("valid extent")
            .field_relation(
                "Ticket",
                "status",
                rel::RelationInstance::builder(2)
                    .tuple(rel::TupleValue::new(vec![
                        WitnessValue::SlotRef(EntitySlotRef::new("Ticket", 0)),
                        if open {
                            WitnessValue::String("Open".to_owned())
                        } else {
                            WitnessValue::String("Closed".to_owned())
                        },
                    ]))
                    .expect("valid tuple")
                    .build()
                    .expect("valid relation"),
            )
            .expect("valid field relation")
            .evaluation("is_open", WitnessValue::Bool(open))
            .expect("valid eval")
            .build()
            .expect("valid relational state")
    }

    fn relational_evidence(witness: rel::RelationalWitness) -> EvidenceEnvelope {
        EvidenceEnvelope::witness(WitnessEnvelope::relational(witness).expect("valid envelope"))
            .expect("valid evidence")
    }

    fn sample_relational_snapshot_evidence() -> EvidenceEnvelope {
        relational_evidence(
            rel::RelationalWitness::snapshot(sample_relational_state(true))
                .expect("valid snapshot"),
        )
    }

    fn sample_relational_temporal_evidence() -> EvidenceEnvelope {
        relational_evidence(
            rel::RelationalWitness::temporal(
                rel::TemporalRelationalWitness::new(
                    vec![
                        sample_relational_state(true),
                        sample_relational_state(false),
                    ],
                    Some(1),
                )
                .expect("valid temporal"),
            )
            .expect("valid temporal witness"),
        )
    }

    fn sample_countermodel_evidence() -> EvidenceEnvelope {
        EvidenceEnvelope::countermodel(
            Countermodel::new()
                .backend("z3")
                .summary("negated VC is satisfiable")
                .binding(
                    abide_witness::CountermodelBinding::new("x", WitnessValue::Int(42))
                        .expect("valid binding"),
                ),
        )
        .expect("valid countermodel")
    }

    fn sample_proof_ref_evidence() -> EvidenceEnvelope {
        EvidenceEnvelope::proof_artifact_ref(
            ProofArtifactRef::new("proofs/no_overdraft.agda")
                .expect("valid proof ref")
                .backend("agda")
                .label("no_overdraft")
                .checked(true),
        )
        .expect("valid proof ref evidence")
    }

    fn evidence_artifact(
        result_kind: &'static str,
        name: &str,
        evidence: EvidenceEnvelope,
    ) -> Artifact {
        Artifact {
            id: 1,
            name: name.to_owned(),
            result_kind,
            payload: ArtifactPayload::Evidence(evidence),
            evidence_extraction_error: None,
        }
    }

    fn sample_state_space() -> ExplicitStateSpace {
        ExplicitStateSpace {
            systems: vec!["Shop".to_owned()],
            stutter: true,
            depth_bound: Some(2),
            store_bounds: vec![ExplicitStateSpaceStoreBound {
                name: "orders".to_owned(),
                entity_type: "Order".to_owned(),
                slots: 1,
            }],
            states: vec![sample_state("Pending"), sample_state("Shipped")],
            initial_state: 0,
            transitions: vec![ExplicitStateSpaceTransition {
                from: 0,
                to: 1,
                label: "Shop::ship".to_owned(),
            }],
        }
    }

    #[test]
    fn store_resolves_latest_name_and_kind_name_selectors() {
        let mut store = ArtifactStore::default();
        let results = vec![
            VerificationResult::Counterexample {
                name: "safe".to_owned(),
                evidence: Some(sample_operational_evidence()),
                evidence_extraction_error: None,
                replay: None,
                assumptions: vec![],
                span: None,
                file: None,
            },
            VerificationResult::Deadlock {
                name: "safe".to_owned(),
                evidence: Some(sample_operational_evidence()),
                evidence_extraction_error: None,
                step: 1,
                reason: "stuck".to_owned(),
                event_diagnostics: vec![],
                assumptions: vec![],
                span: None,
                file: None,
            },
        ];

        assert_eq!(store.record_verify_results(&results), 2);
        assert_eq!(
            store.resolve("1").expect("id 1").result_kind,
            "counterexample"
        );
        assert_eq!(
            store.resolve("safe").expect("latest safe").result_kind,
            "deadlock"
        );
        assert_eq!(
            store
                .resolve("counterexample:safe")
                .expect("kind-qualified")
                .result_kind,
            "counterexample"
        );
        assert!(store.resolve("unknown").is_none());
    }

    #[test]
    fn store_records_admitted_liveness_and_payload_variants() {
        let mut store = ArtifactStore::default();
        let results = vec![
            VerificationResult::Admitted {
                name: "external_proof".to_owned(),
                reason: "trusted proof".to_owned(),
                time_ms: 2,
                evidence: Some(sample_proof_ref_evidence()),
                assumptions: vec![],
                span: None,
                file: None,
            },
            VerificationResult::LivenessViolation {
                name: "eventually_paid".to_owned(),
                evidence: Some(sample_liveness_evidence()),
                evidence_extraction_error: Some("partial lasso".to_owned()),
                loop_start: 1,
                fairness_analysis: vec![],
                assumptions: vec![],
                span: None,
                file: None,
            },
        ];

        assert_eq!(store.record_verify_results(&results), 2);
        let admitted = store.resolve("admitted:external_proof").expect("admitted");
        assert_eq!(admitted.result_kind, "admitted");
        assert!(admitted.summary_line().contains("proof-artifact-ref"));

        let liveness = store
            .resolve("liveness-violation:eventually_paid")
            .expect("liveness");
        assert_eq!(liveness.result_kind, "liveness-violation");
        assert_eq!(
            liveness.evidence_extraction_error.as_deref(),
            Some("partial lasso")
        );
        assert!(liveness.summary_line().contains("operational-witness"));
    }

    #[test]
    fn payload_kind_labels_cover_all_artifact_payloads() {
        assert_eq!(
            payload_kind_label(&ArtifactPayload::Evidence(sample_operational_evidence())),
            "operational-witness"
        );
        assert_eq!(
            payload_kind_label(&ArtifactPayload::Evidence(
                sample_relational_snapshot_evidence()
            )),
            "relational-witness"
        );
        assert_eq!(
            payload_kind_label(&ArtifactPayload::Evidence(sample_countermodel_evidence())),
            "countermodel"
        );
        assert_eq!(
            payload_kind_label(&ArtifactPayload::Evidence(sample_proof_ref_evidence())),
            "proof-artifact-ref"
        );
        assert_eq!(
            payload_kind_label(&ArtifactPayload::Simulation(SimulationArtifact {
                systems: vec!["Shop".to_owned()],
                seed: 1,
                steps_requested: 0,
                steps_executed: 0,
                termination: SimulationTermination::StepLimit,
                behavior: op::Behavior::builder().build().expect("empty behavior"),
            })),
            "simulation"
        );
        assert_eq!(
            payload_kind_label(&ArtifactPayload::StateSpace(sample_state_space())),
            "state-space"
        );
    }

    #[test]
    fn simulation_artifact_renders_and_exports() {
        let mut store = ArtifactStore::default();
        let simulation = SimulationArtifact {
            systems: vec!["Shop".to_owned()],
            seed: 11,
            steps_requested: 4,
            steps_executed: 1,
            termination: SimulationTermination::StepLimit,
            behavior: sample_behavior(),
        };

        assert_eq!(
            store.record_simulation_result("Shop".to_owned(), simulation),
            1
        );
        let artifact = store
            .resolve("simulation:Shop")
            .expect("simulation selector");
        let draw = artifact.render_draw().expect("draw");
        assert!(draw.contains("[state 0]"));
        assert!(draw.contains("Shop::ship"));
        assert!(artifact
            .render_state(0)
            .expect("state")
            .contains("Order#0.status = OrderStatus::Pending"));
        assert!(artifact
            .render_diff(0, 1)
            .expect("diff")
            .contains("OrderStatus::Shipped"));
        assert!(artifact
            .export_json()
            .expect("json")
            .contains("\"systems\""));
    }

    #[test]
    fn state_space_artifact_renders_graph_state_and_diff() {
        let artifact = Artifact {
            id: 1,
            name: "explore_shop".to_owned(),
            result_kind: "state-space",
            payload: ArtifactPayload::StateSpace(sample_state_space()),
            evidence_extraction_error: None,
        };

        let show = artifact.render_show();
        assert!(show.contains("bounded state-space exploration"));
        assert!(show.contains("Store<Order>[1]"));

        let graph = artifact.render_draw().expect("graph");
        assert!(graph.contains("[state 0]  <initial>"));
        assert!(graph.contains("-- Shop::ship --> [state 1]"));

        assert!(artifact
            .render_state(1)
            .expect("state")
            .contains("Shop.phase = phase-Shipped"));
        assert!(artifact.render_diff(0, 1).expect("diff").contains("added"));
        assert!(artifact.render_state(9).is_err());
    }

    #[test]
    fn operational_witness_artifact_renders_summary_timeline_state_and_diff() {
        let artifact =
            evidence_artifact("counterexample", "bad_trace", sample_operational_evidence());

        let show = artifact.render_show();
        assert!(show.contains("witness kind: counterexample"));
        assert!(show.contains("states: 2  transitions: 1"));

        let timeline = artifact.render_draw().expect("timeline");
        assert!(timeline.contains("[state 0]"));
        assert!(timeline.contains("-- Shop::ship -->"));

        assert!(artifact
            .render_state(0)
            .expect("state")
            .contains("Order#0 active = true"));
        let diff = artifact.render_diff(0, 1).expect("diff");
        assert!(diff.contains("removed"));
        assert!(diff.contains("added"));
        assert!(artifact.render_state(3).is_err());
    }

    #[test]
    fn liveness_witness_timeline_marks_loop_start() {
        let artifact = evidence_artifact(
            "liveness-violation",
            "eventually_paid",
            sample_liveness_evidence(),
        );

        let show = artifact.render_show();
        assert!(show.contains("witness kind: liveness"));
        assert!(show.contains("loop_start: 1"));
        assert!(artifact
            .render_draw()
            .expect("timeline")
            .contains("[state 1]  <loop-start>"));
    }

    #[test]
    fn relational_snapshot_witness_renders_state_and_rejects_timeline() {
        let evidence = sample_relational_snapshot_evidence();
        let EvidencePayload::Witness(witness) = evidence.payload() else {
            panic!("expected witness evidence");
        };
        assert!(witness_state_lines(witness, 0).is_ok());
        assert!(witness_state_lines(witness, 1).is_err());

        let artifact = evidence_artifact("scene-pass", "snapshot", evidence);

        let show = artifact.render_show();
        assert!(show.contains("witness kind: relational-snapshot"));
        assert!(show.contains("relations: 2  evaluations: 1"));
        assert!(artifact.render_draw().is_err());

        let state = artifact.render_state(0).expect("snapshot state");
        assert!(state.contains("relation store tickets"));
        assert!(state.contains("eval is_open = true"));
        assert!(artifact.render_state(1).is_err());
        assert!(artifact.render_diff(1, 0).is_err());
    }

    #[test]
    fn relational_temporal_witness_renders_timeline_state_and_diff() {
        let artifact = evidence_artifact(
            "counterexample",
            "rel_trace",
            sample_relational_temporal_evidence(),
        );

        let show = artifact.render_show();
        assert!(show.contains("witness kind: relational-temporal"));
        assert!(show.contains("states: 2  loop_start: 1"));

        let timeline = artifact.render_draw().expect("timeline");
        assert_eq!(
            timeline,
            "[state 0]\n  -- next -->\n[state 1]  <loop-start>\n"
        );

        assert!(artifact.render_state(1).expect("state").contains("Closed"));
        assert!(artifact
            .render_diff(0, 1)
            .expect("diff")
            .contains("is_open = false"));
    }

    #[test]
    fn countermodel_and_proof_ref_artifacts_render_summaries_and_reject_views() {
        let countermodel =
            evidence_artifact("counterexample", "bad_vc", sample_countermodel_evidence());
        let countermodel_show = countermodel.render_show();
        assert!(countermodel_show.contains("countermodel"));
        assert!(countermodel_show.contains("backend: z3"));
        assert!(countermodel_show.contains("bindings: 1"));
        assert!(countermodel.render_draw().is_err());
        assert!(countermodel.render_state(0).is_err());
        assert!(countermodel.render_diff(0, 1).is_err());

        let proof = evidence_artifact("admitted", "trusted", sample_proof_ref_evidence());
        let proof_show = proof.render_show();
        assert!(proof_show.contains("proof artifact"));
        assert!(proof_show.contains("locator: proofs/no_overdraft.agda"));
        assert!(proof_show.contains("backend: agda"));
        assert!(proof_show.contains("checked: true"));
        assert!(proof.render_draw().is_err());
    }

    #[test]
    fn witness_value_rendering_covers_structural_values() {
        let mut record = BTreeMap::new();
        record.insert("status".to_owned(), order_status("Paid"));
        record.insert("total".to_owned(), WitnessValue::Int(42));

        assert_eq!(render_witness_value(&WitnessValue::Unknown), "?");
        assert_eq!(render_witness_value(&WitnessValue::Bool(true)), "true");
        assert_eq!(
            render_witness_value(&WitnessValue::Real("1/3".to_owned())),
            "1/3"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Float("1.5".to_owned())),
            "1.5"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Identity("order-1".to_owned())),
            "order-1"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::SlotRef(EntitySlotRef::new("Order", 2))),
            "Order#2"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Tuple(vec![
                WitnessValue::Int(1),
                WitnessValue::String("ok".to_owned()),
            ])),
            "(1, ok)"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Record(record)),
            "{status: OrderStatus::Paid, total: 42}"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Set(vec![
                WitnessValue::Int(1),
                WitnessValue::Int(2),
            ])),
            "{1, 2}"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Seq(vec![
                WitnessValue::String("a".to_owned()),
                WitnessValue::String("b".to_owned()),
            ])),
            "[a, b]"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Map(vec![(
                WitnessValue::String("key".to_owned()),
                WitnessValue::Bool(false),
            )])),
            "{key: false}"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Opaque {
                display: "opaque".to_owned(),
                ty: Some("T".to_owned()),
            }),
            "opaque:T"
        );
        assert_eq!(
            render_witness_value(&WitnessValue::Opaque {
                display: "opaque".to_owned(),
                ty: None,
            }),
            "opaque"
        );
    }

    #[test]
    fn state_diff_reports_no_changes_removed_and_added() {
        assert!(
            render_state_diff(vec!["a".to_owned()], vec!["a".to_owned()], 0, 1)
                .expect("no changes")
                .contains("(no semantic changes)")
        );

        let added_only =
            render_state_diff(Vec::new(), vec!["c".to_owned()], 0, 1).expect("added-only diff");
        assert!(!added_only.contains("(no semantic changes)"));
        assert!(added_only.contains("added"));
        assert!(added_only.contains("+ c"));

        let diff = render_state_diff(
            vec!["a".to_owned(), "b".to_owned()],
            vec!["b".to_owned(), "c".to_owned()],
            0,
            1,
        )
        .expect("diff");
        assert!(diff.contains("removed"));
        assert!(diff.contains("- a"));
        assert!(diff.contains("added"));
        assert!(diff.contains("+ c"));
    }

    #[test]
    fn witness_diff_reports_added_only_changes() {
        let transition = op::Transition::builder().build().expect("valid transition");
        let behavior = op::Behavior::builder()
            .state(op::State::builder().build())
            .transition(transition)
            .state(sample_state("Pending"))
            .build()
            .expect("valid behavior");
        let witness = WitnessEnvelope::operational(
            op::OperationalWitness::counterexample(behavior).expect("valid witness"),
        )
        .expect("valid envelope");

        let diff = render_witness_diff(&witness, 0, 1).expect("witness diff");
        assert!(!diff.contains("(no semantic changes)"));
        assert!(diff.contains("added"));
        assert!(diff.contains("Order#0.status = OrderStatus::Pending"));
    }
}
