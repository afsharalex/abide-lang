use std::collections::{BTreeMap, BTreeSet};

use abide_verify::verify::{ExplicitStateSpace, VerificationResult};
use abide_witness::{
    op, rel, Countermodel, EntitySlotRef, EvidenceEnvelope, EvidencePayload, ProofArtifactRef,
    WitnessEnvelope, WitnessValue,
};
use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum SimulationTermination {
    StepLimit,
    Deadlock { reasons: Vec<String> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SimulationArtifact {
    pub systems: Vec<String>,
    pub seed: u64,
    pub steps_requested: usize,
    pub steps_executed: usize,
    pub termination: SimulationTermination,
    pub behavior: op::Behavior,
}

pub type StateSpaceArtifact = ExplicitStateSpace;

#[derive(Debug, Clone)]
pub enum ArtifactPayload {
    Evidence(EvidenceEnvelope),
    Simulation(SimulationArtifact),
    StateSpace(StateSpaceArtifact),
}

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
            ArtifactPayload::StateSpace(state_space) => render_state_space_state(state_space, index),
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
        let Some((name, result_kind, payload, extraction_error)) =
            artifact_parts_from_result_with_name(result, Some(name))
        else {
            return 0;
        };
        self.next_id += 1;
        self.artifacts.push(Artifact {
            id: self.next_id,
            name,
            result_kind,
            payload,
            evidence_extraction_error: extraction_error,
        });
        1
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

    pub fn record_state_space_result(&mut self, name: String, state_space: StateSpaceArtifact) -> usize {
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
        outgoing.entry(transition.from).or_default().push(&transition.label);
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
        WitnessValue::EnumVariant { enum_name, variant } => format!("{enum_name}::{variant}"),
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

    fn sample_operational_evidence() -> EvidenceEnvelope {
        let state0 = op::State::builder()
            .entity_slot(
                EntitySlotRef::new("Order", 0),
                op::EntityState::builder(true)
                    .field(
                        "status",
                        WitnessValue::EnumVariant {
                            enum_name: "OrderStatus".to_owned(),
                            variant: "Pending".to_owned(),
                        },
                    )
                    .build(),
            )
            .build();
        let state1 = op::State::builder()
            .entity_slot(
                EntitySlotRef::new("Order", 0),
                op::EntityState::builder(true)
                    .field(
                        "status",
                        WitnessValue::EnumVariant {
                            enum_name: "OrderStatus".to_owned(),
                            variant: "Shipped".to_owned(),
                        },
                    )
                    .build(),
            )
            .build();
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
        let witness = op::OperationalWitness::counterexample(
            op::Behavior::builder()
                .state(state0)
                .transition(transition)
                .state(state1)
                .build()
                .expect("valid behavior"),
        )
        .expect("valid witness");
        EvidenceEnvelope::witness(WitnessEnvelope::operational(witness).expect("valid envelope"))
            .expect("valid evidence")
    }

    #[test]
    fn store_resolves_latest_name_and_kind_name_selectors() {
        let mut store = ArtifactStore::default();
        let results = vec![
            VerificationResult::Counterexample {
                name: "safe".to_owned(),
                evidence: Some(sample_operational_evidence()),
                evidence_extraction_error: None,
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
    fn simulation_artifact_renders_and_exports() {
        let mut store = ArtifactStore::default();
        let transition = op::Transition::builder().build().expect("valid transition");
        let behavior = op::Behavior::builder()
            .state(op::State::builder().build())
            .transition(transition)
            .state(op::State::builder().build())
            .build()
            .expect("valid behavior");
        let simulation = SimulationArtifact {
            systems: vec!["Shop".to_owned()],
            seed: 11,
            steps_requested: 4,
            steps_executed: 1,
            termination: SimulationTermination::StepLimit,
            behavior,
        };

        assert_eq!(
            store.record_simulation_result("Shop".to_owned(), simulation),
            1
        );
        let artifact = store
            .resolve("simulation:Shop")
            .expect("simulation selector");
        assert!(artifact.render_draw().expect("draw").contains("[state 0]"));
        assert!(artifact
            .export_json()
            .expect("json")
            .contains("\"systems\""));
    }
}
