use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use miette::{Context, IntoDiagnostic};
use serde::{Deserialize, Serialize};

use crate::simulate::SimulationResult;
use crate::verify::VerificationResult;
use crate::witness::{op, EvidenceEnvelope, EvidencePayload, WitnessPayload, WitnessValue};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceArtifactBundle {
    kind: String,
    version: u32,
    files: Vec<String>,
    replay: ReplayInfo,
    artifacts: Vec<TraceArtifact>,
}

impl TraceArtifactBundle {
    pub fn new(files: &[PathBuf], replay: ReplayInfo, artifacts: Vec<TraceArtifact>) -> Self {
        Self {
            kind: "abide_trace_artifacts".to_owned(),
            version: 1,
            files: files
                .iter()
                .map(|path| path.display().to_string())
                .collect(),
            replay,
            artifacts,
        }
    }

    pub fn artifacts(&self) -> &[TraceArtifact] {
        &self.artifacts
    }

    pub fn files(&self) -> &[String] {
        &self.files
    }

    pub fn replay(&self) -> &ReplayInfo {
        &self.replay
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayInfo {
    command: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    working_directory: Option<String>,
}

impl ReplayInfo {
    pub fn from_current_process() -> Self {
        Self {
            command: std::env::args().collect(),
            working_directory: std::env::current_dir()
                .ok()
                .map(|path| path.display().to_string()),
        }
    }

    pub fn command(&self) -> &[String] {
        &self.command
    }

    pub fn working_directory(&self) -> Option<&str> {
        self.working_directory.as_deref()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceArtifact {
    id: usize,
    name: String,
    source: ArtifactSource,
    outcome: String,
    provenance: ArtifactProvenance,
    #[serde(skip_serializing_if = "Option::is_none")]
    normalized_trace: Option<NormalizedTrace>,
    payload: TraceArtifactPayload,
}

impl TraceArtifact {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn outcome(&self) -> &str {
        &self.outcome
    }

    pub fn id(&self) -> usize {
        self.id
    }

    pub fn source(&self) -> &ArtifactSource {
        &self.source
    }

    pub fn normalized_trace(&self) -> Option<&NormalizedTrace> {
        self.normalized_trace.as_ref()
    }

    pub fn payload(&self) -> &TraceArtifactPayload {
        &self.payload
    }
}

impl ArtifactSource {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Verify => "verify",
            Self::Simulate => "simulate",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactSource {
    Verify,
    Simulate,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArtifactProvenance {
    engine: String,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    options: BTreeMap<String, serde_json::Value>,
}

impl ArtifactProvenance {
    pub fn new(engine: impl Into<String>) -> Self {
        Self {
            engine: engine.into(),
            options: BTreeMap::new(),
        }
    }

    pub fn option(mut self, key: impl Into<String>, value: impl Serialize) -> Self {
        self.options.insert(
            key.into(),
            serde_json::to_value(value).unwrap_or(serde_json::Value::Null),
        );
        self
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", content = "payload", rename_all = "snake_case")]
pub enum TraceArtifactPayload {
    Evidence(EvidenceEnvelope),
    Simulation(SimulationResult),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NormalizedTrace {
    topology: TraceTopology,
    frames: Vec<TraceFrame>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TraceTopology {
    Linear,
    Lasso { loop_start: usize },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceFrame {
    index: usize,
    facts: Vec<TraceFact>,
    #[serde(skip_serializing_if = "Option::is_none")]
    transition_to_next: Option<TraceTransition>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceFact {
    owner: String,
    field: String,
    value: WitnessValue,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceTransition {
    label: String,
    atomic_steps: Vec<TraceAtomicStep>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    observations: Vec<TraceObservation>,
    changes: Vec<TraceChange>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceAtomicStep {
    id: String,
    system: String,
    command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    step_name: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    params: Vec<TraceBinding>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    choices: Vec<op::Choice>,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<WitnessValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceBinding {
    name: String,
    value: WitnessValue,
    #[serde(skip_serializing_if = "Option::is_none")]
    ty_hint: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceObservation {
    name: String,
    value: WitnessValue,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceChange {
    owner: String,
    field: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    before: Option<WitnessValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    after: Option<WitnessValue>,
}

#[derive(Debug, Clone)]
pub struct VerifyArtifactConfig<'a> {
    pub solver: &'a str,
    pub chc_solver: &'a str,
    pub bounded_only: bool,
    pub unbounded_only: bool,
    pub induction_timeout_ms: u64,
    pub bmc_timeout_ms: u64,
    pub ic3_timeout_ms: u64,
    pub no_ic3: bool,
    pub no_prop_verify: bool,
    pub no_fn_verify: bool,
    pub witness_semantics: &'a str,
    pub target: Option<&'a str>,
}

#[derive(Debug, Clone)]
pub struct SimulationArtifactConfig {
    pub slots_per_entity: usize,
    pub system: Option<String>,
}

pub fn verification_trace_artifacts(
    results: &[VerificationResult],
    config: &VerifyArtifactConfig<'_>,
) -> Vec<TraceArtifact> {
    results
        .iter()
        .filter_map(|result| verification_artifact(result, config))
        .enumerate()
        .map(|(index, mut artifact)| {
            artifact.id = index + 1;
            artifact
        })
        .collect()
}

fn verification_artifact(
    result: &VerificationResult,
    config: &VerifyArtifactConfig<'_>,
) -> Option<TraceArtifact> {
    let (name, outcome, evidence) = match result {
        VerificationResult::Counterexample { name, evidence, .. } => {
            (name.clone(), "counterexample", evidence.clone()?)
        }
        VerificationResult::Deadlock { name, evidence, .. } => {
            (name.clone(), "deadlock", evidence.clone()?)
        }
        VerificationResult::LivenessViolation { name, evidence, .. } => {
            (name.clone(), "liveness_violation", evidence.clone()?)
        }
        VerificationResult::Admitted { name, evidence, .. } => {
            (name.clone(), "admitted", evidence.clone()?)
        }
        _ => return None,
    };

    let normalized_trace = normalized_trace_for_evidence(&evidence);

    Some(TraceArtifact {
        id: 0,
        name,
        source: ArtifactSource::Verify,
        outcome: outcome.to_owned(),
        provenance: ArtifactProvenance::new("verify")
            .option("solver", config.solver)
            .option("chc_solver", config.chc_solver)
            .option("bounded_only", config.bounded_only)
            .option("unbounded_only", config.unbounded_only)
            .option("induction_timeout_ms", config.induction_timeout_ms)
            .option("bmc_timeout_ms", config.bmc_timeout_ms)
            .option("ic3_timeout_ms", config.ic3_timeout_ms)
            .option("no_ic3", config.no_ic3)
            .option("no_prop_verify", config.no_prop_verify)
            .option("no_fn_verify", config.no_fn_verify)
            .option("witness_semantics", config.witness_semantics)
            .option("target", config.target),
        normalized_trace,
        payload: TraceArtifactPayload::Evidence(evidence),
    })
}

pub fn simulation_trace_artifact(
    simulation: SimulationResult,
    config: &SimulationArtifactConfig,
) -> TraceArtifact {
    TraceArtifact {
        id: 1,
        name: simulation.systems.join(","),
        source: ArtifactSource::Simulate,
        outcome: simulation_outcome(&simulation).to_owned(),
        provenance: ArtifactProvenance::new("simulate")
            .option("seed", simulation.seed)
            .option("steps_requested", simulation.steps_requested)
            .option("steps_executed", simulation.steps_executed)
            .option("slots_per_entity", config.slots_per_entity)
            .option("system", &config.system),
        normalized_trace: Some(normalized_trace_from_behavior(
            &simulation.behavior,
            TraceTopology::Linear,
        )),
        payload: TraceArtifactPayload::Simulation(simulation),
    }
}

fn normalized_trace_for_evidence(evidence: &EvidenceEnvelope) -> Option<NormalizedTrace> {
    let EvidencePayload::Witness(witness) = evidence.payload() else {
        return None;
    };
    let WitnessPayload::Operational(witness) = witness.payload() else {
        return None;
    };
    let topology = match witness {
        op::OperationalWitness::Counterexample { .. } | op::OperationalWitness::Deadlock { .. } => {
            TraceTopology::Linear
        }
        op::OperationalWitness::Liveness { witness } => TraceTopology::Lasso {
            loop_start: witness.loop_start(),
        },
    };
    Some(normalized_trace_from_behavior(witness.behavior(), topology))
}

fn normalized_trace_from_behavior(
    behavior: &op::Behavior,
    topology: TraceTopology,
) -> NormalizedTrace {
    let frames = behavior
        .states()
        .iter()
        .enumerate()
        .map(|(index, state)| TraceFrame {
            index,
            facts: trace_facts_for_state(state),
            transition_to_next: behavior.transition_after_state(index).map(|transition| {
                let next = behavior.state(index + 1);
                trace_transition(transition, state, next)
            }),
        })
        .collect();
    NormalizedTrace { topology, frames }
}

fn trace_facts_for_state(state: &op::State) -> Vec<TraceFact> {
    state_value_map(state)
        .into_iter()
        .map(|((owner, field), value)| TraceFact {
            owner,
            field,
            value,
        })
        .collect()
}

fn state_value_map(state: &op::State) -> BTreeMap<(String, String), WitnessValue> {
    let mut values = BTreeMap::new();
    for (slot_ref, entity_state) in state.entity_slots() {
        if !entity_state.active() {
            continue;
        }
        let owner = format!("{}[{}]", slot_ref.entity(), slot_ref.slot());
        for (field, value) in entity_state.fields() {
            values.insert((owner.clone(), field.clone()), value.clone());
        }
    }
    for (system, fields) in state.system_fields() {
        for (field, value) in fields {
            values.insert((format!("System::{system}"), field.clone()), value.clone());
        }
    }
    values
}

fn trace_transition(
    transition: &op::Transition,
    before: &op::State,
    after: Option<&op::State>,
) -> TraceTransition {
    let atomic_steps = transition
        .atomic_steps()
        .iter()
        .map(trace_atomic_step)
        .collect::<Vec<_>>();
    let label = if atomic_steps.is_empty() {
        "stutter".to_owned()
    } else {
        atomic_steps
            .iter()
            .map(|step| format!("{}::{}", step.system, step.command))
            .collect::<Vec<_>>()
            .join(" | ")
    };
    TraceTransition {
        label,
        atomic_steps,
        observations: transition
            .observations()
            .iter()
            .map(|observation| TraceObservation {
                name: observation.name().to_owned(),
                value: observation.value().clone(),
            })
            .collect(),
        changes: after.map_or_else(Vec::new, |after| {
            trace_changes_between_states(before, after)
        }),
    }
}

fn trace_atomic_step(step: &op::AtomicStep) -> TraceAtomicStep {
    TraceAtomicStep {
        id: step.id().as_str().to_owned(),
        system: step.system().to_owned(),
        command: step.command().to_owned(),
        step_name: step.step_name().map(str::to_owned),
        params: step
            .params()
            .iter()
            .map(|binding| TraceBinding {
                name: binding.name().to_owned(),
                value: binding.value().clone(),
                ty_hint: binding.ty_hint().map(str::to_owned),
            })
            .collect(),
        choices: step.choices().to_vec(),
        result: step.result().cloned(),
    }
}

fn trace_changes_between_states(before: &op::State, after: &op::State) -> Vec<TraceChange> {
    let before = state_value_map(before);
    let after = state_value_map(after);
    before
        .keys()
        .chain(after.keys())
        .cloned()
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .filter_map(|(owner, field)| {
            let before_value = before.get(&(owner.clone(), field.clone())).cloned();
            let after_value = after.get(&(owner.clone(), field.clone())).cloned();
            (before_value != after_value).then_some(TraceChange {
                owner,
                field,
                before: before_value,
                after: after_value,
            })
        })
        .collect()
}

fn simulation_outcome(simulation: &SimulationResult) -> &'static str {
    if !simulation.violations.is_empty() {
        return "assertion_violation";
    }
    match simulation.termination {
        crate::simulate::SimulationTermination::StepLimit => "step_limit",
        crate::simulate::SimulationTermination::Deadlock { .. } => "deadlock",
    }
}

pub fn write_trace_artifact_bundle(
    path: &Path,
    bundle: &TraceArtifactBundle,
) -> miette::Result<()> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)
            .into_diagnostic()
            .wrap_err_with(|| {
                format!("failed to create artifact directory {}", parent.display())
            })?;
    }
    let body = serde_json::to_string_pretty(bundle)
        .into_diagnostic()
        .wrap_err("failed to serialize trace artifact JSON")?;
    fs::write(path, body)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to write trace artifact to {}", path.display()))
}

pub fn read_trace_artifact_bundle(path: &Path) -> miette::Result<TraceArtifactBundle> {
    let body = fs::read_to_string(path)
        .into_diagnostic()
        .wrap_err_with(|| format!("failed to read trace artifact from {}", path.display()))?;
    let bundle: TraceArtifactBundle = serde_json::from_str(&body)
        .into_diagnostic()
        .wrap_err_with(|| {
            format!(
                "failed to parse trace artifact JSON from {}",
                path.display()
            )
        })?;
    if bundle.kind != "abide_trace_artifacts" {
        return Err(miette::miette!(
            "unsupported artifact kind `{}`; expected `abide_trace_artifacts`",
            bundle.kind
        ));
    }
    if bundle.version != 1 {
        return Err(miette::miette!(
            "unsupported trace artifact version {}; expected 1",
            bundle.version
        ));
    }
    Ok(bundle)
}

pub fn render_trace_artifact_list(bundle: &TraceArtifactBundle) -> String {
    let mut out = String::new();
    out.push_str("Trace artifacts\n");
    if !bundle.files().is_empty() {
        out.push_str("files:\n");
        for file in bundle.files() {
            out.push_str(&format!("  - {file}\n"));
        }
    }
    if let Some(cwd) = bundle.replay().working_directory() {
        out.push_str(&format!("working directory: {cwd}\n"));
    }
    if !bundle.replay().command().is_empty() {
        out.push_str(&format!(
            "replay: {}\n",
            bundle.replay().command().join(" ")
        ));
    }
    if bundle.artifacts().is_empty() {
        out.push_str("artifacts: none\n");
        return out;
    }
    out.push_str("artifacts:\n");
    for artifact in bundle.artifacts() {
        let (frames, topology) = artifact.normalized_trace().map_or_else(
            || (0, "none".to_owned()),
            |trace| (trace.frames.len(), render_topology(&trace.topology)),
        );
        out.push_str(&format!(
            "  #{} {} [{}:{}] frames={frames} topology={topology}\n",
            artifact.id(),
            artifact.name(),
            artifact.source().as_str(),
            artifact.outcome(),
        ));
    }
    out
}

pub fn select_trace_artifact(
    bundle: &TraceArtifactBundle,
    id: usize,
) -> Result<&TraceArtifact, String> {
    bundle
        .artifacts()
        .iter()
        .find(|artifact| artifact.id() == id)
        .ok_or_else(|| {
            let available = bundle
                .artifacts()
                .iter()
                .map(|artifact| artifact.id().to_string())
                .collect::<Vec<_>>()
                .join(", ");
            if available.is_empty() {
                format!("trace artifact #{id} not found; bundle has no artifacts")
            } else {
                format!("trace artifact #{id} not found; available artifacts: {available}")
            }
        })
}

pub fn render_trace_artifact_draw(artifact: &TraceArtifact) -> Result<String, String> {
    let trace = require_normalized_trace(artifact)?;
    let mut out = String::new();
    out.push_str(&format!(
        "Artifact #{} {} [{}:{}]\n",
        artifact.id(),
        artifact.name(),
        artifact.source().as_str(),
        artifact.outcome()
    ));
    out.push_str(&format!("topology: {}\n", render_topology(&trace.topology)));
    for frame in &trace.frames {
        let marker = loop_frame_marker(&trace.topology, frame.index);
        out.push_str(&format!("frame {}{marker}\n", frame.index));
        for fact in &frame.facts {
            out.push_str(&format!(
                "  {}.{} = {}\n",
                fact.owner,
                fact.field,
                render_trace_value(&fact.value)
            ));
        }
        if let Some(transition) = &frame.transition_to_next {
            out.push_str(&format!("  -- {} -->\n", transition.label));
            for step in &transition.atomic_steps {
                out.push_str(&format!(
                    "    step {} {}::{}",
                    step.id, step.system, step.command
                ));
                if let Some(step_name) = &step.step_name {
                    out.push_str(&format!(" as {step_name}"));
                }
                out.push('\n');
                for param in &step.params {
                    out.push_str(&format!(
                        "      param {} = {}\n",
                        param.name,
                        render_trace_value(&param.value)
                    ));
                }
                for choice in &step.choices {
                    out.push_str(&format!("      {}\n", render_choice(choice)));
                }
                if let Some(result) = &step.result {
                    out.push_str(&format!("      result = {}\n", render_trace_value(result)));
                }
            }
            for observation in &transition.observations {
                out.push_str(&format!(
                    "    observe {} = {}\n",
                    observation.name,
                    render_trace_value(&observation.value)
                ));
            }
            if !transition.changes.is_empty() {
                out.push_str("    changes:\n");
                for change in &transition.changes {
                    out.push_str(&format!(
                        "      {}.{}: {} -> {}\n",
                        change.owner,
                        change.field,
                        render_optional_trace_value(change.before.as_ref()),
                        render_optional_trace_value(change.after.as_ref())
                    ));
                }
            }
        }
    }
    if let TraceTopology::Lasso { loop_start } = &trace.topology {
        out.push_str(&format!(
            "loop: final frame returns to frame {loop_start}\n"
        ));
    }
    Ok(out)
}

pub fn render_trace_artifact_state(
    artifact: &TraceArtifact,
    index: usize,
) -> Result<String, String> {
    let trace = require_normalized_trace(artifact)?;
    let frame = trace
        .frames
        .iter()
        .find(|frame| frame.index == index)
        .ok_or_else(|| {
            let max = trace.frames.last().map_or(0, |frame| frame.index);
            format!("frame {index} not found; available frame range is 0..={max}")
        })?;
    let mut out = String::new();
    let marker = loop_frame_marker(&trace.topology, frame.index);
    out.push_str(&format!(
        "Artifact #{} {} frame {}{}\n",
        artifact.id(),
        artifact.name(),
        frame.index,
        marker
    ));
    if frame.facts.is_empty() {
        out.push_str("  no active state facts\n");
        return Ok(out);
    }
    for fact in &frame.facts {
        out.push_str(&format!(
            "  {}.{} = {}\n",
            fact.owner,
            fact.field,
            render_trace_value(&fact.value)
        ));
    }
    Ok(out)
}

pub fn render_trace_artifact_diff(
    artifact: &TraceArtifact,
    from: usize,
    to: usize,
) -> Result<String, String> {
    let trace = require_normalized_trace(artifact)?;
    let before = trace
        .frames
        .iter()
        .find(|frame| frame.index == from)
        .ok_or_else(|| format!("frame {from} not found"))?;
    let after = trace
        .frames
        .iter()
        .find(|frame| frame.index == to)
        .ok_or_else(|| format!("frame {to} not found"))?;
    let before = fact_map(before);
    let after = fact_map(after);
    let mut out = String::new();
    out.push_str(&format!(
        "Artifact #{} {} diff frame {} -> {}\n",
        artifact.id(),
        artifact.name(),
        from,
        to
    ));
    let mut has_diff = false;
    for key in before
        .keys()
        .chain(after.keys())
        .cloned()
        .collect::<std::collections::BTreeSet<_>>()
    {
        match (before.get(&key), after.get(&key)) {
            (Some(old), Some(new)) if old == new => {}
            (Some(old), Some(new)) => {
                has_diff = true;
                out.push_str(&format!("  ~ {key}: {old} -> {new}\n"));
            }
            (Some(old), None) => {
                has_diff = true;
                out.push_str(&format!("  - {key} = {old}\n"));
            }
            (None, Some(new)) => {
                has_diff = true;
                out.push_str(&format!("  + {key} = {new}\n"));
            }
            (None, None) => {}
        }
    }
    if !has_diff {
        out.push_str("  no state changes\n");
    }
    Ok(out)
}

pub fn render_trace_artifact_json(artifact: &TraceArtifact) -> Result<String, String> {
    serde_json::to_string_pretty(artifact).map_err(|err| {
        format!(
            "failed to serialize trace artifact #{}: {err}",
            artifact.id()
        )
    })
}

fn require_normalized_trace(artifact: &TraceArtifact) -> Result<&NormalizedTrace, String> {
    artifact.normalized_trace().ok_or_else(|| {
        format!(
            "artifact #{} has no normalized trace to inspect",
            artifact.id()
        )
    })
}

fn render_topology(topology: &TraceTopology) -> String {
    match topology {
        TraceTopology::Linear => "linear".to_owned(),
        TraceTopology::Lasso { loop_start } => format!("lasso(loop_start={loop_start})"),
    }
}

fn loop_frame_marker(topology: &TraceTopology, frame_index: usize) -> &'static str {
    match topology {
        TraceTopology::Lasso { loop_start } if *loop_start == frame_index => " [loop start]",
        _ => "",
    }
}

fn fact_map(frame: &TraceFrame) -> BTreeMap<String, String> {
    frame
        .facts
        .iter()
        .map(|fact| {
            (
                format!("{}.{}", fact.owner, fact.field),
                render_trace_value(&fact.value),
            )
        })
        .collect()
}

fn render_optional_trace_value(value: Option<&WitnessValue>) -> String {
    value
        .map(render_trace_value)
        .unwrap_or_else(|| "<absent>".to_owned())
}

fn render_choice(choice: &op::Choice) -> String {
    match choice {
        op::Choice::Choose { binder, selected } => {
            format!(
                "choose {binder} = {}[{}]",
                selected.entity(),
                selected.slot()
            )
        }
        op::Choice::ForAll { binder, iterated } => {
            let slots = iterated
                .iter()
                .map(|slot| format!("{}[{}]", slot.entity(), slot.slot()))
                .collect::<Vec<_>>()
                .join(", ");
            format!("for all {binder} in [{slots}]")
        }
        op::Choice::Create { created } => {
            format!("create {}[{}]", created.entity(), created.slot())
        }
    }
}

fn render_trace_value(value: &WitnessValue) -> String {
    match value {
        WitnessValue::Unknown => "?".to_owned(),
        WitnessValue::Int(value) => value.to_string(),
        WitnessValue::Bool(value) => value.to_string(),
        WitnessValue::Real(value) | WitnessValue::Float(value) | WitnessValue::String(value) => {
            value.clone()
        }
        WitnessValue::Identity(value) => format!("#{value}"),
        WitnessValue::EnumVariant { enum_name, variant } => {
            format!("@{enum_name}::{variant}")
        }
        WitnessValue::SlotRef(slot) => format!("{}[{}]", slot.entity(), slot.slot()),
        WitnessValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(render_trace_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(field, value)| format!("{field}: {}", render_trace_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Set(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(render_trace_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Seq(values) => format!(
            "[{}]",
            values
                .iter()
                .map(render_trace_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, value)| {
                    format!(
                        "{} -> {}",
                        render_trace_value(key),
                        render_trace_value(value)
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Opaque { display, .. } => display.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::{op, EvidenceEnvelope, WitnessEnvelope, WitnessValue};

    fn sample_behavior() -> op::Behavior {
        let state0 = op::State::builder()
            .system_field("Banking", "balance", WitnessValue::Int(0))
            .build();
        let state1 = op::State::builder()
            .system_field("Banking", "balance", WitnessValue::Int(-1))
            .build();
        let step = op::AtomicStep::builder(
            op::AtomicStepId::new("withdraw").expect("valid id"),
            "Banking",
            "withdraw",
        )
        .build()
        .expect("valid step");
        let transition = op::Transition::builder()
            .atomic_step(step)
            .build()
            .expect("valid transition");
        op::Behavior::from_parts(vec![state0, state1], vec![transition]).expect("valid behavior")
    }

    fn sample_evidence() -> EvidenceEnvelope {
        let witness =
            op::OperationalWitness::counterexample(sample_behavior()).expect("valid witness");
        EvidenceEnvelope::witness(WitnessEnvelope::operational(witness).expect("valid envelope"))
            .expect("valid evidence")
    }

    fn sample_liveness_evidence() -> EvidenceEnvelope {
        let witness =
            op::OperationalWitness::liveness(sample_behavior(), 1).expect("valid lasso witness");
        EvidenceEnvelope::witness(WitnessEnvelope::operational(witness).expect("valid envelope"))
            .expect("valid evidence")
    }

    fn verify_config() -> VerifyArtifactConfig<'static> {
        VerifyArtifactConfig {
            solver: "z3",
            chc_solver: "z3",
            bounded_only: true,
            unbounded_only: false,
            induction_timeout_ms: 1_000,
            bmc_timeout_ms: 2_000,
            ic3_timeout_ms: 3_000,
            no_ic3: true,
            no_prop_verify: false,
            no_fn_verify: false,
            witness_semantics: "operational",
            target: None,
        }
    }

    #[test]
    fn verification_artifacts_keep_replayable_evidence_and_provenance() {
        let results = vec![VerificationResult::Counterexample {
            name: "no_negatives".to_owned(),
            evidence: Some(sample_evidence()),
            evidence_extraction_error: None,
            assumptions: vec![],
            span: None,
            file: None,
        }];

        let artifacts = verification_trace_artifacts(&results, &verify_config());

        assert_eq!(artifacts.len(), 1);
        assert_eq!(artifacts[0].name(), "no_negatives");
        assert_eq!(artifacts[0].outcome(), "counterexample");
        let json = serde_json::to_value(&artifacts[0]).expect("serialize artifact");
        assert_eq!(json["provenance"]["options"]["solver"], "z3");
        assert_eq!(json["payload"]["kind"], "evidence");
        assert_eq!(json["normalized_trace"]["topology"]["kind"], "linear");
        assert_eq!(json["normalized_trace"]["frames"][0]["index"], 0);
        assert_eq!(
            json["normalized_trace"]["frames"][0]["transition_to_next"]["label"],
            "Banking::withdraw"
        );
        assert_eq!(
            json["normalized_trace"]["frames"][0]["transition_to_next"]["changes"][0]["field"],
            "balance"
        );
    }

    #[test]
    fn simulation_artifact_records_seed_bounds_and_behavior() {
        let simulation = SimulationResult {
            systems: vec!["Banking".to_owned()],
            seed: 9,
            steps_requested: 10,
            steps_executed: 1,
            termination: crate::simulate::SimulationTermination::StepLimit,
            violations: vec![],
            behavior: sample_behavior(),
        };
        let artifact = simulation_trace_artifact(
            simulation,
            &SimulationArtifactConfig {
                slots_per_entity: 4,
                system: Some("Banking".to_owned()),
            },
        );

        assert_eq!(artifact.name(), "Banking");
        assert_eq!(artifact.outcome(), "step_limit");
        let json = serde_json::to_value(&artifact).expect("serialize artifact");
        assert_eq!(json["provenance"]["options"]["seed"], 9);
        assert_eq!(json["payload"]["kind"], "simulation");
        assert_eq!(
            json["normalized_trace"]["frames"][0]["facts"]
                .as_array()
                .expect("facts array")
                .len(),
            1
        );
        assert_eq!(
            json["normalized_trace"]["frames"][0]["transition_to_next"]["changes"][0]["after"]
                ["value"],
            -1
        );
    }

    #[test]
    fn trace_artifact_bundle_round_trips_and_renders_inspection_views() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("trace.json");
        let simulation = SimulationResult {
            systems: vec!["Banking".to_owned()],
            seed: 9,
            steps_requested: 10,
            steps_executed: 1,
            termination: crate::simulate::SimulationTermination::StepLimit,
            violations: vec![],
            behavior: sample_behavior(),
        };
        let artifact = simulation_trace_artifact(
            simulation,
            &SimulationArtifactConfig {
                slots_per_entity: 4,
                system: Some("Banking".to_owned()),
            },
        );
        let bundle = TraceArtifactBundle::new(
            &[PathBuf::from("banking.ab")],
            ReplayInfo {
                command: vec!["abide".to_owned(), "run".to_owned()],
                working_directory: Some("/tmp/project".to_owned()),
            },
            vec![artifact],
        );

        write_trace_artifact_bundle(&path, &bundle).expect("write artifact bundle");
        let loaded = read_trace_artifact_bundle(&path).expect("read artifact bundle");
        let list = render_trace_artifact_list(&loaded);

        assert!(list.contains("Trace artifacts"));
        assert!(list.contains("#1 Banking [simulate:step_limit] frames=2 topology=linear"));
        let selected = select_trace_artifact(&loaded, 1).expect("select artifact");

        let draw = render_trace_artifact_draw(selected).expect("draw trace");
        assert!(draw.contains("topology: linear"));
        assert!(draw.contains("frame 0"));
        assert!(draw.contains("-- Banking::withdraw -->"));
        assert!(draw.contains("System::Banking.balance: 0 -> -1"));

        let state = render_trace_artifact_state(selected, 1).expect("frame state");
        assert!(state.contains("frame 1"));
        assert!(state.contains("System::Banking.balance = -1"));

        let diff = render_trace_artifact_diff(selected, 0, 1).expect("frame diff");
        assert!(diff.contains("~ System::Banking.balance: 0 -> -1"));

        let json = render_trace_artifact_json(selected).expect("artifact json");
        assert!(json.contains("\"name\": \"Banking\""));
    }

    #[test]
    fn liveness_trace_artifact_rendering_marks_lasso_loop_start() {
        let results = vec![VerificationResult::LivenessViolation {
            name: "eventually_paid".to_owned(),
            evidence: Some(sample_liveness_evidence()),
            evidence_extraction_error: None,
            loop_start: 1,
            fairness_analysis: vec![],
            assumptions: vec![],
            span: None,
            file: None,
        }];

        let artifacts = verification_trace_artifacts(&results, &verify_config());
        let bundle = TraceArtifactBundle::new(
            &[PathBuf::from("banking.ab")],
            ReplayInfo {
                command: vec!["abide".to_owned(), "verify".to_owned()],
                working_directory: None,
            },
            artifacts,
        );

        let list = render_trace_artifact_list(&bundle);
        assert!(
            list.contains(
                "#1 eventually_paid [verify:liveness_violation] frames=2 topology=lasso(loop_start=1)"
            ),
            "{list}"
        );
        let selected = select_trace_artifact(&bundle, 1).expect("select artifact");

        let draw = render_trace_artifact_draw(selected).expect("draw lasso trace");
        assert!(draw.contains("topology: lasso(loop_start=1)"), "{draw}");
        assert!(draw.contains("frame 1 [loop start]"), "{draw}");
        assert!(
            draw.contains("loop: final frame returns to frame 1"),
            "{draw}"
        );

        let state = render_trace_artifact_state(selected, 1).expect("lasso state");
        assert!(state.contains("frame 1 [loop start]"), "{state}");
    }
}
