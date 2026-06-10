//! Operational witnesses — concrete (state, transition, state, …)
//! sequences produced by the verifier when an obligation fails (or by
//! a scene when it succeeds).
//!
//! The shape is:
//!
//! ```text
//! Behavior = [State, Transition, State, Transition, … State]
//! Transition = one or more AtomicSteps (event firings) + observations
//! AtomicStep = system::command + Choice + StepRelation rewrites
//! State      = per-EntitySlot state + per-system field values
//! ```
//!
//! All public types use checked constructors / builders. The
//! `validate()` method on [`OperationalWitness`] re-asserts every
//! invariant — it is run at importer boundaries by
//! [`crate::WitnessEnvelope`].

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub use crate::value::{EntitySlotRef, WitnessValue};
use abide_core::span::Span;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Concrete state of a single entity slot at one [`State`].
///
/// `active` distinguishes a slot that has been allocated but not yet
/// initialized from one carrying real field values.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EntityState {
    active: bool,
    fields: BTreeMap<String, WitnessValue>,
}

impl EntityState {
    pub fn builder(active: bool) -> EntityStateBuilder {
        EntityStateBuilder {
            active,
            fields: BTreeMap::new(),
        }
    }

    pub fn active(&self) -> bool {
        self.active
    }

    pub fn fields(&self) -> &BTreeMap<String, WitnessValue> {
        &self.fields
    }
}

pub struct EntityStateBuilder {
    active: bool,
    fields: BTreeMap<String, WitnessValue>,
}

impl EntityStateBuilder {
    pub fn field(mut self, name: impl Into<String>, value: WitnessValue) -> Self {
        self.fields.insert(name.into(), value);
        self
    }

    pub fn build(self) -> EntityState {
        EntityState {
            active: self.active,
            fields: self.fields,
        }
    }
}

/// Concrete state snapshot in an operational witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct State {
    #[serde(
        serialize_with = "serialize_entity_slots",
        deserialize_with = "deserialize_entity_slots"
    )]
    entity_slots: BTreeMap<EntitySlotRef, EntityState>,
    system_fields: BTreeMap<String, BTreeMap<String, WitnessValue>>,
}

impl State {
    pub fn builder() -> StateBuilder {
        StateBuilder {
            entity_slots: BTreeMap::new(),
            system_fields: BTreeMap::new(),
        }
    }

    pub fn entity_slots(&self) -> &BTreeMap<EntitySlotRef, EntityState> {
        &self.entity_slots
    }

    pub fn system_fields(&self) -> &BTreeMap<String, BTreeMap<String, WitnessValue>> {
        &self.system_fields
    }
}

pub struct StateBuilder {
    entity_slots: BTreeMap<EntitySlotRef, EntityState>,
    system_fields: BTreeMap<String, BTreeMap<String, WitnessValue>>,
}

#[derive(Serialize, Deserialize)]
struct EntitySlotEntry {
    slot_ref: EntitySlotRef,
    state: EntityState,
}

fn serialize_entity_slots<S>(
    entity_slots: &BTreeMap<EntitySlotRef, EntityState>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let entries: Vec<EntitySlotEntry> = entity_slots
        .iter()
        .map(|(slot_ref, state)| EntitySlotEntry {
            slot_ref: slot_ref.clone(),
            state: state.clone(),
        })
        .collect();
    entries.serialize(serializer)
}

fn deserialize_entity_slots<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<EntitySlotRef, EntityState>, D::Error>
where
    D: Deserializer<'de>,
{
    let entries = Vec::<EntitySlotEntry>::deserialize(deserializer)?;
    Ok(entries
        .into_iter()
        .map(|entry| (entry.slot_ref, entry.state))
        .collect())
}

impl StateBuilder {
    pub fn entity_slot(mut self, slot: EntitySlotRef, state: EntityState) -> Self {
        self.entity_slots.insert(slot, state);
        self
    }

    pub fn system_field(
        mut self,
        system: impl Into<String>,
        field: impl Into<String>,
        value: WitnessValue,
    ) -> Self {
        self.system_fields
            .entry(system.into())
            .or_default()
            .insert(field.into(), value);
        self
    }

    pub fn build(self) -> State {
        State {
            entity_slots: self.entity_slots,
            system_fields: self.system_fields,
        }
    }
}

/// Concrete step-parameter binding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Binding {
    name: String,
    value: WitnessValue,
    #[serde(skip_serializing_if = "Option::is_none")]
    ty_hint: Option<String>,
}

impl Binding {
    pub fn new(name: impl Into<String>, value: WitnessValue) -> Result<Self, ValidationError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(ValidationError::EmptyBindingName);
        }
        Ok(Self {
            name,
            value,
            ty_hint: None,
        })
    }

    pub fn with_ty_hint(mut self, ty_hint: impl Into<String>) -> Self {
        self.ty_hint = Some(ty_hint.into());
        self
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn value(&self) -> &WitnessValue {
        &self.value
    }

    pub fn ty_hint(&self) -> Option<&str> {
        self.ty_hint.as_deref()
    }
}

/// Nondeterministic choice made during an atomic step.
///
/// Captures the surface-language constructs that introduce
/// nondeterminism so the witness can pin down exactly which entity (or
/// entities) the step touched.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Choice {
    /// `choose x: T` — one entity selected from a store.
    Choose {
        binder: String,
        selected: EntitySlotRef,
    },
    /// `for x in T` — iteration over many entities at this step.
    ForAll {
        binder: String,
        iterated: Vec<EntitySlotRef>,
    },
    /// `create T(...)` — a freshly allocated entity.
    Create { created: EntitySlotRef },
}

/// Stable identifier for an atomic step inside a transition.
///
/// Used to link [`StepRelation`] entries to the [`AtomicStep`]s they
/// constrain; cross-step references inside one transition resolve
/// through this id.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AtomicStepId(String);

impl AtomicStepId {
    pub fn new(id: impl Into<String>) -> Result<Self, ValidationError> {
        let id = id.into();
        if id.trim().is_empty() {
            return Err(ValidationError::EmptyAtomicStepId);
        }
        Ok(Self(id))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// One atomic operational step inside a witness transition.
///
/// An atomic step is the firing of one `system::command`, carrying
/// concrete parameter bindings, any nondeterministic [`Choice`]s the
/// step made, and the optional return value. Multiple atomic steps may
/// appear in a single [`Transition`] when composed via `&` (same-step)
/// or `||` (concurrent) in the source.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomicStep {
    id: AtomicStepId,
    system: String,
    command: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    step_name: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    params: Vec<Binding>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    choices: Vec<Choice>,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<WitnessValue>,
}

impl AtomicStep {
    pub fn builder(
        id: AtomicStepId,
        system: impl Into<String>,
        command: impl Into<String>,
    ) -> AtomicStepBuilder {
        AtomicStepBuilder {
            id,
            system: system.into(),
            command: command.into(),
            step_name: None,
            params: Vec::new(),
            choices: Vec::new(),
            result: None,
        }
    }

    pub fn id(&self) -> &AtomicStepId {
        &self.id
    }

    pub fn system(&self) -> &str {
        &self.system
    }

    pub fn command(&self) -> &str {
        &self.command
    }

    pub fn step_name(&self) -> Option<&str> {
        self.step_name.as_deref()
    }

    pub fn params(&self) -> &[Binding] {
        &self.params
    }

    pub fn choices(&self) -> &[Choice] {
        &self.choices
    }

    pub fn result(&self) -> Option<&WitnessValue> {
        self.result.as_ref()
    }
}

pub struct AtomicStepBuilder {
    id: AtomicStepId,
    system: String,
    command: String,
    step_name: Option<String>,
    params: Vec<Binding>,
    choices: Vec<Choice>,
    result: Option<WitnessValue>,
}

impl AtomicStepBuilder {
    pub fn step_name(mut self, step_name: impl Into<String>) -> Self {
        self.step_name = Some(step_name.into());
        self
    }

    pub fn param(mut self, binding: Binding) -> Self {
        self.params.push(binding);
        self
    }

    pub fn choice(mut self, choice: Choice) -> Self {
        self.choices.push(choice);
        self
    }

    pub fn result(mut self, result: WitnessValue) -> Self {
        self.result = Some(result);
        self
    }

    pub fn build(self) -> Result<AtomicStep, ValidationError> {
        if self.system.trim().is_empty() {
            return Err(ValidationError::EmptySystemName);
        }
        if self.command.trim().is_empty() {
            return Err(ValidationError::EmptyCommandName);
        }

        Ok(AtomicStep {
            id: self.id,
            system: self.system,
            command: self.command,
            step_name: self.step_name,
            params: self.params,
            choices: self.choices,
            result: self.result,
        })
    }
}

/// Explicit relation among atomic steps in a single transition.
///
/// Mirrors the surface composition operators:
/// - `Ordered` ↔ `->` (sequence within a single transition's bundle)
/// - `SameStep` ↔ `&` (must fire in the same step)
/// - `Concurrent` ↔ `||` (interleaving is unconstrained)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum StepRelation {
    /// `before` precedes `after`.
    Ordered {
        before: AtomicStepId,
        after: AtomicStepId,
    },
    /// Both steps fire as part of the same step.
    SameStep {
        first: AtomicStepId,
        second: AtomicStepId,
    },
    /// Steps may be concurrent; no ordering is asserted.
    Concurrent {
        first: AtomicStepId,
        second: AtomicStepId,
    },
}

impl StepRelation {
    pub fn ordered(before: &AtomicStepId, after: &AtomicStepId) -> Self {
        Self::Ordered {
            before: before.clone(),
            after: after.clone(),
        }
    }

    pub fn same_step(first: &AtomicStepId, second: &AtomicStepId) -> Self {
        Self::SameStep {
            first: first.clone(),
            second: second.clone(),
        }
    }

    pub fn concurrent(first: &AtomicStepId, second: &AtomicStepId) -> Self {
        Self::Concurrent {
            first: first.clone(),
            second: second.clone(),
        }
    }

    fn ids(&self) -> [&AtomicStepId; 2] {
        match self {
            Self::Ordered { before, after } => [before, after],
            Self::SameStep { first, second } => [first, second],
            Self::Concurrent { first, second } => [first, second],
        }
    }
}

/// Additional witness facts attached to a transition rather than modeled state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionObservation {
    name: String,
    value: WitnessValue,
}

impl TransitionObservation {
    pub fn new(name: impl Into<String>, value: WitnessValue) -> Result<Self, ValidationError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(ValidationError::EmptyObservationName);
        }
        Ok(Self { name, value })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn value(&self) -> &WitnessValue {
        &self.value
    }
}

/// A transition between adjacent states in an operational witness behavior.
///
/// The transition itself does not store source/target indices. In a valid
/// behavior, `transitions[i]` connects `states[i]` to `states[i + 1]`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transition {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    atomic_steps: Vec<AtomicStep>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    relations: Vec<StepRelation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    observations: Vec<TransitionObservation>,
}

impl Transition {
    pub fn builder() -> TransitionBuilder {
        TransitionBuilder {
            atomic_steps: Vec::new(),
            relations: Vec::new(),
            observations: Vec::new(),
        }
    }

    pub fn atomic_steps(&self) -> &[AtomicStep] {
        &self.atomic_steps
    }

    pub fn relations(&self) -> &[StepRelation] {
        &self.relations
    }

    pub fn observations(&self) -> &[TransitionObservation] {
        &self.observations
    }

    pub fn atomic_step(&self, id: &AtomicStepId) -> Option<&AtomicStep> {
        self.atomic_steps.iter().find(|step| step.id() == id)
    }

    pub fn step_relations<'a>(
        &'a self,
        id: &'a AtomicStepId,
    ) -> impl Iterator<Item = &'a StepRelation> + 'a {
        self.relations
            .iter()
            .filter(move |relation| relation.ids().contains(&id))
    }

    fn validate(&self) -> Result<(), ValidationError> {
        let mut ids = BTreeSet::new();
        for step in &self.atomic_steps {
            if !ids.insert(step.id.clone()) {
                return Err(ValidationError::DuplicateAtomicStepId(step.id.0.clone()));
            }
        }

        for relation in &self.relations {
            for id in relation.ids() {
                if !ids.contains(id) {
                    return Err(ValidationError::UnknownAtomicStepRef(id.0.clone()));
                }
            }
        }

        Ok(())
    }
}

pub struct TransitionBuilder {
    atomic_steps: Vec<AtomicStep>,
    relations: Vec<StepRelation>,
    observations: Vec<TransitionObservation>,
}

impl TransitionBuilder {
    pub fn atomic_step(mut self, step: AtomicStep) -> Self {
        self.atomic_steps.push(step);
        self
    }

    pub fn relation(mut self, relation: StepRelation) -> Self {
        self.relations.push(relation);
        self
    }

    pub fn observation(mut self, observation: TransitionObservation) -> Self {
        self.observations.push(observation);
        self
    }

    pub fn build(self) -> Result<Transition, ValidationError> {
        let transition = Transition {
            atomic_steps: self.atomic_steps,
            relations: self.relations,
            observations: self.observations,
        };
        transition.validate()?;
        Ok(transition)
    }
}

/// Native operational witness behavior.
///
/// Top-level behaviors stay linear or lasso-shaped. Non-linearity lives inside
/// transitions via their atomic-step relation metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Behavior {
    states: Vec<State>,
    transitions: Vec<Transition>,
}

impl Behavior {
    pub fn builder() -> BehaviorBuilder {
        BehaviorBuilder {
            states: Vec::new(),
            transitions: Vec::new(),
        }
    }

    pub fn from_parts(
        states: Vec<State>,
        transitions: Vec<Transition>,
    ) -> Result<Self, ValidationError> {
        let behavior = Self {
            states,
            transitions,
        };
        behavior.validate()?;
        Ok(behavior)
    }

    pub fn states(&self) -> &[State] {
        &self.states
    }

    pub fn transitions(&self) -> &[Transition] {
        &self.transitions
    }

    pub fn state(&self, index: usize) -> Option<&State> {
        self.states.get(index)
    }

    pub fn transition(&self, index: usize) -> Option<&Transition> {
        self.transitions.get(index)
    }

    pub fn transition_after_state(&self, state_index: usize) -> Option<&Transition> {
        self.transitions.get(state_index)
    }

    /// Returns true when transitions connect adjacent states linearly.
    pub fn is_linear_topology(&self) -> bool {
        self.transitions.len() + 1 == self.states.len()
            || self.states.is_empty() && self.transitions.is_empty()
    }

    /// Re-checks witness invariants on an already constructed behavior.
    ///
    /// Normal in-process creation should prefer the checked constructors and
    /// builders. `validate()` exists for boundary situations such as
    /// deserialization, import, and defensive integration checks.
    pub fn validate(&self) -> Result<(), ValidationError> {
        if self.states.is_empty() {
            if self.transitions.is_empty() {
                return Ok(());
            }
            return Err(ValidationError::TransitionsWithoutStates);
        }

        if self.transitions.len() + 1 != self.states.len() {
            return Err(ValidationError::TransitionCount {
                states: self.states.len(),
                transitions: self.transitions.len(),
            });
        }

        for transition in &self.transitions {
            transition.validate()?;
        }

        Ok(())
    }
}

pub struct BehaviorBuilder {
    states: Vec<State>,
    transitions: Vec<Transition>,
}

impl BehaviorBuilder {
    pub fn state(mut self, state: State) -> Self {
        self.states.push(state);
        self
    }

    pub fn transition(mut self, transition: Transition) -> Self {
        self.transitions.push(transition);
        self
    }

    pub fn build(self) -> Result<Behavior, ValidationError> {
        Behavior::from_parts(self.states, self.transitions)
    }
}

/// Concrete deadlock witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeadlockWitness {
    behavior: Behavior,
}

impl DeadlockWitness {
    pub fn new(behavior: Behavior) -> Result<Self, ValidationError> {
        behavior.validate()?;
        if behavior.states.is_empty() {
            return Err(ValidationError::EmptyBehavior);
        }
        Ok(Self { behavior })
    }

    pub fn behavior(&self) -> &Behavior {
        &self.behavior
    }

    pub fn deadlocked_at(&self) -> usize {
        self.behavior.states.len() - 1
    }
}

/// Concrete lasso witness for liveness failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LassoWitness {
    behavior: Behavior,
    loop_start: usize,
}

impl LassoWitness {
    pub fn new(behavior: Behavior, loop_start: usize) -> Result<Self, ValidationError> {
        behavior.validate()?;
        if loop_start >= behavior.states.len() {
            return Err(ValidationError::LoopStart {
                loop_start,
                states: behavior.states.len(),
            });
        }
        Ok(Self {
            behavior,
            loop_start,
        })
    }

    pub fn behavior(&self) -> &Behavior {
        &self.behavior
    }

    pub fn loop_start(&self) -> usize {
        self.loop_start
    }
}

/// First-class operational witness object produced by verification.
///
/// Variant selection encodes the kind of failure (or scene success)
/// being represented:
/// - `Counterexample` — a finite trace that violates a safety property.
/// - `Deadlock` — same trace ending in a state with no enabled steps.
/// - `Liveness` — a lasso (finite stem + cycle) witnessing a liveness
///   counterexample (the loop revisits `loop_start` indefinitely).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum OperationalWitness {
    /// Safety counterexample.
    Counterexample { behavior: Behavior },
    /// Deadlock witness — terminal state with no enabled steps.
    Deadlock { witness: DeadlockWitness },
    /// Liveness counterexample (lasso).
    Liveness { witness: LassoWitness },
}

impl OperationalWitness {
    pub fn counterexample(behavior: Behavior) -> Result<Self, ValidationError> {
        behavior.validate()?;
        Ok(Self::Counterexample { behavior })
    }

    pub fn deadlock(behavior: Behavior) -> Result<Self, ValidationError> {
        Ok(Self::Deadlock {
            witness: DeadlockWitness::new(behavior)?,
        })
    }

    pub fn liveness(behavior: Behavior, loop_start: usize) -> Result<Self, ValidationError> {
        Ok(Self::Liveness {
            witness: LassoWitness::new(behavior, loop_start)?,
        })
    }

    pub fn behavior(&self) -> &Behavior {
        match self {
            Self::Counterexample { behavior } => behavior,
            Self::Deadlock { witness } => witness.behavior(),
            Self::Liveness { witness } => witness.behavior(),
        }
    }

    /// Re-checks witness invariants on an already constructed witness.
    ///
    /// Normal in-process creation should prefer the checked constructors and
    /// builders. `validate()` exists for boundary situations such as
    /// deserialization, import, and defensive integration checks.
    pub fn validate(&self) -> Result<(), ValidationError> {
        match self {
            Self::Counterexample { behavior } => behavior.validate(),
            Self::Deadlock { witness } => witness.behavior.validate(),
            Self::Liveness { witness } => witness.behavior.validate().and({
                if witness.loop_start >= witness.behavior.states.len() {
                    Err(ValidationError::LoopStart {
                        loop_start: witness.loop_start,
                        states: witness.behavior.states.len(),
                    })
                } else {
                    Ok(())
                }
            }),
        }
    }
}

/// Optional provenance for an operational witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessOrigin {
    backend: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_span: Option<Span>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_file: Option<String>,
}

impl WitnessOrigin {
    pub fn new(backend: impl Into<String>) -> Result<Self, ValidationError> {
        let backend = backend.into();
        if backend.trim().is_empty() {
            return Err(ValidationError::EmptyBackendName);
        }
        Ok(Self {
            backend,
            source_span: None,
            source_file: None,
        })
    }

    pub fn with_source_span(mut self, source_span: Span) -> Self {
        self.source_span = Some(source_span);
        self
    }

    pub fn with_source_file(mut self, source_file: impl Into<String>) -> Self {
        self.source_file = Some(source_file.into());
        self
    }

    pub fn backend(&self) -> &str {
        &self.backend
    }
}

/// Errors produced when constructing or validating an operational
/// witness.
///
/// Most variants check shape invariants enforced by the builders;
/// `TransitionCount` and `LoopStart` are the two structural mismatches
/// that can only be caught after the full payload is in hand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    /// Witness has no states at all where one was required.
    EmptyBehavior,
    /// Transitions were supplied but no states.
    TransitionsWithoutStates,
    /// `states.len() - 1 != transitions.len()`.
    TransitionCount { states: usize, transitions: usize },
    /// `AtomicStepId` constructor saw an empty string.
    EmptyAtomicStepId,
    /// `AtomicStepBuilder` left the system name empty.
    EmptySystemName,
    /// `AtomicStepBuilder` left the command name empty.
    EmptyCommandName,
    /// A [`Binding`] was constructed with an empty name.
    EmptyBindingName,
    /// A [`TransitionObservation`] was constructed with an empty name.
    EmptyObservationName,
    /// [`WitnessOrigin::new`] received an empty backend label.
    EmptyBackendName,
    /// Two atomic steps in the same transition share an id.
    DuplicateAtomicStepId(String),
    /// A [`StepRelation`] referenced an unknown atomic step id.
    UnknownAtomicStepRef(String),
    /// Liveness `loop_start` index points past the end of the states.
    LoopStart { loop_start: usize, states: usize },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBehavior => write!(f, "operational witness behavior must contain at least one state"),
            Self::TransitionsWithoutStates => {
                write!(f, "operational witness has transitions but no states")
            }
            Self::TransitionCount {
                states,
                transitions,
            } => write!(
                f,
                "operational witness topology mismatch: {states} states require {} transitions, found {transitions}",
                states.saturating_sub(1)
            ),
            Self::EmptyAtomicStepId => write!(f, "atomic step id must not be empty"),
            Self::EmptySystemName => write!(f, "atomic step system name must not be empty"),
            Self::EmptyCommandName => write!(f, "atomic step command name must not be empty"),
            Self::EmptyBindingName => write!(f, "binding name must not be empty"),
            Self::EmptyObservationName => write!(f, "transition observation name must not be empty"),
            Self::EmptyBackendName => write!(f, "witness origin backend name must not be empty"),
            Self::DuplicateAtomicStepId(id) => {
                write!(f, "transition reuses atomic step id `{id}`")
            }
            Self::UnknownAtomicStepRef(id) => {
                write!(f, "transition relation references unknown atomic step `{id}`")
            }
            Self::LoopStart { loop_start, states } => write!(
                f,
                "liveness witness loop start {loop_start} is out of bounds for {states} states"
            ),
        }
    }
}

impl std::error::Error for ValidationError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_behavior() -> Behavior {
        let step_a = AtomicStep::builder(
            AtomicStepId::new("billing_charge").expect("valid id"),
            "Billing",
            "charge",
        )
        .step_name("charge_card")
        .param(
            Binding::new("amount", WitnessValue::Int(42))
                .expect("valid binding")
                .with_ty_hint("int"),
        )
        .choice(Choice::Choose {
            binder: "o".to_owned(),
            selected: EntitySlotRef::new("Order", 1),
        })
        .result(WitnessValue::Bool(true))
        .build()
        .expect("valid step");

        let step_b = AtomicStep::builder(
            AtomicStepId::new("mail_send").expect("valid id"),
            "Mail",
            "send",
        )
        .build()
        .expect("valid step");

        let relation = StepRelation::concurrent(step_a.id(), step_b.id());

        let transition = Transition::builder()
            .atomic_step(step_a)
            .atomic_step(step_b)
            .relation(relation)
            .observation(
                TransitionObservation::new("result", WitnessValue::Bool(true))
                    .expect("valid observation"),
            )
            .build()
            .expect("valid transition");

        Behavior::builder()
            .state(
                State::builder()
                    .entity_slot(
                        EntitySlotRef::new("Order", 1),
                        EntityState::builder(true)
                            .field(
                                "status",
                                WitnessValue::EnumVariant {
                                    enum_name: "OrderStatus".to_owned(),
                                    variant: "Pending".to_owned(),
                                    fields: BTreeMap::new(),
                                },
                            )
                            .build(),
                    )
                    .system_field("Billing", "mode", WitnessValue::String("live".to_owned()))
                    .build(),
            )
            .state(
                State::builder()
                    .entity_slot(
                        EntitySlotRef::new("Order", 1),
                        EntityState::builder(true)
                            .field(
                                "status",
                                WitnessValue::EnumVariant {
                                    enum_name: "OrderStatus".to_owned(),
                                    variant: "Charged".to_owned(),
                                    fields: BTreeMap::new(),
                                },
                            )
                            .build(),
                    )
                    .system_field("Billing", "mode", WitnessValue::String("live".to_owned()))
                    .build(),
            )
            .transition(transition)
            .build()
            .expect("valid behavior")
    }

    #[test]
    fn counterexample_round_trips_shape() {
        let witness = OperationalWitness::counterexample(sample_behavior()).expect("valid witness");

        let json = serde_json::to_string(&witness).expect("serialize witness");
        let decoded: OperationalWitness = serde_json::from_str(&json).expect("deserialize witness");
        assert_eq!(decoded, witness);
        assert_eq!(decoded.validate(), Ok(()));
        assert!(decoded.behavior().transition_after_state(0).is_some());
    }

    #[test]
    fn enum_variant_payload_round_trips_json() {
        let json = serde_json::json!({
            "kind": "enum_variant",
            "value": {
                "enum_name": "Decision",
                "variant": "Accept",
                "fields": {
                    "allowed": {
                        "kind": "bool",
                        "value": false
                    }
                }
            }
        });

        let decoded: WitnessValue =
            serde_json::from_value(json).expect("payload enum witness should deserialize");
        let encoded = serde_json::to_value(decoded).expect("payload enum witness should serialize");

        assert_eq!(
            encoded
                .pointer("/value/fields/allowed/kind")
                .and_then(serde_json::Value::as_str),
            Some("bool")
        );
        assert_eq!(
            encoded
                .pointer("/value/fields/allowed/value")
                .and_then(serde_json::Value::as_bool),
            Some(false)
        );
    }

    #[test]
    fn linear_topology_accepts_adjacent_states() {
        let behavior = Behavior::builder()
            .state(State::builder().build())
            .state(State::builder().build())
            .state(State::builder().build())
            .transition(Transition::builder().build().expect("valid transition"))
            .transition(Transition::builder().build().expect("valid transition"))
            .build()
            .expect("valid behavior");

        assert!(behavior.is_linear_topology());
        assert_eq!(behavior.validate(), Ok(()));
    }

    #[test]
    fn rejects_missing_transition_for_state_pair() {
        let err = Behavior::builder()
            .state(State::builder().build())
            .state(State::builder().build())
            .build()
            .expect_err("should reject missing transition");

        assert_eq!(
            err,
            ValidationError::TransitionCount {
                states: 2,
                transitions: 0,
            }
        );
    }

    #[test]
    fn transition_rejects_unknown_step_relation_refs() {
        let step = AtomicStep::builder(AtomicStepId::new("a").expect("valid id"), "S", "c")
            .build()
            .expect("valid step");
        let missing = AtomicStepId::new("missing").expect("valid id");

        let err = Transition::builder()
            .atomic_step(step.clone())
            .relation(StepRelation::ordered(step.id(), &missing))
            .build()
            .expect_err("should reject unknown relation refs");

        assert_eq!(
            err,
            ValidationError::UnknownAtomicStepRef("missing".to_owned())
        );
    }

    #[test]
    fn transition_lookup_finds_step_and_relations() {
        let step_id = AtomicStepId::new("a").expect("valid id");
        let step = AtomicStep::builder(step_id.clone(), "S", "c")
            .build()
            .expect("valid step");
        let transition = Transition::builder()
            .atomic_step(step)
            .relation(StepRelation::same_step(&step_id, &step_id))
            .build()
            .expect("valid transition");

        assert!(transition.atomic_step(&step_id).is_some());
        assert_eq!(transition.step_relations(&step_id).count(), 1);
    }

    #[test]
    fn checked_constructors_reject_empty_names() {
        assert_eq!(
            Binding::new("   ", WitnessValue::Bool(true)),
            Err(ValidationError::EmptyBindingName)
        );
        assert_eq!(
            AtomicStepId::new(" "),
            Err(ValidationError::EmptyAtomicStepId)
        );
        assert_eq!(
            TransitionObservation::new("", WitnessValue::Bool(true)),
            Err(ValidationError::EmptyObservationName)
        );
        assert_eq!(
            WitnessOrigin::new(" "),
            Err(ValidationError::EmptyBackendName)
        );
    }

    #[test]
    fn atomic_step_builder_rejects_empty_system_or_command() {
        let id = AtomicStepId::new("s").expect("valid id");
        assert_eq!(
            AtomicStep::builder(id.clone(), "", "cmd").build(),
            Err(ValidationError::EmptySystemName)
        );
        assert_eq!(
            AtomicStep::builder(id, "Sys", " ").build(),
            Err(ValidationError::EmptyCommandName)
        );
    }

    #[test]
    fn deadlock_and_liveness_constructors_check_bounds() {
        let empty = Behavior::builder()
            .build()
            .expect("empty behavior is valid");
        assert_eq!(
            DeadlockWitness::new(empty),
            Err(ValidationError::EmptyBehavior)
        );

        let behavior = Behavior::builder()
            .state(State::builder().build())
            .state(State::builder().build())
            .transition(Transition::builder().build().expect("valid transition"))
            .build()
            .expect("valid behavior");

        let deadlock = DeadlockWitness::new(behavior.clone()).expect("deadlock witness");
        assert_eq!(deadlock.deadlocked_at(), 1);

        assert_eq!(
            LassoWitness::new(behavior, 2),
            Err(ValidationError::LoopStart {
                loop_start: 2,
                states: 2,
            })
        );
    }

    #[test]
    fn builders_and_getters_preserve_state_shape() {
        let slot = EntitySlotRef::new("Order", 3);
        let entity = EntityState::builder(true)
            .field(
                "status",
                WitnessValue::EnumVariant {
                    enum_name: "OrderStatus".to_owned(),
                    variant: "pending".to_owned(),
                    fields: BTreeMap::new(),
                },
            )
            .build();
        let state = State::builder()
            .entity_slot(slot.clone(), entity)
            .system_field("Billing", "enabled", WitnessValue::Bool(true))
            .build();

        assert_eq!(slot.entity(), "Order");
        assert_eq!(slot.slot(), 3);
        assert!(state
            .entity_slots()
            .get(&slot)
            .expect("entity state")
            .active());
        assert_eq!(
            state
                .entity_slots()
                .get(&slot)
                .expect("entity state")
                .fields()
                .get("status"),
            Some(&WitnessValue::EnumVariant {
                enum_name: "OrderStatus".to_owned(),
                variant: "pending".to_owned(),
                fields: BTreeMap::new(),
            })
        );
        assert_eq!(
            state
                .system_fields()
                .get("Billing")
                .and_then(|fields| fields.get("enabled")),
            Some(&WitnessValue::Bool(true))
        );
    }

    #[test]
    fn entity_state_getters_preserve_inactive_slots() {
        let entity = EntityState::builder(false).build();

        assert!(!entity.active());
        assert!(entity.fields().is_empty());
    }

    #[test]
    fn binding_and_atomic_step_getters_work() {
        let binding = Binding::new("amount", WitnessValue::Int(7))
            .expect("valid binding")
            .with_ty_hint("int");
        assert_eq!(binding.name(), "amount");
        assert_eq!(binding.value(), &WitnessValue::Int(7));
        assert_eq!(binding.ty_hint(), Some("int"));

        let step_id = AtomicStepId::new("charge").expect("valid id");
        let step = AtomicStep::builder(step_id.clone(), "Billing", "charge")
            .step_name("charge_card")
            .param(binding)
            .choice(Choice::Create {
                created: EntitySlotRef::new("Payment", 0),
            })
            .result(WitnessValue::Bool(true))
            .build()
            .expect("valid step");

        assert_eq!(step.id(), &step_id);
        assert_eq!(step.id().as_str(), "charge");
        assert_eq!(step.system(), "Billing");
        assert_eq!(step.command(), "charge");
        assert_eq!(step.step_name(), Some("charge_card"));
        assert_eq!(step.params().len(), 1);
        assert_eq!(step.choices().len(), 1);
        assert_eq!(step.result(), Some(&WitnessValue::Bool(true)));
    }

    #[test]
    fn witness_origin_and_observation_getters_work() {
        let origin = WitnessOrigin::new("z3")
            .expect("valid origin")
            .with_source_file("spec.ab");
        assert_eq!(origin.backend(), "z3");

        let obs = TransitionObservation::new("enabled", WitnessValue::Bool(false))
            .expect("valid observation");
        assert_eq!(obs.name(), "enabled");
        assert_eq!(obs.value(), &WitnessValue::Bool(false));
    }

    #[test]
    fn witness_constructors_cover_deadlock_and_liveness() {
        let behavior = sample_behavior();
        let deadlock = OperationalWitness::deadlock(behavior.clone()).expect("deadlock witness");
        let liveness = OperationalWitness::liveness(behavior.clone(), 0).expect("liveness witness");

        assert!(matches!(deadlock, OperationalWitness::Deadlock { .. }));
        assert!(matches!(liveness, OperationalWitness::Liveness { .. }));
        assert_eq!(deadlock.behavior().states().len(), 2);
        assert_eq!(liveness.behavior().transitions().len(), 1);
    }

    #[test]
    fn deadlock_and_liveness_accessors_return_actual_indices() {
        let behavior = Behavior::builder()
            .state(State::builder().build())
            .state(State::builder().build())
            .state(State::builder().build())
            .transition(Transition::builder().build().expect("valid transition"))
            .transition(Transition::builder().build().expect("valid transition"))
            .build()
            .expect("valid behavior");

        let deadlock = DeadlockWitness::new(behavior.clone()).expect("deadlock witness");
        let liveness = LassoWitness::new(behavior, 2).expect("valid liveness witness");

        assert_eq!(deadlock.deadlocked_at(), 2);
        assert_eq!(liveness.loop_start(), 2);
    }

    #[test]
    fn transition_and_behavior_accessors_work() {
        let behavior = sample_behavior();
        let transition = behavior.transition(0).expect("transition");

        assert_eq!(behavior.states().len(), 2);
        assert_eq!(behavior.transitions().len(), 1);
        assert!(behavior.state(1).is_some());
        assert_eq!(transition.atomic_steps().len(), 2);
        assert_eq!(transition.relations().len(), 1);
        assert_eq!(transition.observations().len(), 1);

        let ordered = StepRelation::ordered(
            &AtomicStepId::new("a").expect("valid id"),
            &AtomicStepId::new("b").expect("valid id"),
        );
        let concurrent = StepRelation::concurrent(
            &AtomicStepId::new("c").expect("valid id"),
            &AtomicStepId::new("d").expect("valid id"),
        );

        assert!(matches!(ordered, StepRelation::Ordered { .. }));
        assert!(matches!(concurrent, StepRelation::Concurrent { .. }));
    }

    #[test]
    fn behavior_accessors_and_topology_report_absent_or_invalid_shapes() {
        let behavior = Behavior {
            states: vec![State::builder().build(), State::builder().build()],
            transitions: vec![],
        };

        assert!(behavior.state(2).is_none());
        assert!(!behavior.is_linear_topology());
    }

    #[test]
    fn operational_witness_validate_rejects_invalid_liveness_payload() {
        let witness = OperationalWitness::Liveness {
            witness: LassoWitness {
                behavior: Behavior {
                    states: vec![State::builder().build()],
                    transitions: vec![],
                },
                loop_start: 1,
            },
        };

        assert_eq!(
            witness.validate(),
            Err(ValidationError::LoopStart {
                loop_start: 1,
                states: 1,
            })
        );
    }

    #[test]
    fn validation_error_display_includes_context() {
        assert_eq!(
            ValidationError::TransitionCount {
                states: 3,
                transitions: 1,
            }
            .to_string(),
            "operational witness topology mismatch: 3 states require 2 transitions, found 1"
        );
        assert_eq!(
            ValidationError::UnknownAtomicStepRef("missing".to_owned()).to_string(),
            "transition relation references unknown atomic step `missing`"
        );
    }
}
