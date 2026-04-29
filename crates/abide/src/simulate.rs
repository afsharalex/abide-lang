use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::ir::types::{
    IRAction, IRActionMatchScrutinee, IRCreateField, IREntity, IRExpr, IRField, IRFunction,
    IRMatchArm, IRPattern, IRProgram, IRSystem, IRSystemAction, IRTransition, IRType, IRVariant,
    LitVal,
};
use crate::witness::op::{
    self, AtomicStepId, Behavior, Binding, Choice, EntitySlotRef, EntityState,
    TransitionObservation, WitnessValue,
};

#[derive(Clone, Debug)]
pub struct SimulateConfig {
    pub steps: usize,
    pub seed: u64,
    pub slots_per_entity: usize,
    pub entity_slot_overrides: BTreeMap<String, usize>,
    pub system: Option<String>,
}

impl Default for SimulateConfig {
    fn default() -> Self {
        Self {
            steps: 25,
            seed: 0,
            slots_per_entity: 4,
            entity_slot_overrides: BTreeMap::new(),
            system: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum SimulationTermination {
    StepLimit,
    Deadlock { reasons: Vec<String> },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SimulationResult {
    pub systems: Vec<String>,
    pub seed: u64,
    pub steps_requested: usize,
    pub steps_executed: usize,
    pub termination: SimulationTermination,
    pub behavior: Behavior,
}

impl SimulationResult {
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        out.push_str("Simulation\n");
        out.push_str(&format!("systems: {}\n", self.systems.join(", ")));
        out.push_str(&format!("seed: {}\n", self.seed));
        out.push_str(&format!(
            "steps: {}/{}\n",
            self.steps_executed, self.steps_requested
        ));
        match &self.termination {
            SimulationTermination::StepLimit => out.push_str("termination: step limit reached\n"),
            SimulationTermination::Deadlock { reasons } => {
                out.push_str("termination: deadlock\n");
                for reason in reasons {
                    out.push_str(&format!("  - {reason}\n"));
                }
            }
        }

        for (index, state) in self.behavior.states().iter().enumerate() {
            out.push('\n');
            out.push_str(&format!("state {index}\n"));
            for (slot_ref, entity_state) in state.entity_slots() {
                if !entity_state.active() {
                    continue;
                }
                out.push_str(&format!("  {}[{}]\n", slot_ref.entity(), slot_ref.slot()));
                for (field, value) in entity_state.fields() {
                    out.push_str(&format!("    {field} = {}\n", render_value(value)));
                }
            }
            for (system, fields) in state.system_fields() {
                out.push_str(&format!("  System::{system}\n"));
                for (field, value) in fields {
                    out.push_str(&format!("    {field} = {}\n", render_value(value)));
                }
            }

            if let Some(transition) = self.behavior.transition_after_state(index) {
                out.push_str("  ->\n");
                for atomic in transition.atomic_steps() {
                    out.push_str(&format!("    {}::{}", atomic.system(), atomic.command()));
                    if atomic.params().is_empty() {
                        out.push_str("()");
                    } else {
                        let params = atomic
                            .params()
                            .iter()
                            .map(|binding| {
                                format!("{}={}", binding.name(), render_value(binding.value()))
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        out.push_str(&format!("({params})"));
                    }
                    if let Some(step_name) = atomic.step_name() {
                        out.push_str(&format!(" [{step_name}]"));
                    }
                    out.push('\n');
                    for choice in atomic.choices() {
                        match choice {
                            Choice::Choose { binder, selected } => {
                                out.push_str(&format!(
                                    "      choose {binder} = {}[{}]\n",
                                    selected.entity(),
                                    selected.slot()
                                ));
                            }
                            Choice::ForAll { binder, iterated } => {
                                let items = iterated
                                    .iter()
                                    .map(|slot| format!("{}[{}]", slot.entity(), slot.slot()))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                out.push_str(&format!("      forall {binder} in [{items}]\n"));
                            }
                            Choice::Create { created } => {
                                out.push_str(&format!(
                                    "      create {}[{}]\n",
                                    created.entity(),
                                    created.slot()
                                ));
                            }
                        }
                    }
                    if let Some(result) = atomic.result() {
                        out.push_str(&format!("      result = {}\n", render_value(result)));
                    }
                }
                for observation in transition.observations() {
                    out.push_str(&format!(
                        "    observation {} = {}\n",
                        observation.name(),
                        render_value(observation.value())
                    ));
                }
            }
        }

        out
    }
}

pub fn simulate_program(
    program: &IRProgram,
    config: &SimulateConfig,
) -> Result<SimulationResult, String> {
    let selected_systems = select_systems(program, config)?;
    let mut runtime = Runtime::new(program, config.clone(), &selected_systems)?;

    let mut states = vec![runtime.snapshot()];
    let mut transitions = Vec::new();
    let mut executed = 0usize;
    let termination = loop {
        if executed >= config.steps {
            break SimulationTermination::StepLimit;
        }

        let candidates = runtime.command_candidates()?;
        if candidates.is_empty() {
            break SimulationTermination::Deadlock {
                reasons: runtime.deadlock_reasons(),
            };
        }

        let index = runtime.rng.next_index(candidates.len());
        let transition = runtime.execute_candidate(&candidates[index])?;
        transitions.push(transition);
        states.push(runtime.snapshot());
        executed += 1;
    };

    let behavior = op::Behavior::from_parts(states, transitions)
        .map_err(|err| format!("failed to build simulation behavior: {err}"))?;
    Ok(SimulationResult {
        systems: selected_systems
            .iter()
            .map(|system| system.name.clone())
            .collect(),
        seed: config.seed,
        steps_requested: config.steps,
        steps_executed: executed,
        termination,
        behavior,
    })
}

fn select_systems<'a>(
    program: &'a IRProgram,
    config: &SimulateConfig,
) -> Result<Vec<&'a IRSystem>, String> {
    if program.systems.is_empty() {
        return Err("no systems found to simulate".to_owned());
    }
    if let Some(name) = config.system.as_deref() {
        let system = program
            .systems
            .iter()
            .find(|system| system.name == name)
            .ok_or_else(|| format!("unknown system `{name}`"))?;
        return Ok(vec![system]);
    }
    Ok(program.systems.iter().collect())
}

#[derive(Clone, Debug)]
struct LcgRng {
    state: u64,
}

impl LcgRng {
    fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_add(0x9E37_79B9_7F4A_7C15),
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.state
    }

    fn next_index(&mut self, len: usize) -> usize {
        if len <= 1 {
            0
        } else {
            (self.next_u64() as usize) % len
        }
    }
}

#[derive(Clone, Debug)]
struct SlotState {
    active: bool,
    fields: BTreeMap<String, WitnessValue>,
}

#[derive(Clone, Debug, Default)]
struct RuntimeState {
    entity_slots: BTreeMap<String, Vec<SlotState>>,
    system_fields: BTreeMap<String, BTreeMap<String, WitnessValue>>,
}

#[derive(Clone, Debug)]
struct Runtime<'a> {
    program: &'a IRProgram,
    systems: BTreeMap<String, &'a IRSystem>,
    entry_systems: BTreeSet<String>,
    entities: BTreeMap<String, &'a IREntity>,
    functions: BTreeMap<String, &'a IRFunction>,
    state: RuntimeState,
    rng: LcgRng,
    next_identity: usize,
}

#[derive(Clone, Debug)]
struct CommandCandidate {
    system: String,
    step: String,
    params: BTreeMap<String, WitnessValue>,
}

#[derive(Clone, Debug)]
struct AtomicCapture {
    atomic_step: op::AtomicStep,
    observations: Vec<op::TransitionObservation>,
}

impl AtomicCapture {
    fn result(&self) -> Result<&WitnessValue, String> {
        self.atomic_step.result().ok_or_else(|| {
            format!(
                "simulated cross-call `{}`::`{}` did not return a value",
                self.atomic_step.system(),
                self.atomic_step.command()
            )
        })
    }
}

impl<'a> Runtime<'a> {
    fn new(
        program: &'a IRProgram,
        config: SimulateConfig,
        selected_systems: &[&'a IRSystem],
    ) -> Result<Self, String> {
        let mut systems = BTreeMap::new();
        let mut entry_systems = BTreeSet::new();
        for system in selected_systems {
            systems.insert(system.name.clone(), *system);
            entry_systems.insert(system.name.clone());
        }

        for system in selected_systems {
            for step in &system.actions {
                collect_crosscall_systems(program, step, &mut systems)?;
            }
        }

        let entities: BTreeMap<_, _> = program
            .entities
            .iter()
            .map(|entity| (entity.name.clone(), entity))
            .collect();
        let functions: BTreeMap<_, _> = program
            .functions
            .iter()
            .map(|function| (function.name.clone(), function))
            .collect();

        let mut state = RuntimeState::default();
        let mut required_entities = BTreeSet::new();
        for system in systems.values() {
            required_entities.extend(system.entities.iter().cloned());
            let mut fields = BTreeMap::new();
            for field in &system.fields {
                let value = deterministic_field_value(field, None)?;
                fields.insert(field.name.clone(), value);
            }
            state.system_fields.insert(system.name.clone(), fields);
        }

        for entity_name in config.entity_slot_overrides.keys() {
            if !required_entities.contains(entity_name) {
                return Err(format!(
                    "simulation scope override names unknown or unused entity `{entity_name}`"
                ));
            }
        }

        for entity_name in required_entities {
            let entity = entities
                .get(&entity_name)
                .ok_or_else(|| format!("unknown entity `{entity_name}` in system scope"))?;
            let mut slots = Vec::new();
            let slot_count = config
                .entity_slot_overrides
                .get(&entity_name)
                .copied()
                .unwrap_or(config.slots_per_entity);
            for _ in 0..slot_count {
                let mut fields = BTreeMap::new();
                for field in &entity.fields {
                    let value = deterministic_field_value(field, None)?;
                    fields.insert(field.name.clone(), value);
                }
                slots.push(SlotState {
                    active: false,
                    fields,
                });
            }
            state.entity_slots.insert(entity_name, slots);
        }

        Ok(Self {
            program,
            systems,
            entry_systems,
            entities,
            functions,
            state,
            rng: LcgRng::new(config.seed),
            next_identity: 1,
        })
    }

    fn snapshot(&self) -> op::State {
        let mut builder = op::State::builder();
        for (entity, slots) in &self.state.entity_slots {
            for (slot_index, slot) in slots.iter().enumerate() {
                let mut entity_builder = EntityState::builder(slot.active);
                for (field, value) in &slot.fields {
                    entity_builder = entity_builder.field(field.clone(), value.clone());
                }
                builder = builder.entity_slot(
                    EntitySlotRef::new(entity.clone(), slot_index),
                    entity_builder.build(),
                );
            }
        }
        for (system, fields) in &self.state.system_fields {
            for (field, value) in fields {
                builder = builder.system_field(system.clone(), field.clone(), value.clone());
            }
        }
        builder.build()
    }

    fn deadlock_reasons(&self) -> Vec<String> {
        self.entry_systems
            .iter()
            .filter_map(|name| self.systems.get(name))
            .flat_map(|system| {
                system.actions.iter().map(|step| {
                    format!(
                        "{}::{} has no synthesized parameter instance with a true guard",
                        system.name, step.name
                    )
                })
            })
            .collect()
    }

    fn command_candidates(&self) -> Result<Vec<CommandCandidate>, String> {
        let mut out = Vec::new();
        for system in self
            .entry_systems
            .iter()
            .filter_map(|name| self.systems.get(name))
        {
            for step in &system.actions {
                let bindings = self.enumerate_param_bindings(system, step)?;
                for params in bindings {
                    let env = EvalEnv {
                        current_system: &system.name,
                        current_slot: None,
                        locals: params.clone(),
                    };
                    if self.eval_bool(&step.guard, &env)? {
                        let mut probe = self.clone();
                        if probe.execute_step(system, step, &params, false).is_err() {
                            continue;
                        }
                        out.push(CommandCandidate {
                            system: system.name.clone(),
                            step: step.name.clone(),
                            params,
                        });
                    }
                }
            }
        }
        Ok(out)
    }

    fn enumerate_param_bindings(
        &self,
        system: &IRSystem,
        step: &IRSystemAction,
    ) -> Result<Vec<BTreeMap<String, WitnessValue>>, String> {
        if step.params.is_empty() {
            return Ok(vec![BTreeMap::new()]);
        }

        let mut candidates_per_param = Vec::new();
        for param in &step.params {
            let values = self.candidate_values(system, &param.ty);
            if values.is_empty() {
                return Ok(Vec::new());
            }
            candidates_per_param.push((param.name.clone(), values));
        }

        const LIMIT: usize = 128;
        let mut out = Vec::new();
        let mut current = BTreeMap::new();
        enumerate_bindings_recursive(&candidates_per_param, 0, &mut current, &mut out, LIMIT);
        Ok(out)
    }

    fn candidate_values(&self, system: &IRSystem, ty: &IRType) -> Vec<WitnessValue> {
        match ty {
            IRType::Bool => vec![WitnessValue::Bool(false), WitnessValue::Bool(true)],
            IRType::Int => {
                let mut values = vec![-1, 0, 1, 2, 3, 5, 10];
                values.extend(self.ints_in_state());
                values.sort_unstable();
                values.dedup();
                values.into_iter().map(WitnessValue::Int).collect()
            }
            IRType::Real => vec![
                WitnessValue::Real("0".to_owned()),
                WitnessValue::Real("1".to_owned()),
            ],
            IRType::Float => vec![
                WitnessValue::Float("0".to_owned()),
                WitnessValue::Float("1".to_owned()),
            ],
            IRType::String => {
                let mut values = vec![String::new(), "sample".to_owned()];
                values.extend(self.strings_in_state());
                values.sort();
                values.dedup();
                values.into_iter().map(WitnessValue::String).collect()
            }
            IRType::Identity => {
                let mut values = self.identities_in_state();
                values.push(format!("sim-{}", self.next_identity));
                values.sort();
                values.dedup();
                values.into_iter().map(WitnessValue::Identity).collect()
            }
            IRType::Enum { name, variants } => variants
                .iter()
                .filter(|variant| variant.fields.is_empty())
                .map(|variant| WitnessValue::EnumVariant {
                    enum_name: name.clone(),
                    variant: variant.name.clone(),
                })
                .collect(),
            IRType::Entity { name } => self
                .active_slots_for_entity(system, name)
                .into_iter()
                .map(WitnessValue::SlotRef)
                .collect(),
            _ => Vec::new(),
        }
    }

    fn ints_in_state(&self) -> Vec<i64> {
        let mut values = Vec::new();
        for slots in self.state.entity_slots.values() {
            for slot in slots {
                for value in slot.fields.values() {
                    if let WitnessValue::Int(v) = value {
                        values.push(*v);
                    }
                }
            }
        }
        for fields in self.state.system_fields.values() {
            for value in fields.values() {
                if let WitnessValue::Int(v) = value {
                    values.push(*v);
                }
            }
        }
        values
    }

    fn strings_in_state(&self) -> Vec<String> {
        let mut values = Vec::new();
        for slots in self.state.entity_slots.values() {
            for slot in slots {
                for value in slot.fields.values() {
                    match value {
                        WitnessValue::String(v) | WitnessValue::Identity(v) => {
                            values.push(v.clone());
                        }
                        _ => {}
                    }
                }
            }
        }
        values
    }

    fn identities_in_state(&self) -> Vec<String> {
        let mut values = Vec::new();
        for slots in self.state.entity_slots.values() {
            for slot in slots {
                if !slot.active {
                    continue;
                }
                for value in slot.fields.values() {
                    if let WitnessValue::Identity(v) = value {
                        values.push(v.clone());
                    }
                }
            }
        }
        values
    }

    fn active_slots_for_entity(&self, system: &IRSystem, entity_name: &str) -> Vec<EntitySlotRef> {
        if !system.entities.iter().any(|entity| entity == entity_name) {
            return Vec::new();
        }
        self.state
            .entity_slots
            .get(entity_name)
            .into_iter()
            .flat_map(|slots| {
                slots
                    .iter()
                    .enumerate()
                    .filter(|(_, slot)| slot.active)
                    .map(|(index, _)| EntitySlotRef::new(entity_name.to_owned(), index))
            })
            .collect()
    }

    fn execute_candidate(
        &mut self,
        candidate: &CommandCandidate,
    ) -> Result<op::Transition, String> {
        let system = self
            .systems
            .get(&candidate.system)
            .copied()
            .ok_or_else(|| format!("unknown system `{}`", candidate.system))?;
        let step = system
            .actions
            .iter()
            .find(|step| step.name == candidate.step)
            .ok_or_else(|| {
                format!(
                    "unknown step `{}` on system `{}`",
                    candidate.step, system.name
                )
            })?;

        let capture = self.execute_step(system, step, &candidate.params, true)?;
        let mut builder = op::Transition::builder().atomic_step(capture.atomic_step);
        for observation in capture.observations {
            builder = builder.observation(observation);
        }
        builder
            .build()
            .map_err(|err| format!("failed to build simulation transition: {err}"))
    }

    fn execute_step(
        &mut self,
        system: &IRSystem,
        step: &IRSystemAction,
        params: &BTreeMap<String, WitnessValue>,
        top_level: bool,
    ) -> Result<AtomicCapture, String> {
        let mut locals = params.clone();
        let env = Self::eval_env(&system.name, None, &locals);
        if !self.eval_bool(&step.guard, &env)? {
            return Err(format!(
                "step guard became false during execution: {}::{}",
                system.name, step.name
            ));
        }

        let step_id = AtomicStepId::new(format!(
            "{}:{}:{}",
            system.name, step.name, self.next_identity
        ))
        .map_err(|err| format!("invalid atomic step id: {err}"))?;
        let mut atomic_builder =
            op::AtomicStep::builder(step_id, system.name.clone(), step.name.clone())
                .step_name(step.name.clone());
        let mut choices = Vec::new();
        for (name, value) in params {
            let binding = Binding::new(name.clone(), value.clone())
                .map_err(|err| format!("invalid simulation binding: {err}"))?;
            atomic_builder = atomic_builder.param(binding);
        }

        let mut observations = Vec::new();
        for action in &step.body {
            self.execute_action(
                system,
                action,
                &system.name,
                None,
                &mut locals,
                &mut choices,
                &mut observations,
            )?;
        }
        if top_level {
            let observation = TransitionObservation::new(
                "event",
                WitnessValue::String(format!("{}::{}", system.name, step.name)),
            )
            .map_err(|err| format!("invalid simulation observation: {err}"))?;
            observations.push(observation);
        }

        let result = if let Some(expr) = &step.return_expr {
            let env = Self::eval_env(&system.name, None, &locals);
            Some(self.eval_expr(expr, &env)?)
        } else {
            None
        };
        if let Some(result) = result {
            atomic_builder = atomic_builder.result(result);
        }
        for choice in choices {
            atomic_builder = atomic_builder.choice(choice);
        }

        Ok(AtomicCapture {
            atomic_step: atomic_builder
                .build()
                .map_err(|err| format!("failed to build atomic simulation step: {err}"))?,
            observations,
        })
    }

    fn execute_action(
        &mut self,
        system: &IRSystem,
        action: &IRAction,
        current_system: &str,
        current_slot: Option<&EntitySlotRef>,
        locals: &mut BTreeMap<String, WitnessValue>,
        choices: &mut Vec<Choice>,
        observations: &mut Vec<op::TransitionObservation>,
    ) -> Result<(), String> {
        match action {
            IRAction::Choose {
                var,
                entity,
                filter,
                ops,
            } => {
                let candidates = self
                    .active_slots_for_entity(system, entity)
                    .into_iter()
                    .filter(|slot| {
                        let mut local_locals = locals.clone();
                        local_locals.insert(var.clone(), WitnessValue::SlotRef(slot.clone()));
                        let local_env = Self::eval_env(current_system, None, &local_locals);
                        self.eval_bool(filter, &local_env).unwrap_or(false)
                    })
                    .collect::<Vec<_>>();
                if candidates.is_empty() {
                    return Err(format!(
                        "choose `{var}: {entity}` found no active matching slot in {}::{current_system}",
                        system.name
                    ));
                }
                let selected = candidates[self.rng.next_index(candidates.len())].clone();
                choices.push(Choice::Choose {
                    binder: var.clone(),
                    selected: selected.clone(),
                });
                let mut local_locals = locals.clone();
                local_locals.insert(var.clone(), WitnessValue::SlotRef(selected.clone()));
                for op in ops {
                    self.execute_action(
                        system,
                        op,
                        current_system,
                        None,
                        &mut local_locals,
                        choices,
                        observations,
                    )?;
                }
                Ok(())
            }
            IRAction::ForAll { var, entity, ops } => {
                let iterated = self.active_slots_for_entity(system, entity);
                choices.push(Choice::ForAll {
                    binder: var.clone(),
                    iterated: iterated.clone(),
                });
                for slot in iterated {
                    let mut local_locals = locals.clone();
                    local_locals.insert(var.clone(), WitnessValue::SlotRef(slot.clone()));
                    for op in ops {
                        self.execute_action(
                            system,
                            op,
                            current_system,
                            None,
                            &mut local_locals,
                            choices,
                            observations,
                        )?;
                    }
                }
                Ok(())
            }
            IRAction::Create { entity, fields } => {
                let env = Self::eval_env(current_system, current_slot, locals);
                let created = self.create_entity(entity, fields, &env)?;
                choices.push(Choice::Create { created });
                Ok(())
            }
            IRAction::Apply {
                target,
                transition,
                refs,
                args,
            } => {
                let target_value = locals
                    .get(target)
                    .ok_or_else(|| format!("unknown apply target `{target}`"))?;
                let slot = match target_value {
                    WitnessValue::SlotRef(slot) => slot.clone(),
                    other => {
                        return Err(format!(
                            "apply target `{target}` must be an entity slot, found {}",
                            render_value(other)
                        ))
                    }
                };
                let env = Self::eval_env(current_system, current_slot, locals);
                self.apply_entity_transition(&slot, transition, refs, args, &env)
            }
            IRAction::CrossCall {
                system: target_system,
                command,
                args,
            } => {
                let capture = self.execute_cross_call(
                    target_system,
                    command,
                    args,
                    current_system,
                    current_slot,
                    locals,
                )?;
                Self::record_cross_call_observations(
                    target_system,
                    command,
                    &capture,
                    observations,
                )?;
                Ok(())
            }
            IRAction::LetCrossCall {
                name,
                system: target_system,
                command,
                args,
            } => {
                let capture = self.execute_cross_call(
                    target_system,
                    command,
                    args,
                    current_system,
                    current_slot,
                    locals,
                )?;
                Self::record_cross_call_observations(
                    target_system,
                    command,
                    &capture,
                    observations,
                )?;
                locals.insert(name.clone(), capture.result()?.clone());
                Ok(())
            }
            IRAction::Match { scrutinee, arms } => {
                let scrutinee_value = match scrutinee {
                    IRActionMatchScrutinee::Var { name } => locals
                        .get(name)
                        .cloned()
                        .ok_or_else(|| format!("unknown match scrutinee `{name}`"))?,
                    IRActionMatchScrutinee::CrossCall {
                        system: target_system,
                        command,
                        args,
                    } => {
                        let capture = self.execute_cross_call(
                            target_system,
                            command,
                            args,
                            current_system,
                            current_slot,
                            locals,
                        )?;
                        Self::record_cross_call_observations(
                            target_system,
                            command,
                            &capture,
                            observations,
                        )?;
                        capture.result()?.clone()
                    }
                };
                let (locals, body) = self
                    .select_match_arm(
                        &scrutinee_value,
                        arms,
                        &Self::eval_env(current_system, current_slot, locals),
                    )?
                    .ok_or_else(|| "no simulation match arm matched".to_owned())?;
                let mut local_locals = locals;
                for op in body {
                    self.execute_action(
                        system,
                        op,
                        current_system,
                        None,
                        &mut local_locals,
                        choices,
                        observations,
                    )?;
                }
                Ok(())
            }
            IRAction::ExprStmt { expr } => {
                if !self.try_execute_assignment(expr, current_system, current_slot, locals)? {
                    let env = Self::eval_env(current_system, current_slot, locals);
                    let value = self.eval_expr(expr, &env)?;
                    let observation =
                        TransitionObservation::new(format!("expr:{}", expr_kind(expr)), value)
                            .map_err(|err| format!("invalid expr observation: {err}"))?;
                    observations.push(observation);
                }
                Ok(())
            }
        }
    }

    fn execute_cross_call(
        &mut self,
        target_system: &str,
        command: &str,
        args: &[IRExpr],
        current_system: &str,
        current_slot: Option<&EntitySlotRef>,
        locals: &BTreeMap<String, WitnessValue>,
    ) -> Result<AtomicCapture, String> {
        let env = Self::eval_env(current_system, current_slot, locals);
        let params = self.eval_call_args(target_system, command, args, &env)?;
        let target = self
            .systems
            .get(target_system)
            .copied()
            .ok_or_else(|| format!("unknown cross-call system `{target_system}`"))?;
        let step = target
            .actions
            .iter()
            .find(|step| step.name == command)
            .ok_or_else(|| format!("unknown cross-call command `{target_system}::{command}`"))?;
        self.execute_step(target, step, &params, false)
    }

    fn record_cross_call_observations(
        target_system: &str,
        command: &str,
        capture: &AtomicCapture,
        observations: &mut Vec<op::TransitionObservation>,
    ) -> Result<(), String> {
        let summary = TransitionObservation::new(
            format!("cross_call:{target_system}::{command}"),
            WitnessValue::Bool(true),
        )
        .map_err(|err| format!("invalid cross-call observation: {err}"))?;
        observations.push(summary);
        let nested = TransitionObservation::new(
            format!("cross_call_atomic:{target_system}::{command}"),
            WitnessValue::String(format!(
                "{}::{}",
                capture.atomic_step.system(),
                capture.atomic_step.command()
            )),
        )
        .map_err(|err| format!("invalid nested observation: {err}"))?;
        observations.push(nested);
        Ok(())
    }

    fn try_execute_assignment(
        &mut self,
        expr: &IRExpr,
        current_system: &str,
        current_slot: Option<&EntitySlotRef>,
        locals: &BTreeMap<String, WitnessValue>,
    ) -> Result<bool, String> {
        let IRExpr::BinOp {
            op, left, right, ..
        } = expr
        else {
            return Ok(false);
        };
        if op != "OpEq" && op != "==" {
            return Ok(false);
        }
        let Some(target) = self.assignment_target(left, current_system, current_slot, locals)?
        else {
            return Ok(false);
        };
        let env = Self::eval_env(current_system, current_slot, locals);
        let value = self.eval_expr(right, &env)?;
        match target {
            AssignmentTarget::SystemField { system, field } => {
                let fields = self
                    .state
                    .system_fields
                    .get_mut(&system)
                    .ok_or_else(|| format!("missing runtime system scope `{system}`"))?;
                fields.insert(field, value);
            }
            AssignmentTarget::EntityField { slot, field } => {
                let slot_state = self
                    .state
                    .entity_slots
                    .get_mut(slot.entity())
                    .and_then(|slots| slots.get_mut(slot.slot()))
                    .ok_or_else(|| {
                        format!(
                            "missing slot during simulated assignment {}[{}]",
                            slot.entity(),
                            slot.slot()
                        )
                    })?;
                slot_state.fields.insert(field, value);
            }
        }
        Ok(true)
    }

    fn assignment_target(
        &self,
        expr: &IRExpr,
        current_system: &str,
        current_slot: Option<&EntitySlotRef>,
        locals: &BTreeMap<String, WitnessValue>,
    ) -> Result<Option<AssignmentTarget>, String> {
        let IRExpr::Prime { expr, .. } = expr else {
            return Ok(None);
        };
        match expr.as_ref() {
            IRExpr::Var { name, .. } => {
                if let Some(slot) = current_slot {
                    if self.slot_field(slot, name).is_some() {
                        return Ok(Some(AssignmentTarget::EntityField {
                            slot: slot.clone(),
                            field: name.clone(),
                        }));
                    }
                }
                Ok(Some(AssignmentTarget::SystemField {
                    system: current_system.to_owned(),
                    field: name.clone(),
                }))
            }
            IRExpr::Field {
                expr: base, field, ..
            } => {
                let env = Self::eval_env(current_system, current_slot, locals);
                match self.eval_expr(base, &env)? {
                    WitnessValue::SlotRef(slot) => Ok(Some(AssignmentTarget::EntityField {
                        slot,
                        field: field.clone(),
                    })),
                    other => Err(format!(
                        "primed field assignment target must be an entity slot, found {}",
                        render_value(&other)
                    )),
                }
            }
            _ => Ok(None),
        }
    }

    fn create_entity(
        &mut self,
        entity_name: &str,
        fields: &[IRCreateField],
        env: &EvalEnv<'_>,
    ) -> Result<EntitySlotRef, String> {
        let entity = self
            .entities
            .get(entity_name)
            .copied()
            .ok_or_else(|| format!("unknown created entity `{entity_name}`"))?;
        let mut computed = BTreeMap::new();
        for field in &entity.fields {
            let value = deterministic_field_value(field, Some(self.next_identity))?;
            computed.insert(field.name.clone(), value);
        }
        for IRCreateField { name, value } in fields {
            computed.insert(name.clone(), self.eval_expr(value, env)?);
        }
        if let Some(id_value) = computed.get_mut("id") {
            *id_value = WitnessValue::Identity(format!("sim-{}", self.next_identity));
            self.next_identity += 1;
        }
        let slots = self
            .state
            .entity_slots
            .get_mut(entity_name)
            .ok_or_else(|| format!("entity `{entity_name}` is not in simulation scope"))?;
        let slot_index = slots
            .iter()
            .position(|slot| !slot.active)
            .ok_or_else(|| format!("no inactive slot available for `{entity_name}`"))?;
        let slot = slots
            .get_mut(slot_index)
            .ok_or_else(|| format!("missing slot {slot_index} for `{entity_name}`"))?;
        slot.active = true;
        slot.fields = computed;
        Ok(EntitySlotRef::new(entity_name.to_owned(), slot_index))
    }

    fn apply_entity_transition(
        &mut self,
        slot: &EntitySlotRef,
        transition_name: &str,
        refs: &[String],
        args: &[IRExpr],
        env: &EvalEnv<'_>,
    ) -> Result<(), String> {
        let entity = self
            .entities
            .get(slot.entity())
            .copied()
            .ok_or_else(|| format!("unknown entity `{}`", slot.entity()))?;
        let transition = entity
            .transitions
            .iter()
            .find(|transition| transition.name == transition_name)
            .ok_or_else(|| {
                format!(
                    "unknown transition `{transition_name}` on `{}`",
                    slot.entity()
                )
            })?;
        let mut locals = Self::eval_transition_refs(transition, refs, env)?;
        for (name, value) in self.eval_transition_args(transition, args, env)? {
            locals.insert(name, value);
        }
        let local_env = EvalEnv {
            current_system: env.current_system,
            current_slot: Some(slot.clone()),
            locals,
        };
        if !self.eval_bool(&transition.guard, &local_env)? {
            return Err(format!(
                "entity transition guard failed for {}[{}].{}",
                slot.entity(),
                slot.slot(),
                transition_name
            ));
        }

        let new_values = transition
            .updates
            .iter()
            .map(|update| {
                self.eval_expr(&update.value, &local_env)
                    .map(|value| (update.field.clone(), value))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let slot_state = self
            .state
            .entity_slots
            .get_mut(slot.entity())
            .and_then(|slots| slots.get_mut(slot.slot()))
            .ok_or_else(|| format!("missing slot {}[{}]", slot.entity(), slot.slot()))?;
        for (field, value) in new_values {
            slot_state.fields.insert(field, value);
        }
        Ok(())
    }

    fn eval_call_args(
        &self,
        system_name: &str,
        command_name: &str,
        args: &[IRExpr],
        env: &EvalEnv<'_>,
    ) -> Result<BTreeMap<String, WitnessValue>, String> {
        let target = self
            .systems
            .get(system_name)
            .copied()
            .ok_or_else(|| format!("unknown system `{system_name}`"))?;
        let step = target
            .actions
            .iter()
            .find(|step| step.name == command_name)
            .ok_or_else(|| format!("unknown command `{system_name}::{command_name}`"))?;
        self.eval_param_args(&step.params, args, env)
    }

    fn eval_transition_args(
        &self,
        transition: &IRTransition,
        args: &[IRExpr],
        env: &EvalEnv<'_>,
    ) -> Result<BTreeMap<String, WitnessValue>, String> {
        self.eval_param_args(&transition.params, args, env)
    }

    fn eval_transition_refs(
        transition: &IRTransition,
        refs: &[String],
        env: &EvalEnv<'_>,
    ) -> Result<BTreeMap<String, WitnessValue>, String> {
        if transition.refs.len() != refs.len() {
            return Err(format!(
                "transition ref arity mismatch: expected {} refs, found {}",
                transition.refs.len(),
                refs.len()
            ));
        }

        let mut out = BTreeMap::new();
        for (decl, ref_name) in transition.refs.iter().zip(refs) {
            let value = env
                .locals
                .get(ref_name)
                .ok_or_else(|| format!("unknown transition ref `{ref_name}`"))?;
            let slot = match value {
                WitnessValue::SlotRef(slot) => slot.clone(),
                other => {
                    return Err(format!(
                        "transition ref `{ref_name}` must be an entity slot, found {}",
                        render_value(other)
                    ))
                }
            };
            if normalize_type_name(slot.entity()) != normalize_type_name(&decl.entity) {
                return Err(format!(
                    "transition ref `{}` expected entity `{}`, found `{}`",
                    decl.name,
                    decl.entity,
                    slot.entity()
                ));
            }
            out.insert(decl.name.clone(), WitnessValue::SlotRef(slot));
        }
        Ok(out)
    }

    fn eval_param_args(
        &self,
        params: &[crate::ir::types::IRTransParam],
        args: &[IRExpr],
        env: &EvalEnv<'_>,
    ) -> Result<BTreeMap<String, WitnessValue>, String> {
        if params.len() != args.len() {
            return Err(format!(
                "arity mismatch: expected {} args, found {}",
                params.len(),
                args.len()
            ));
        }
        let mut out = BTreeMap::new();
        for (param, arg) in params.iter().zip(args) {
            out.insert(param.name.clone(), self.eval_expr(arg, env)?);
        }
        Ok(out)
    }

    fn eval_bool(&self, expr: &IRExpr, env: &EvalEnv<'_>) -> Result<bool, String> {
        match self.eval_expr(expr, env)? {
            WitnessValue::Bool(value) => Ok(value),
            other => Err(format!("expected bool, found {}", render_value(&other))),
        }
    }

    fn eval_expr(&self, expr: &IRExpr, env: &EvalEnv<'_>) -> Result<WitnessValue, String> {
        match expr {
            IRExpr::Lit { value, .. } => Ok(match value {
                LitVal::Int { value } => WitnessValue::Int(*value),
                LitVal::Real { value } => WitnessValue::Real(normalize_float(*value)),
                LitVal::Float { value } => WitnessValue::Float(normalize_float(*value)),
                LitVal::Bool { value } => WitnessValue::Bool(*value),
                LitVal::Str { value } => WitnessValue::String(value.clone()),
            }),
            IRExpr::Var { name, .. } => {
                if let Some(value) = env.locals.get(name) {
                    return Ok(value.clone());
                }
                if let Some(slot) = &env.current_slot {
                    if let Some(value) = self.slot_field(slot, name) {
                        return Ok(value.clone());
                    }
                }
                if let Some(fields) = self.state.system_fields.get(env.current_system) {
                    if let Some(value) = fields.get(name) {
                        return Ok(value.clone());
                    }
                }
                if let Some(constant) = self
                    .program
                    .constants
                    .iter()
                    .find(|constant| constant.name == *name)
                {
                    return self.eval_expr(&constant.value, env);
                }
                Err(format!("unknown variable `{name}` in simulation"))
            }
            IRExpr::Ctor {
                enum_name,
                ctor,
                args,
                ..
            } => {
                if args.is_empty() {
                    Ok(WitnessValue::EnumVariant {
                        enum_name: enum_name.clone(),
                        variant: ctor.clone(),
                    })
                } else {
                    let mut fields = BTreeMap::new();
                    fields.insert("__ctor".to_owned(), WitnessValue::String(ctor.clone()));
                    fields.insert("__enum".to_owned(), WitnessValue::String(enum_name.clone()));
                    for (field, expr) in args {
                        fields.insert(field.clone(), self.eval_expr(expr, env)?);
                    }
                    Ok(WitnessValue::Record(fields))
                }
            }
            IRExpr::BinOp {
                op, left, right, ..
            } => {
                let left = self.eval_expr(left, env)?;
                let right = self.eval_expr(right, env)?;
                eval_binop(op, &left, &right)
            }
            IRExpr::UnOp { op, operand, .. } => {
                let operand = self.eval_expr(operand, env)?;
                eval_unop(op, &operand)
            }
            IRExpr::Let { bindings, body, .. } => {
                let mut locals = env.locals.clone();
                for binding in bindings {
                    let local_env = EvalEnv {
                        current_system: env.current_system,
                        current_slot: env.current_slot.clone(),
                        locals: locals.clone(),
                    };
                    let value = self.eval_expr(&binding.expr, &local_env)?;
                    locals.insert(binding.name.clone(), value);
                }
                let local_env = EvalEnv {
                    current_system: env.current_system,
                    current_slot: env.current_slot.clone(),
                    locals,
                };
                self.eval_expr(body, &local_env)
            }
            IRExpr::Field { expr, field, .. } => {
                let base = self.eval_expr(expr, env)?;
                match base {
                    WitnessValue::SlotRef(slot) => {
                        self.slot_field(&slot, field).cloned().ok_or_else(|| {
                            format!(
                                "missing field `{field}` on {}[{}]",
                                slot.entity(),
                                slot.slot()
                            )
                        })
                    }
                    WitnessValue::Record(fields) => fields
                        .get(field)
                        .cloned()
                        .ok_or_else(|| format!("missing record field `{field}`")),
                    other => Err(format!(
                        "cannot project field `{field}` from {}",
                        render_value(&other)
                    )),
                }
            }
            IRExpr::Exists {
                var, domain, body, ..
            } => {
                for candidate in self.candidate_values_for_quantifier(domain, env) {
                    let mut locals = env.locals.clone();
                    locals.insert(var.clone(), candidate);
                    let local_env = EvalEnv {
                        current_system: env.current_system,
                        current_slot: env.current_slot.clone(),
                        locals,
                    };
                    if self.eval_bool(body, &local_env)? {
                        return Ok(WitnessValue::Bool(true));
                    }
                }
                Ok(WitnessValue::Bool(false))
            }
            IRExpr::Forall {
                var, domain, body, ..
            } => {
                for candidate in self.candidate_values_for_quantifier(domain, env) {
                    let mut locals = env.locals.clone();
                    locals.insert(var.clone(), candidate);
                    let local_env = EvalEnv {
                        current_system: env.current_system,
                        current_slot: env.current_slot.clone(),
                        locals,
                    };
                    if !self.eval_bool(body, &local_env)? {
                        return Ok(WitnessValue::Bool(false));
                    }
                }
                Ok(WitnessValue::Bool(true))
            }
            IRExpr::One {
                var, domain, body, ..
            } => {
                let mut count = 0usize;
                for candidate in self.candidate_values_for_quantifier(domain, env) {
                    let mut locals = env.locals.clone();
                    locals.insert(var.clone(), candidate);
                    let local_env = EvalEnv {
                        current_system: env.current_system,
                        current_slot: env.current_slot.clone(),
                        locals,
                    };
                    if self.eval_bool(body, &local_env)? {
                        count += 1;
                    }
                }
                Ok(WitnessValue::Bool(count == 1))
            }
            IRExpr::Lone {
                var, domain, body, ..
            } => {
                let mut count = 0usize;
                for candidate in self.candidate_values_for_quantifier(domain, env) {
                    let mut locals = env.locals.clone();
                    locals.insert(var.clone(), candidate);
                    let local_env = EvalEnv {
                        current_system: env.current_system,
                        current_slot: env.current_slot.clone(),
                        locals,
                    };
                    if self.eval_bool(body, &local_env)? {
                        count += 1;
                    }
                }
                Ok(WitnessValue::Bool(count <= 1))
            }
            IRExpr::Match {
                scrutinee, arms, ..
            } => {
                let scrutinee = self.eval_expr(scrutinee, env)?;
                let (locals, body) = self
                    .select_expr_match_arm(&scrutinee, arms, env)?
                    .ok_or_else(|| "non-exhaustive match in simulation".to_owned())?;
                let local_env = EvalEnv {
                    current_system: env.current_system,
                    current_slot: env.current_slot.clone(),
                    locals,
                };
                self.eval_expr(body, &local_env)
            }
            IRExpr::Choose {
                var,
                domain,
                predicate,
                ..
            } => {
                for candidate in self.candidate_values_for_quantifier(domain, env) {
                    if let Some(predicate) = predicate {
                        let mut locals = env.locals.clone();
                        locals.insert(var.clone(), candidate.clone());
                        let local_env = EvalEnv {
                            current_system: env.current_system,
                            current_slot: env.current_slot.clone(),
                            locals,
                        };
                        if !self.eval_bool(predicate, &local_env)? {
                            continue;
                        }
                    }
                    return Ok(candidate);
                }
                Err(format!(
                    "pure choose `{var}: {}` found no matching candidate in simulation",
                    render_type(domain)
                ))
            }
            IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => self.eval_expr(expr, env),
            IRExpr::Lam { .. } => {
                Err("lambda values are not directly executable in simulation".to_owned())
            }
            IRExpr::Block { exprs, .. } => {
                let mut last = WitnessValue::Bool(true);
                let mut locals = env.locals.clone();
                for expr in exprs {
                    let local_env = EvalEnv {
                        current_system: env.current_system,
                        current_slot: env.current_slot.clone(),
                        locals: locals.clone(),
                    };
                    last = self.eval_expr(expr, &local_env)?;
                    if let IRExpr::VarDecl { name, init, .. } = expr {
                        let value = self.eval_expr(init, &local_env)?;
                        locals.insert(name.clone(), value);
                    }
                }
                Ok(last)
            }
            IRExpr::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => {
                if self.eval_bool(cond, env)? {
                    self.eval_expr(then_body, env)
                } else if let Some(else_body) = else_body {
                    self.eval_expr(else_body, env)
                } else {
                    Ok(WitnessValue::Bool(true))
                }
            }
            IRExpr::App { .. } => self.eval_app(expr, env),
            IRExpr::SetLit { elements, .. } => Ok(WitnessValue::Set(
                elements
                    .iter()
                    .map(|element| self.eval_expr(element, env))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            IRExpr::SeqLit { elements, .. } => Ok(WitnessValue::Seq(
                elements
                    .iter()
                    .map(|element| self.eval_expr(element, env))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            IRExpr::MapLit { entries, .. } => Ok(WitnessValue::Map(
                entries
                    .iter()
                    .map(|(key, value)| {
                        Ok((self.eval_expr(key, env)?, self.eval_expr(value, env)?))
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            )),
            IRExpr::MapUpdate {
                map, key, value, ..
            } => {
                let map = self.eval_expr(map, env)?;
                let key = self.eval_expr(key, env)?;
                let value = self.eval_expr(value, env)?;
                match map {
                    WitnessValue::Map(mut entries) => {
                        if let Some(entry) =
                            entries.iter_mut().find(|(existing, _)| existing == &key)
                        {
                            entry.1 = value;
                        } else {
                            entries.push((key, value));
                        }
                        Ok(WitnessValue::Map(entries))
                    }
                    other => Err(format!(
                        "cannot update non-map value {}",
                        render_value(&other)
                    )),
                }
            }
            IRExpr::Index { map, key, .. } => {
                let map = self.eval_expr(map, env)?;
                let key = self.eval_expr(key, env)?;
                match map {
                    WitnessValue::Map(entries) => entries
                        .into_iter()
                        .find(|(existing, _)| *existing == key)
                        .map(|(_, value)| value)
                        .ok_or_else(|| "missing map key during simulation".to_owned()),
                    WitnessValue::Seq(values) => {
                        let index = expect_int(&key)? as usize;
                        values
                            .get(index)
                            .cloned()
                            .ok_or_else(|| format!("sequence index {index} out of bounds"))
                    }
                    other => Err(format!("cannot index value {}", render_value(&other))),
                }
            }
            IRExpr::Card { expr, .. } => {
                let value = self.eval_expr(expr, env)?;
                match value {
                    WitnessValue::Set(values) | WitnessValue::Seq(values) => {
                        Ok(WitnessValue::Int(values.len() as i64))
                    }
                    WitnessValue::Map(entries) => Ok(WitnessValue::Int(entries.len() as i64)),
                    other => Err(format!(
                        "cannot take cardinality of {}",
                        render_value(&other)
                    )),
                }
            }
            IRExpr::VarDecl {
                init, rest, name, ..
            } => {
                let value = self.eval_expr(init, env)?;
                let mut locals = env.locals.clone();
                locals.insert(name.clone(), value);
                let local_env = EvalEnv {
                    current_system: env.current_system,
                    current_slot: env.current_slot.clone(),
                    locals,
                };
                self.eval_expr(rest, &local_env)
            }
            IRExpr::Sorry { .. } | IRExpr::Todo { .. } => {
                Err("cannot simulate sorry/todo expressions".to_owned())
            }
            IRExpr::Prime { .. }
            | IRExpr::Always { .. }
            | IRExpr::Eventually { .. }
            | IRExpr::Until { .. }
            | IRExpr::Historically { .. }
            | IRExpr::Once { .. }
            | IRExpr::Previously { .. }
            | IRExpr::Since { .. }
            | IRExpr::Aggregate { .. }
            | IRExpr::Saw { .. }
            | IRExpr::SetComp { .. }
            | IRExpr::While { .. } => Err(format!(
                "simulation does not yet support expression kind `{}`",
                expr_kind(expr)
            )),
        }
    }

    fn eval_app(&self, expr: &IRExpr, env: &EvalEnv<'_>) -> Result<WitnessValue, String> {
        let (head, args) = flatten_app(expr);
        let IRExpr::Var { name, .. } = head else {
            return Err(
                "simulation only supports simple named function/query applications".to_owned(),
            );
        };

        if let Some(function) = self.functions.get(name) {
            return self.eval_named_callable(function, &args, env);
        }

        if let Some(system) = self.systems.get(env.current_system) {
            if let Some(query) = system.queries.iter().find(|query| query.name == *name) {
                if query.params.len() != args.len() {
                    return Err(format!(
                        "arity mismatch calling query `{name}`: expected {}, found {}",
                        query.params.len(),
                        args.len()
                    ));
                }
                let mut locals = env.locals.clone();
                for (param, arg) in query.params.iter().zip(args) {
                    locals.insert(param.name.clone(), self.eval_expr(arg, env)?);
                }
                let local_env = EvalEnv {
                    current_system: env.current_system,
                    current_slot: env.current_slot.clone(),
                    locals,
                };
                let mut query_locals = local_env.locals.clone();
                return self.eval_exec_expr(
                    &query.body,
                    local_env.current_system,
                    local_env.current_slot.as_ref(),
                    &mut query_locals,
                );
            }
            if let Some(pred) = system.preds.iter().find(|pred| pred.name == *name) {
                return self.eval_named_callable(pred, &args, env);
            }
        }

        Err(format!("unknown callable `{name}` in simulation"))
    }

    fn eval_named_callable(
        &self,
        function: &IRFunction,
        args: &[&IRExpr],
        env: &EvalEnv<'_>,
    ) -> Result<WitnessValue, String> {
        let (params, body) = lam_chain(&function.body);
        if params.len() != args.len() {
            return Err(format!(
                "arity mismatch calling `{}`: expected {}, found {}",
                function.name,
                params.len(),
                args.len()
            ));
        }
        let mut locals = env.locals.clone();
        for ((param_name, _param_ty), arg) in params.iter().zip(args) {
            locals.insert(param_name.clone(), self.eval_expr(arg, env)?);
        }
        let local_env = EvalEnv {
            current_system: env.current_system,
            current_slot: env.current_slot.clone(),
            locals,
        };
        let mut call_locals = local_env.locals.clone();
        self.eval_exec_expr(
            body,
            local_env.current_system,
            local_env.current_slot.as_ref(),
            &mut call_locals,
        )
    }

    fn candidate_values_for_quantifier(
        &self,
        domain: &IRType,
        env: &EvalEnv<'_>,
    ) -> Vec<WitnessValue> {
        let system = self
            .systems
            .get(env.current_system)
            .copied()
            .or_else(|| self.systems.values().next().copied());
        system
            .map(|system| self.candidate_values(system, domain))
            .unwrap_or_default()
    }

    fn select_match_arm<'b>(
        &self,
        scrutinee: &WitnessValue,
        arms: &'b [crate::ir::types::IRActionMatchArm],
        env: &EvalEnv<'_>,
    ) -> Result<Option<(BTreeMap<String, WitnessValue>, &'b [IRAction])>, String> {
        for arm in arms {
            if let Some(bindings) = pattern_bindings(scrutinee, &arm.pattern) {
                let mut locals = env.locals.clone();
                locals.extend(bindings);
                let local_env = EvalEnv {
                    current_system: env.current_system,
                    current_slot: env.current_slot.clone(),
                    locals: locals.clone(),
                };
                if let Some(guard) = &arm.guard {
                    if !self.eval_bool(guard, &local_env)? {
                        continue;
                    }
                }
                return Ok(Some((locals, &arm.body)));
            }
        }
        Ok(None)
    }

    fn select_expr_match_arm<'b>(
        &self,
        scrutinee: &WitnessValue,
        arms: &'b [IRMatchArm],
        env: &EvalEnv<'_>,
    ) -> Result<Option<(BTreeMap<String, WitnessValue>, &'b IRExpr)>, String> {
        for arm in arms {
            if let Some(bindings) = pattern_bindings(scrutinee, &arm.pattern) {
                let mut locals = env.locals.clone();
                locals.extend(bindings);
                let local_env = EvalEnv {
                    current_system: env.current_system,
                    current_slot: env.current_slot.clone(),
                    locals: locals.clone(),
                };
                if let Some(guard) = &arm.guard {
                    if !self.eval_bool(guard, &local_env)? {
                        continue;
                    }
                }
                return Ok(Some((locals, &arm.body)));
            }
        }
        Ok(None)
    }

    fn slot_field<'b>(&'b self, slot: &EntitySlotRef, field: &str) -> Option<&'b WitnessValue> {
        self.state
            .entity_slots
            .get(slot.entity())
            .and_then(|slots| slots.get(slot.slot()))
            .and_then(|slot| slot.fields.get(field))
    }

    fn eval_env<'b>(
        current_system: &'b str,
        current_slot: Option<&EntitySlotRef>,
        locals: &BTreeMap<String, WitnessValue>,
    ) -> EvalEnv<'b> {
        EvalEnv {
            current_system,
            current_slot: current_slot.cloned(),
            locals: locals.clone(),
        }
    }

    fn eval_exec_expr(
        &self,
        expr: &IRExpr,
        current_system: &str,
        current_slot: Option<&EntitySlotRef>,
        locals: &mut BTreeMap<String, WitnessValue>,
    ) -> Result<WitnessValue, String> {
        match expr {
            IRExpr::Block { exprs, .. } => {
                let mut last = WitnessValue::Bool(true);
                for expr in exprs {
                    last = self.eval_exec_stmt(expr, current_system, current_slot, locals)?;
                }
                Ok(last)
            }
            IRExpr::VarDecl {
                name, init, rest, ..
            } => {
                let env = Self::eval_env(current_system, current_slot, locals);
                let value = self.eval_expr(init, &env)?;
                let mut scoped = locals.clone();
                scoped.insert(name.clone(), value);
                self.eval_exec_expr(rest, current_system, current_slot, &mut scoped)
            }
            IRExpr::While {
                cond,
                body,
                span: _,
                ..
            } => {
                const LOOP_LIMIT: usize = 1024;
                for _ in 0..LOOP_LIMIT {
                    let env = Self::eval_env(current_system, current_slot, locals);
                    if !self.eval_bool(cond, &env)? {
                        return Ok(WitnessValue::Bool(true));
                    }
                    self.eval_exec_stmt(body, current_system, current_slot, locals)?;
                }
                Err("simulation loop iteration limit exceeded".to_owned())
            }
            IRExpr::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let env = Self::eval_env(current_system, current_slot, locals);
                if self.eval_bool(cond, &env)? {
                    self.eval_exec_expr(then_body, current_system, current_slot, locals)
                } else if let Some(else_body) = else_body {
                    self.eval_exec_expr(else_body, current_system, current_slot, locals)
                } else {
                    Ok(WitnessValue::Bool(true))
                }
            }
            IRExpr::Match {
                scrutinee, arms, ..
            } => {
                let env = Self::eval_env(current_system, current_slot, locals);
                let scrutinee = self.eval_expr(scrutinee, &env)?;
                let (mut arm_locals, body) = self
                    .select_expr_match_arm(&scrutinee, arms, &env)?
                    .ok_or_else(|| "non-exhaustive match in simulation".to_owned())?;
                self.eval_exec_expr(body, current_system, current_slot, &mut arm_locals)
            }
            IRExpr::Let { bindings, body, .. } => {
                let mut scoped = locals.clone();
                for binding in bindings {
                    let env = Self::eval_env(current_system, current_slot, &scoped);
                    let value = self.eval_expr(&binding.expr, &env)?;
                    scoped.insert(binding.name.clone(), value);
                }
                self.eval_exec_expr(body, current_system, current_slot, &mut scoped)
            }
            _ => {
                let env = Self::eval_env(current_system, current_slot, locals);
                self.eval_expr(expr, &env)
            }
        }
    }

    fn eval_exec_stmt(
        &self,
        expr: &IRExpr,
        current_system: &str,
        current_slot: Option<&EntitySlotRef>,
        locals: &mut BTreeMap<String, WitnessValue>,
    ) -> Result<WitnessValue, String> {
        if let IRExpr::BinOp {
            op, left, right, ..
        } = expr
        {
            if op == "OpEq" {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if locals.contains_key(name) {
                        let value =
                            self.eval_exec_expr(right, current_system, current_slot, locals)?;
                        locals.insert(name.clone(), value);
                        return Ok(WitnessValue::Bool(true));
                    }
                }
            }
        }
        self.eval_exec_expr(expr, current_system, current_slot, locals)
    }
}

#[derive(Clone, Debug)]
struct EvalEnv<'a> {
    current_system: &'a str,
    current_slot: Option<EntitySlotRef>,
    locals: BTreeMap<String, WitnessValue>,
}

#[derive(Clone, Debug)]
enum AssignmentTarget {
    SystemField { system: String, field: String },
    EntityField { slot: EntitySlotRef, field: String },
}

fn enumerate_bindings_recursive(
    params: &[(String, Vec<WitnessValue>)],
    index: usize,
    current: &mut BTreeMap<String, WitnessValue>,
    out: &mut Vec<BTreeMap<String, WitnessValue>>,
    limit: usize,
) {
    if out.len() >= limit {
        return;
    }
    if index == params.len() {
        out.push(current.clone());
        return;
    }
    let (name, values) = &params[index];
    for value in values {
        current.insert(name.clone(), value.clone());
        enumerate_bindings_recursive(params, index + 1, current, out, limit);
        current.remove(name);
        if out.len() >= limit {
            return;
        }
    }
}

fn deterministic_field_value(
    field: &IRField,
    fresh_identity: Option<usize>,
) -> Result<WitnessValue, String> {
    if let Some(default) = &field.default {
        // Only handle literal/ctor defaults here.
        return eval_static_expr(default, fresh_identity);
    }
    zero_value_for_type(&field.ty, fresh_identity)
}

fn eval_static_expr(expr: &IRExpr, fresh_identity: Option<usize>) -> Result<WitnessValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(match value {
            LitVal::Int { value } => WitnessValue::Int(*value),
            LitVal::Real { value } => WitnessValue::Real(normalize_float(*value)),
            LitVal::Float { value } => WitnessValue::Float(normalize_float(*value)),
            LitVal::Bool { value } => WitnessValue::Bool(*value),
            LitVal::Str { value } => WitnessValue::String(value.clone()),
        }),
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            if args.is_empty() {
                Ok(WitnessValue::EnumVariant {
                    enum_name: enum_name.clone(),
                    variant: ctor.clone(),
                })
            } else {
                let mut fields = BTreeMap::new();
                fields.insert("__ctor".to_owned(), WitnessValue::String(ctor.clone()));
                fields.insert("__enum".to_owned(), WitnessValue::String(enum_name.clone()));
                for (field, value) in args {
                    fields.insert(field.clone(), eval_static_expr(value, fresh_identity)?);
                }
                Ok(WitnessValue::Record(fields))
            }
        }
        IRExpr::Var { name, .. } if name == "$" => match fresh_identity {
            Some(index) => Ok(WitnessValue::Identity(format!("sim-{index}"))),
            None => Err("unexpected `$` in static default evaluation".to_owned()),
        },
        _ => Err(format!(
            "simulation default evaluation does not support expression kind `{}`",
            expr_kind(expr)
        )),
    }
}

fn zero_value_for_type(ty: &IRType, fresh_identity: Option<usize>) -> Result<WitnessValue, String> {
    match ty {
        IRType::Int => Ok(WitnessValue::Int(0)),
        IRType::Bool => Ok(WitnessValue::Bool(false)),
        IRType::String => Ok(WitnessValue::String(String::new())),
        IRType::Identity => Ok(WitnessValue::Identity(format!(
            "sim-{}",
            fresh_identity.unwrap_or(0)
        ))),
        IRType::Real => Ok(WitnessValue::Real("0".to_owned())),
        IRType::Float => Ok(WitnessValue::Float("0".to_owned())),
        IRType::Enum { name, variants } => {
            let variant = variants
                .first()
                .ok_or_else(|| format!("enum `{name}` has no variants"))?;
            if variant.fields.is_empty() {
                Ok(WitnessValue::EnumVariant {
                    enum_name: name.clone(),
                    variant: variant.name.clone(),
                })
            } else {
                record_value_for_variant(name, variant, fresh_identity)
            }
        }
        IRType::Set { .. } => Ok(WitnessValue::Set(Vec::new())),
        IRType::Seq { .. } => Ok(WitnessValue::Seq(Vec::new())),
        IRType::Map { .. } => Ok(WitnessValue::Map(Vec::new())),
        IRType::Tuple { elements } => Ok(WitnessValue::Tuple(
            elements
                .iter()
                .map(|element| zero_value_for_type(element, fresh_identity))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        IRType::Record { fields, .. } => {
            let mut out = BTreeMap::new();
            for field in fields {
                out.insert(
                    field.name.clone(),
                    zero_value_for_type(&field.ty, fresh_identity)?,
                );
            }
            Ok(WitnessValue::Record(out))
        }
        IRType::Refinement { base, .. } => zero_value_for_type(base, fresh_identity),
        IRType::Entity { name } => Err(format!(
            "cannot synthesize standalone default entity value for `{name}`"
        )),
        IRType::Fn { .. } => Ok(WitnessValue::Opaque {
            display: "<fn>".to_owned(),
            ty: None,
        }),
    }
}

fn record_value_for_variant(
    enum_name: &str,
    variant: &IRVariant,
    fresh_identity: Option<usize>,
) -> Result<WitnessValue, String> {
    let mut fields = BTreeMap::new();
    fields.insert(
        "__ctor".to_owned(),
        WitnessValue::String(variant.name.clone()),
    );
    fields.insert(
        "__enum".to_owned(),
        WitnessValue::String(enum_name.to_owned()),
    );
    for field in &variant.fields {
        fields.insert(
            field.name.clone(),
            zero_value_for_type(&field.ty, fresh_identity)?,
        );
    }
    Ok(WitnessValue::Record(fields))
}

fn collect_crosscall_systems<'a>(
    program: &'a IRProgram,
    step: &IRSystemAction,
    out: &mut BTreeMap<String, &'a IRSystem>,
) -> Result<(), String> {
    for action in &step.body {
        collect_action_crosscalls(program, action, out)?;
    }
    Ok(())
}

fn collect_action_crosscalls<'a>(
    program: &'a IRProgram,
    action: &IRAction,
    out: &mut BTreeMap<String, &'a IRSystem>,
) -> Result<(), String> {
    match action {
        IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
            for op in ops {
                collect_action_crosscalls(program, op, out)?;
            }
        }
        IRAction::CrossCall { system, .. } | IRAction::LetCrossCall { system, .. } => {
            let target = program
                .systems
                .iter()
                .find(|candidate| candidate.name == *system)
                .ok_or_else(|| format!("unknown cross-call system `{system}`"))?;
            out.entry(system.clone()).or_insert(target);
            for step in &target.actions {
                collect_crosscall_systems(program, step, out)?;
            }
        }
        IRAction::Match { arms, .. } => {
            if let IRAction::Match {
                scrutinee:
                    IRActionMatchScrutinee::CrossCall {
                        system,
                        command: _,
                        args: _,
                    },
                ..
            } = action
            {
                let target = program
                    .systems
                    .iter()
                    .find(|candidate| candidate.name == *system)
                    .ok_or_else(|| format!("unknown cross-call system `{system}`"))?;
                out.entry(system.clone()).or_insert(target);
                for step in &target.actions {
                    collect_crosscall_systems(program, step, out)?;
                }
            }
            for arm in arms {
                for op in &arm.body {
                    collect_action_crosscalls(program, op, out)?;
                }
            }
        }
        IRAction::Create { .. } | IRAction::Apply { .. } | IRAction::ExprStmt { .. } => {}
    }
    Ok(())
}

fn flatten_app(expr: &IRExpr) -> (&IRExpr, Vec<&IRExpr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let IRExpr::App { func, arg, .. } = current {
        args.push(arg.as_ref());
        current = func.as_ref();
    }
    args.reverse();
    (current, args)
}

fn lam_chain(expr: &IRExpr) -> (Vec<(String, IRType)>, &IRExpr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let IRExpr::Lam {
        param,
        param_type,
        body,
        ..
    } = current
    {
        params.push((param.clone(), param_type.clone()));
        current = body.as_ref();
    }
    (params, current)
}

fn pattern_bindings(
    value: &WitnessValue,
    pattern: &IRPattern,
) -> Option<BTreeMap<String, WitnessValue>> {
    match pattern {
        IRPattern::PWild => Some(BTreeMap::new()),
        IRPattern::PVar { name } => {
            let mut bindings = BTreeMap::new();
            bindings.insert(name.clone(), value.clone());
            Some(bindings)
        }
        IRPattern::POr { left, right } => {
            pattern_bindings(value, left).or_else(|| pattern_bindings(value, right))
        }
        IRPattern::PCtor { name, fields } => match value {
            WitnessValue::EnumVariant { variant, .. } if variant == name && fields.is_empty() => {
                Some(BTreeMap::new())
            }
            WitnessValue::Record(record) => {
                let Some(WitnessValue::String(ctor)) = record.get("__ctor") else {
                    return None;
                };
                if ctor != name {
                    return None;
                }
                let mut bindings = BTreeMap::new();
                for field in fields {
                    let field_value = record.get(&field.name)?;
                    let nested = pattern_bindings(field_value, &field.pattern)?;
                    bindings.extend(nested);
                }
                Some(bindings)
            }
            _ => None,
        },
    }
}

fn eval_binop(op: &str, left: &WitnessValue, right: &WitnessValue) -> Result<WitnessValue, String> {
    match op {
        "==" | "OpEq" => Ok(WitnessValue::Bool(witness_values_equal(left, right))),
        "!=" | "OpNEq" => Ok(WitnessValue::Bool(!witness_values_equal(left, right))),
        "and" | "&&" | "OpAnd" => Ok(WitnessValue::Bool(
            expect_bool(left)? && expect_bool(right)?,
        )),
        "or" | "||" | "OpOr" => Ok(WitnessValue::Bool(
            expect_bool(left)? || expect_bool(right)?,
        )),
        "implies" | "=>" | "OpImplies" => Ok(WitnessValue::Bool(
            !expect_bool(left)? || expect_bool(right)?,
        )),
        "+" | "OpAdd" | "OpConc" => match (left, right) {
            (WitnessValue::Int(l), WitnessValue::Int(r)) => Ok(WitnessValue::Int(l + r)),
            (WitnessValue::String(l), WitnessValue::String(r)) => {
                Ok(WitnessValue::String(format!("{l}{r}")))
            }
            (WitnessValue::Set(l), WitnessValue::Set(r)) => {
                let mut values = l.clone();
                for value in r {
                    if !values.contains(value) {
                        values.push(value.clone());
                    }
                }
                Ok(WitnessValue::Set(values))
            }
            (WitnessValue::Seq(l), WitnessValue::Seq(r)) => {
                let mut values = l.clone();
                values.extend(r.clone());
                Ok(WitnessValue::Seq(values))
            }
            _ => Err(format!(
                "unsupported `+` operands: {} and {}",
                render_value(left),
                render_value(right)
            )),
        },
        "-" | "OpSub" => Ok(WitnessValue::Int(expect_int(left)? - expect_int(right)?)),
        "*" | "OpMul" => Ok(WitnessValue::Int(expect_int(left)? * expect_int(right)?)),
        "/" | "OpDiv" => Ok(WitnessValue::Int(expect_int(left)? / expect_int(right)?)),
        "%" | "mod" | "OpMod" => Ok(WitnessValue::Int(expect_int(left)? % expect_int(right)?)),
        ">=" | "OpGe" => Ok(WitnessValue::Bool(expect_int(left)? >= expect_int(right)?)),
        ">" | "OpGt" => Ok(WitnessValue::Bool(expect_int(left)? > expect_int(right)?)),
        "<=" | "OpLe" => Ok(WitnessValue::Bool(expect_int(left)? <= expect_int(right)?)),
        "<" | "OpLt" => Ok(WitnessValue::Bool(expect_int(left)? < expect_int(right)?)),
        "in" => match right {
            WitnessValue::Set(values) | WitnessValue::Seq(values) => {
                Ok(WitnessValue::Bool(values.contains(left)))
            }
            _ => Err(format!(
                "unsupported `in` right operand: {}",
                render_value(right)
            )),
        },
        _ => Err(format!("unsupported binary operator `{op}` in simulation")),
    }
}

fn witness_values_equal(left: &WitnessValue, right: &WitnessValue) -> bool {
    match (left, right) {
        (
            WitnessValue::EnumVariant {
                enum_name: left_enum,
                variant: left_variant,
            },
            WitnessValue::EnumVariant {
                enum_name: right_enum,
                variant: right_variant,
            },
        ) => {
            left_variant == right_variant
                && normalize_type_name(left_enum) == normalize_type_name(right_enum)
        }
        _ => left == right,
    }
}

fn normalize_type_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

fn eval_unop(op: &str, value: &WitnessValue) -> Result<WitnessValue, String> {
    match op {
        "not" | "!" | "OpNot" => Ok(WitnessValue::Bool(!expect_bool(value)?)),
        "-" | "OpNeg" => Ok(WitnessValue::Int(-expect_int(value)?)),
        _ => Err(format!("unsupported unary operator `{op}` in simulation")),
    }
}

fn expect_bool(value: &WitnessValue) -> Result<bool, String> {
    match value {
        WitnessValue::Bool(value) => Ok(*value),
        other => Err(format!("expected bool, found {}", render_value(other))),
    }
}

fn expect_int(value: &WitnessValue) -> Result<i64, String> {
    match value {
        WitnessValue::Int(value) => Ok(*value),
        other => Err(format!("expected int, found {}", render_value(other))),
    }
}

fn expr_kind(expr: &IRExpr) -> &'static str {
    match expr {
        IRExpr::Lit { .. } => "lit",
        IRExpr::Var { .. } => "var",
        IRExpr::Ctor { .. } => "ctor",
        IRExpr::BinOp { .. } => "binop",
        IRExpr::UnOp { .. } => "unop",
        IRExpr::App { .. } => "app",
        IRExpr::Lam { .. } => "lam",
        IRExpr::Let { .. } => "let",
        IRExpr::Forall { .. } => "forall",
        IRExpr::Exists { .. } => "exists",
        IRExpr::One { .. } => "one",
        IRExpr::Lone { .. } => "lone",
        IRExpr::Field { .. } => "field",
        IRExpr::Prime { .. } => "prime",
        IRExpr::Always { .. } => "always",
        IRExpr::Eventually { .. } => "eventually",
        IRExpr::Until { .. } => "until",
        IRExpr::Historically { .. } => "historically",
        IRExpr::Once { .. } => "once",
        IRExpr::Previously { .. } => "previously",
        IRExpr::Since { .. } => "since",
        IRExpr::Aggregate { .. } => "aggregate",
        IRExpr::Saw { .. } => "saw",
        IRExpr::Match { .. } => "match",
        IRExpr::Choose { .. } => "choose",
        IRExpr::MapUpdate { .. } => "map_update",
        IRExpr::Index { .. } => "index",
        IRExpr::SetLit { .. } => "set_lit",
        IRExpr::SeqLit { .. } => "seq_lit",
        IRExpr::MapLit { .. } => "map_lit",
        IRExpr::SetComp { .. } => "set_comp",
        IRExpr::Card { .. } => "card",
        IRExpr::Sorry { .. } => "sorry",
        IRExpr::Todo { .. } => "todo",
        IRExpr::Assert { .. } => "assert",
        IRExpr::Assume { .. } => "assume",
        IRExpr::Block { .. } => "block",
        IRExpr::VarDecl { .. } => "var_decl",
        IRExpr::While { .. } => "while",
        IRExpr::IfElse { .. } => "if_else",
    }
}

fn normalize_float(value: f64) -> String {
    if value.fract() == 0.0 {
        format!("{value:.0}")
    } else {
        value.to_string()
    }
}

fn render_value(value: &WitnessValue) -> String {
    match value {
        WitnessValue::Unknown => "?".to_owned(),
        WitnessValue::Int(value) => value.to_string(),
        WitnessValue::Bool(value) => value.to_string(),
        WitnessValue::Real(value)
        | WitnessValue::Float(value)
        | WitnessValue::String(value)
        | WitnessValue::Identity(value) => value.clone(),
        WitnessValue::EnumVariant { enum_name, variant } => format!("@{enum_name}::{variant}"),
        WitnessValue::SlotRef(slot) => format!("{}[{}]", slot.entity(), slot.slot()),
        WitnessValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(render_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(field, value)| format!("{field}: {}", render_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Set(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(render_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Seq(values) => format!(
            "[{}]",
            values
                .iter()
                .map(render_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, value)| format!("{} -> {}", render_value(key), render_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WitnessValue::Opaque { display, .. } => display.clone(),
    }
}

fn render_type(ty: &IRType) -> String {
    match ty {
        IRType::Bool => "bool".to_owned(),
        IRType::Int => "int".to_owned(),
        IRType::Real => "real".to_owned(),
        IRType::Float => "float".to_owned(),
        IRType::String => "string".to_owned(),
        IRType::Identity => "identity".to_owned(),
        IRType::Entity { name } => name.clone(),
        IRType::Enum { name, .. } => name.clone(),
        IRType::Set { element } => format!("Set<{}>", render_type(element)),
        IRType::Seq { element } => format!("Seq<{}>", render_type(element)),
        IRType::Map { key, value } => format!("Map<{}, {}>", render_type(key), render_type(value)),
        IRType::Tuple { elements } => format!(
            "({})",
            elements
                .iter()
                .map(render_type)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        IRType::Record { name, .. } => name.clone(),
        IRType::Fn { .. } => "<fn>".to_owned(),
        IRType::Refinement { base, .. } => render_type(base),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver;
    use std::io::Write;

    fn lower_source(src: &str) -> driver::LoweredFiles {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("sim.ab");
        let mut file = std::fs::File::create(&path).expect("create source");
        write!(file, "{src}").expect("write source");
        driver::lower_files(std::slice::from_ref(&path)).expect("lower source")
    }

    #[test]
    fn simulate_deep_chain_can_spawn_initial_entity() {
        let lowered = driver::lower_files(&[std::path::PathBuf::from(
            "tests/fixtures/deep_dead_state.ab",
        )])
        .expect("lower fixture");
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 1,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("DeepChain".to_owned()),
            },
        )
        .expect("simulate");

        assert_eq!(result.steps_executed, 1, "expected initial spawn step");
        assert!(matches!(
            result.termination,
            SimulationTermination::StepLimit
        ));
        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let slot = final_state
            .entity_slots()
            .get(&EntitySlotRef::new("E", 0))
            .expect("spawned entity slot");
        assert_eq!(
            slot.fields().get("state"),
            Some(&WitnessValue::EnumVariant {
                enum_name: "Chain".to_owned(),
                variant: "S0".to_owned(),
            })
        );
    }

    #[test]
    fn simulate_nondet_defaults_can_finish_task() {
        let lowered = driver::lower_files(&[std::path::PathBuf::from(
            "tests/fixtures/nondet_defaults.ab",
        )])
        .expect("lower fixture");
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 4,
                seed: 1,
                slots_per_entity: 2,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("TaskManager".to_owned()),
            },
        )
        .expect("simulate");

        assert!(
            result.steps_executed > 0,
            "expected at least one simulated step"
        );
    }

    #[test]
    fn simulate_scope_override_can_enable_single_entity_pool() {
        let lowered = driver::lower_files(&[std::path::PathBuf::from(
            "tests/fixtures/deep_dead_state.ab",
        )])
        .expect("lower fixture");
        let mut overrides = BTreeMap::new();
        overrides.insert("E".to_owned(), 1);
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 0,
                entity_slot_overrides: overrides,
                system: Some("DeepChain".to_owned()),
            },
        )
        .expect("simulate");

        assert_eq!(
            result.steps_executed, 1,
            "expected overridden entity scope to allow spawn"
        );
    }

    #[test]
    fn simulate_rejects_unknown_scope_override_entity() {
        let lowered = driver::lower_files(&[std::path::PathBuf::from(
            "tests/fixtures/deep_dead_state.ab",
        )])
        .expect("lower fixture");
        let mut overrides = BTreeMap::new();
        overrides.insert("Missing".to_owned(), 1);
        let err = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 0,
                entity_slot_overrides: overrides,
                system: Some("DeepChain".to_owned()),
            },
        )
        .expect_err("unknown scope override should fail");

        assert!(
            err.contains("unknown or unused entity `Missing`"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn simulate_macro_step_let_cross_call_binds_result() {
        let lowered = lower_source(
            r"module T

enum Outcome = ok { value: int } | err

system Provider {
  command charge(x: int) -> Outcome {
    return @ok { value: x }
  }
}

system Billing {
  charged: bool = false

  command submit() {
    let result = Provider::charge(1)
    match result {
      ok { value: id } => { charged' = id == 1 }
      err => { charged' = false }
    }
  }
}
",
        );
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 0,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("Billing".to_owned()),
            },
        )
        .expect("simulate");

        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let billing_fields = final_state
            .system_fields()
            .get("Billing")
            .expect("billing system fields");
        assert_eq!(
            billing_fields.get("charged"),
            Some(&WitnessValue::Bool(true)),
            "expected let-bound cross-call result to update charged"
        );
    }

    #[test]
    fn simulate_macro_step_match_cross_call_updates_state() {
        let lowered = lower_source(
            r"module T

enum Outcome = ok | err

system Provider {
  command charge() -> Outcome { return @ok }
}

system Billing {
  charged: bool = false

  command submit() {
    match Provider::charge() {
      ok {} => { charged' = true }
      err {} => { charged' = false }
    }
  }
}
",
        );
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 0,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("Billing".to_owned()),
            },
        )
        .expect("simulate");

        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let billing_fields = final_state
            .system_fields()
            .get("Billing")
            .expect("billing system fields");
        assert_eq!(
            billing_fields.get("charged"),
            Some(&WitnessValue::Bool(true)),
            "expected cross-call scrutinee match to update charged"
        );
    }

    #[test]
    fn simulate_pure_choose_expression_can_synthesize_int_witness() {
        let lowered = lower_source(
            r"module T

system Counter {
  picked: int = 0

  command choose_number() {
    picked' = choose n: int where n > 0 and n < 3
  }
}
",
        );
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 0,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("Counter".to_owned()),
            },
        )
        .expect("simulate");

        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let fields = final_state
            .system_fields()
            .get("Counter")
            .expect("counter system fields");
        assert_eq!(
            fields.get("picked"),
            Some(&WitnessValue::Int(1)),
            "expected deterministic first matching int witness"
        );
    }

    #[test]
    fn simulate_entity_transition_refs_can_drive_guarded_apply() {
        let lowered = lower_source(
            r"module T

enum Status = Active | Frozen

entity Account {
  key: int
  status: Status = @Active
  balance: int = 0

  action transfer_out[to: Account](amount: int)
    requires status == @Active
    requires to.status == @Active
    requires balance >= amount {
    balance' = balance - amount
  }
}

system Bank(accounts: Store<Account>) {
  command seed_accounts() {
    create Account {
      key = 1
      balance = 10
    }
    create Account {
      key = 2
      balance = 0
    }
  }

  command settle() {
    choose from: Account where from.key == 1 {
      choose to: Account where to.key == 2 {
        from.transfer_out[to](3)
      }
    }
  }
}
",
        );
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 2,
                seed: 0,
                slots_per_entity: 2,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("Bank".to_owned()),
            },
        )
        .expect("simulate");

        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let accounts = final_state
            .entity_slots()
            .iter()
            .filter(|(slot, state)| slot.entity() == "Account" && state.active())
            .map(|(_, state)| {
                let id = match state.fields().get("key") {
                    Some(WitnessValue::Int(value)) => *value,
                    other => panic!("expected account key field, found {other:?}"),
                };
                let balance = match state.fields().get("balance") {
                    Some(WitnessValue::Int(value)) => *value,
                    other => panic!("expected account balance field, found {other:?}"),
                };
                (id, balance)
            })
            .collect::<BTreeMap<_, _>>();

        assert_eq!(accounts.get(&1), Some(&7));
        assert_eq!(accounts.get(&2), Some(&0));
    }

    #[test]
    fn simulate_same_step_create_then_choose_then_apply_executes() {
        let lowered = lower_source(
            r"module T

enum Status = Active | Frozen

entity Account {
  key: int
  status: Status = @Active
  balance: int = 0

  action transfer_out[to: Account](amount: int)
    requires status == @Active
    requires to.status == @Active
    requires balance >= amount {
    balance' = balance - amount
  }
}

system Bank(accounts: Store<Account>) {
  command settle() {
    create Account {
      key = 1
      balance = 10
    }
    create Account {
      key = 2
      balance = 0
    }
    choose from: Account where from.key == 1 {
      choose to: Account where to.key == 2 {
        from.transfer_out[to](3)
      }
    }
  }
}
",
        );
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 2,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("Bank".to_owned()),
            },
        )
        .expect("simulate");

        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let accounts = final_state
            .entity_slots()
            .iter()
            .filter(|(slot, state)| slot.entity() == "Account" && state.active())
            .map(|(_, state)| {
                let key = match state.fields().get("key") {
                    Some(WitnessValue::Int(value)) => *value,
                    other => panic!("expected account key field, found {other:?}"),
                };
                let balance = match state.fields().get("balance") {
                    Some(WitnessValue::Int(value)) => *value,
                    other => panic!("expected account balance field, found {other:?}"),
                };
                (key, balance)
            })
            .collect::<BTreeMap<_, _>>();

        assert_eq!(accounts.get(&1), Some(&7));
        assert_eq!(accounts.get(&2), Some(&0));
    }

    #[test]
    fn simulate_imperative_function_with_while_executes() {
        let lowered = lower_source(
            r"module T

fn sum_to(n: int): int {
  var total = 0
  var i = 0
  while i <= n {
    total = total + i
    i = i + 1
  }
  total
}

system Counter {
  total: int = 0

  command run() {
    total' = sum_to(3)
  }
}
",
        );
        let result = simulate_program(
            &lowered.ir_program,
            &SimulateConfig {
                steps: 1,
                seed: 0,
                slots_per_entity: 0,
                entity_slot_overrides: BTreeMap::new(),
                system: Some("Counter".to_owned()),
            },
        )
        .expect("simulate");

        let final_state = result
            .behavior
            .states()
            .last()
            .expect("final state should exist");
        let fields = final_state
            .system_fields()
            .get("Counter")
            .expect("counter system fields");
        assert_eq!(
            fields.get("total"),
            Some(&WitnessValue::Int(6)),
            "expected imperative while-based function to evaluate under simulation"
        );
    }
}
