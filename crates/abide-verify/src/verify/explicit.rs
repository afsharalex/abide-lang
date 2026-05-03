//! Narrow explicit-state backend for finite transition fragments.

use std::collections::{HashMap, HashSet, VecDeque};
use std::time::Instant;

use abide_witness::{
    op::{self, AtomicStepId, Binding},
    EvidenceEnvelope, WitnessEnvelope,
};
use serde::{Deserialize, Serialize};

use crate::ir::types::{
    IRAction, IRCreateField, IREntity, IRExpr, IRField, IRFsm, IRProgram, IRSystemAction,
    IRTransParam, IRTransition, IRType, IRVerify, LitVal,
};

use super::context::VerifyContext;
use super::defenv;
use super::transition;
use super::{
    build_assumptions_for_system_scope, verification_timeout_hint, DeadlockEventDiag,
    FairnessEventAnalysis, FairnessKind, FairnessStatus, VerificationResult,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ExplicitValue {
    Bool(bool),
    Enum { enum_name: String, variant: String },
    Identity(String),
    SlotRef(op::EntitySlotRef),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ExplicitEntitySlotState {
    active: bool,
    values: Vec<ExplicitValue>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ExplicitState {
    system_values: Vec<ExplicitValue>,
    entity_slots: Vec<Vec<ExplicitEntitySlotState>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum MonitorStatus {
    Idle,
    Pending,
    Done,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ExplicitProductState {
    state: ExplicitState,
    monitors: Vec<MonitorStatus>,
}

#[derive(Clone)]
struct ExplicitFieldRef {
    system: String,
    field: String,
}

#[derive(Clone)]
struct ExplicitEntitySpec<'a> {
    name: String,
    slot_count: usize,
    fields: Vec<IRField>,
    field_indices: HashMap<String, usize>,
    transitions: HashMap<String, &'a IRTransition>,
    fsm_decls: Vec<IRFsm>,
}

#[derive(Clone)]
struct ExplicitStepRef<'a> {
    system: String,
    store_param_count: usize,
    step: &'a IRSystemAction,
}

#[derive(Clone)]
struct ExplicitParamBinding {
    name: String,
    value: ExplicitValue,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ExplicitChoiceBinding {
    binder: String,
    selected: op::EntitySlotRef,
}

#[derive(Clone, Copy)]
struct ExplicitSlotBinding {
    entity_index: usize,
    slot: usize,
}

type ExplicitActionState = (
    ExplicitState,
    HashMap<String, ExplicitValue>,
    Vec<op::Choice>,
);

#[derive(Clone)]
enum ExplicitEdge {
    Step {
        system: String,
        step_name: String,
        params: Vec<ExplicitParamBinding>,
        choices: Vec<op::Choice>,
    },
    Stutter,
}

#[derive(Clone)]
struct ExplicitLivenessMonitor {
    trigger: IRExpr,
    response: IRExpr,
    oneshot: bool,
    slot_binding: Option<(String, ExplicitSlotBinding)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExplicitStateSpaceStoreBound {
    pub name: String,
    pub entity_type: String,
    pub slots: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExplicitStateSpaceTransition {
    pub from: usize,
    pub to: usize,
    pub label: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExplicitStateSpace {
    pub systems: Vec<String>,
    pub stutter: bool,
    pub depth_bound: Option<usize>,
    pub store_bounds: Vec<ExplicitStateSpaceStoreBound>,
    pub states: Vec<op::State>,
    pub initial_state: usize,
    pub transitions: Vec<ExplicitStateSpaceTransition>,
}

#[derive(Clone)]
struct ExplicitModel<'a> {
    roots: Vec<String>,
    system_fields: Vec<ExplicitFieldRef>,
    system_field_indices: HashMap<String, usize>,
    entity_specs: Vec<ExplicitEntitySpec<'a>>,
    entity_indices: HashMap<String, usize>,
    steps: Vec<ExplicitStepRef<'a>>,
    step_indices: HashMap<(String, String), usize>,
    safety_properties: Vec<IRExpr>,
    liveness_monitors: Vec<ExplicitLivenessMonitor>,
    extern_assume_exprs: Vec<IRExpr>,
    stutter: bool,
    weak_fair: Vec<(String, String)>,
    strong_fair: Vec<(String, String)>,
    per_tuple_fair: Vec<(String, String)>,
}

fn qualified_system_field_name(system: &str, field: &str) -> String {
    format!("{system}::{field}")
}

fn resolve_system_field_index(
    name: &str,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
) -> Option<usize> {
    if let Some(system) = current_system {
        let qualified = qualified_system_field_name(system, name);
        if let Some(index) = system_fields.get(&qualified) {
            return Some(*index);
        }
    }
    system_fields.get(name).copied()
}

impl<'a> ExplicitModel<'a> {
    fn system_is_scheduled(&self, system: &str) -> bool {
        self.roots.iter().any(|root| root == system)
    }

    fn from_obligation(
        obligation: &'a transition::TransitionVerifyObligation<'a>,
    ) -> Result<Option<(Self, ExplicitState)>, String> {
        let system = obligation.system();

        let mut system_fields = Vec::new();
        let mut system_field_indices = HashMap::new();
        let mut initial_system_values = Vec::new();
        let mut entity_specs = Vec::new();
        let mut entity_indices = HashMap::new();
        for entity in system.relevant_entities() {
            let Some(&slot_count) = system.slots_per_entity().get(entity.name.as_str()) else {
                continue;
            };
            let spec = build_entity_spec(entity, slot_count)?;
            entity_indices.insert(spec.name.clone(), entity_specs.len());
            entity_specs.push(spec);
        }

        let mut steps = Vec::new();
        let mut ambiguous_field_names = HashSet::new();
        for sys in system.relevant_systems() {
            if !sys.let_bindings.is_empty()
                || !sys.procs.is_empty()
                || !sys.derived_fields.is_empty()
            {
                return Ok(None);
            }
            for field in &sys.fields {
                let value = finite_default_value(field)?;
                let idx = system_fields.len();
                system_fields.push(ExplicitFieldRef {
                    system: sys.name.clone(),
                    field: field.name.clone(),
                });
                system_field_indices
                    .insert(qualified_system_field_name(&sys.name, &field.name), idx);
                if !ambiguous_field_names.contains(&field.name) {
                    if system_field_indices.contains_key(&field.name) {
                        system_field_indices.remove(&field.name);
                        ambiguous_field_names.insert(field.name.clone());
                    } else {
                        system_field_indices.insert(field.name.clone(), idx);
                    }
                }
                initial_system_values.push(value);
            }
            for step in &sys.actions {
                for param in &step.params {
                    ensure_supported_explicit_param_type(&param.ty)?;
                }
                steps.push(ExplicitStepRef {
                    system: sys.name.clone(),
                    store_param_count: sys.store_params.len(),
                    step,
                });
            }
        }
        let step_indices = steps
            .iter()
            .enumerate()
            .map(|(index, step)| ((step.system.clone(), step.step.name.clone()), index))
            .collect::<HashMap<_, _>>();
        for step in &steps {
            let mut active_calls = HashSet::new();
            active_calls.insert((step.system.clone(), step.step.name.clone()));
            let param_locals = step
                .step
                .params
                .iter()
                .map(|param| param.name.clone())
                .collect::<HashSet<_>>();
            let final_locals = validate_actions(
                &step.step.body,
                &step.system,
                &system_field_indices,
                &entity_specs,
                &steps,
                &step_indices,
                &param_locals,
                &HashMap::new(),
                &mut active_calls,
            )?;
            if let Some(return_expr) = &step.step.return_expr {
                if !supports_state_expr(
                    return_expr,
                    Some(&step.system),
                    &system_field_indices,
                    &entity_specs,
                    &final_locals,
                    &HashMap::new(),
                ) {
                    return Ok(None);
                }
            }
        }

        let (safety_properties, liveness_monitors) = if obligation.has_liveness() {
            let Some(liveness) = obligation.liveness() else {
                return Ok(None);
            };
            let true_lit = IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            };
            let mut monitors = Vec::new();
            for recipe in liveness.recipes() {
                let mut slot_local_names = HashSet::new();
                let mut static_slot_locals = HashMap::new();
                let bindings = if recipe.is_quantified() {
                    let (Some(var), Some(entity_name)) = recipe.quantified_binding() else {
                        return Ok(None);
                    };
                    let Some((entity_index, spec)) = entity_specs
                        .iter()
                        .enumerate()
                        .find(|(_, spec)| spec.name == entity_name)
                    else {
                        return Ok(None);
                    };
                    slot_local_names.insert(var.to_owned());
                    static_slot_locals.insert(var.to_owned(), entity_index);
                    (0..spec.slot_count)
                        .map(|slot| {
                            Some((var.to_owned(), ExplicitSlotBinding { entity_index, slot }))
                        })
                        .collect::<Vec<_>>()
                } else {
                    vec![None]
                };
                let trigger = recipe.trigger(&true_lit).clone();
                let response = recipe.response().clone();
                if !supports_state_expr(
                    &trigger,
                    None,
                    &system_field_indices,
                    &entity_specs,
                    &HashSet::new(),
                    &static_slot_locals,
                ) || !supports_state_expr(
                    &response,
                    None,
                    &system_field_indices,
                    &entity_specs,
                    &HashSet::new(),
                    &static_slot_locals,
                ) {
                    return Ok(None);
                }
                for slot_binding in bindings {
                    monitors.push(ExplicitLivenessMonitor {
                        trigger: trigger.clone(),
                        response: response.clone(),
                        oneshot: recipe.is_oneshot(),
                        slot_binding,
                    });
                }
            }
            (liveness.safety_obligations().to_vec(), monitors)
        } else {
            (obligation.safety().step_properties().to_vec(), Vec::new())
        };

        for property in &safety_properties {
            if !supports_state_expr(
                property,
                None,
                &system_field_indices,
                &entity_specs,
                &HashSet::new(),
                &HashMap::new(),
            ) {
                return Ok(None);
            }
        }
        let extern_assume_exprs = system.assumptions().extern_assume_exprs().to_vec();
        for expr in &extern_assume_exprs {
            if !supports_state_expr(
                expr,
                None,
                &system_field_indices,
                &entity_specs,
                &HashSet::new(),
                &HashMap::new(),
            ) {
                return Ok(None);
            }
        }
        for step in &steps {
            let value_locals: HashSet<String> = step
                .step
                .params
                .iter()
                .map(|param| param.name.clone())
                .collect();
            if !supports_state_expr(
                &step.step.guard,
                Some(&step.system),
                &system_field_indices,
                &entity_specs,
                &value_locals,
                &HashMap::new(),
            ) {
                return Ok(None);
            }
            let final_locals = validate_actions(
                &step.step.body,
                &step.system,
                &system_field_indices,
                &entity_specs,
                &steps,
                &step_indices,
                &value_locals,
                &HashMap::new(),
                &mut HashSet::new(),
            )?;
            if let Some(return_expr) = &step.step.return_expr {
                if !supports_state_expr(
                    return_expr,
                    Some(&step.system),
                    &system_field_indices,
                    &entity_specs,
                    &final_locals,
                    &HashMap::new(),
                ) {
                    return Ok(None);
                }
            }
        }

        let mut initial_entity_slots = Vec::with_capacity(entity_specs.len());
        for spec in &entity_specs {
            let mut slots = Vec::with_capacity(spec.slot_count);
            for slot in 0..spec.slot_count {
                let values = spec
                    .fields
                    .iter()
                    .map(|field| entity_field_default_value(field, &spec.name, slot))
                    .collect::<Result<Vec<_>, _>>()?;
                slots.push(ExplicitEntitySlotState {
                    active: false,
                    values,
                });
            }
            initial_entity_slots.push(slots);
        }
        for range in system.store_ranges().values() {
            if range.max_active != range.slot_count {
                return Ok(None);
            }
            let Some(&entity_index) = entity_indices.get(&range.entity_type) else {
                continue;
            };
            for slot in range.start_slot..range.start_slot + range.min_active {
                if let Some(slot_state) = initial_entity_slots
                    .get_mut(entity_index)
                    .and_then(|slots| slots.get_mut(slot))
                {
                    slot_state.active = true;
                }
            }
        }

        let model = Self {
            roots: system.selected_system_names().to_vec(),
            system_fields,
            system_field_indices,
            entity_specs,
            entity_indices,
            steps,
            step_indices,
            safety_properties,
            liveness_monitors,
            extern_assume_exprs,
            stutter: system.assumptions().stutter(),
            weak_fair: system.assumptions().weak_fair_event_keys().to_vec(),
            strong_fair: system.assumptions().strong_fair_event_keys().to_vec(),
            per_tuple_fair: system.assumptions().per_tuple_fair_event_keys().to_vec(),
        };
        let initial_state = ExplicitState {
            system_values: initial_system_values,
            entity_slots: initial_entity_slots,
        };
        if !model.state_satisfies_extern_assumptions(&initial_state)? {
            return Ok(None);
        }

        Ok(Some((model, initial_state)))
    }

    fn has_liveness(&self) -> bool {
        !self.liveness_monitors.is_empty()
    }

    fn state_satisfies_extern_assumptions(&self, state: &ExplicitState) -> Result<bool, String> {
        for expr in &self.extern_assume_exprs {
            if !self.eval_bool(state, expr)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn eval_bool(&self, state: &ExplicitState, expr: &IRExpr) -> Result<bool, String> {
        match eval_expr(
            state,
            expr,
            None,
            &self.system_field_indices,
            &self.entity_specs,
            &HashMap::new(),
            &HashMap::new(),
        )? {
            ExplicitValue::Bool(value) => Ok(value),
            other => Err(format!("expected bool expression, found {other:?}")),
        }
    }

    fn property_holds(&self, state: &ExplicitState) -> Result<bool, String> {
        for property in &self.safety_properties {
            if !self.eval_bool(state, property)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn step_successors(
        &self,
        state: &ExplicitState,
    ) -> Result<Vec<(ExplicitState, ExplicitEdge)>, String> {
        let mut out = Vec::new();
        for step in &self.steps {
            if !self.system_is_scheduled(&step.system) {
                continue;
            }
            for bindings in
                enumerate_param_bindings_for_state(&step.step.params, state, &self.entity_specs)?
            {
                for (next, choices) in self.execute_step_with_bindings(state, step, &bindings)? {
                    if !self.state_satisfies_extern_assumptions(&next)? {
                        continue;
                    }
                    out.push((
                        next,
                        ExplicitEdge::Step {
                            system: step.system.clone(),
                            step_name: step.step.name.clone(),
                            params: step
                                .step
                                .params
                                .iter()
                                .map(|param| ExplicitParamBinding {
                                    name: param.name.clone(),
                                    value: bindings[&param.name].clone(),
                                })
                                .collect(),
                            choices,
                        },
                    ));
                }
            }
        }
        Ok(out)
    }

    fn execute_step_with_bindings(
        &self,
        state: &ExplicitState,
        step: &ExplicitStepRef<'_>,
        bindings: &HashMap<String, ExplicitValue>,
    ) -> Result<Vec<(ExplicitState, Vec<op::Choice>)>, String> {
        if !eval_bool_with_locals(
            state,
            &step.step.guard,
            Some(&step.system),
            &self.system_field_indices,
            &self.entity_specs,
            bindings,
            &HashMap::new(),
        )? {
            return Ok(Vec::new());
        }
        execute_actions(
            self,
            state.clone(),
            &step.system,
            &step.step.body,
            bindings,
            &HashMap::new(),
        )
        .map(|states| {
            states
                .into_iter()
                .map(|(state, _, choices)| (state, choices))
                .collect()
        })
    }

    fn advance_monitors(
        &self,
        monitors: &[MonitorStatus],
        state: &ExplicitState,
    ) -> Result<Vec<MonitorStatus>, String> {
        let mut out = Vec::with_capacity(monitors.len());
        for (status, monitor) in monitors.iter().zip(&self.liveness_monitors) {
            let mut slot_locals = HashMap::new();
            let mut slot_active = true;
            if let Some((var, binding)) = &monitor.slot_binding {
                slot_locals.insert(var.clone(), *binding);
                slot_active = state.entity_slots[binding.entity_index][binding.slot].active;
            }
            let (trigger, response) = if slot_active {
                (
                    eval_bool_with_locals(
                        state,
                        &monitor.trigger,
                        None,
                        &self.system_field_indices,
                        &self.entity_specs,
                        &HashMap::new(),
                        &slot_locals,
                    )?,
                    eval_bool_with_locals(
                        state,
                        &monitor.response,
                        None,
                        &self.system_field_indices,
                        &self.entity_specs,
                        &HashMap::new(),
                        &slot_locals,
                    )?,
                )
            } else {
                (false, true)
            };
            let next = match status {
                MonitorStatus::Done => MonitorStatus::Done,
                MonitorStatus::Pending if response => {
                    if monitor.oneshot {
                        MonitorStatus::Done
                    } else {
                        MonitorStatus::Idle
                    }
                }
                MonitorStatus::Pending => MonitorStatus::Pending,
                MonitorStatus::Idle if trigger && !response => MonitorStatus::Pending,
                MonitorStatus::Idle => MonitorStatus::Idle,
            };
            out.push(next);
        }
        Ok(out)
    }

    fn step_enabled_by_key(
        &self,
        state: &ExplicitState,
        system: &str,
        command: &str,
    ) -> Result<bool, String> {
        if !self.system_is_scheduled(system) {
            return Ok(false);
        }
        for step in &self.steps {
            if step.system != system || step.step.name != command {
                continue;
            }
            let bindings =
                enumerate_param_bindings_for_state(&step.step.params, state, &self.entity_specs)?;
            for binding in bindings {
                if !self
                    .execute_step_with_bindings(state, step, &binding)?
                    .is_empty()
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn deadlock_diagnostics(&self, state: &ExplicitState) -> Vec<DeadlockEventDiag> {
        let mut diagnostics = Vec::new();
        let mut seen = HashSet::new();
        for step in &self.steps {
            let key = (step.system.clone(), step.step.name.clone());
            if !seen.insert(key) {
                continue;
            }
            let enabled = self
                .step_enabled_by_key(state, &step.system, &step.step.name)
                .unwrap_or(false);
            if !enabled {
                diagnostics.push(DeadlockEventDiag {
                    system: step.system.clone(),
                    event: step.step.name.clone(),
                    reason: "not enabled in explicit-state fragment".to_owned(),
                });
            }
        }
        diagnostics
    }

    fn step_enabled_by_binding(
        &self,
        state: &ExplicitState,
        system: &str,
        command: &str,
        binding: &HashMap<String, ExplicitValue>,
    ) -> Result<bool, String> {
        if !self.system_is_scheduled(system) {
            return Ok(false);
        }
        for step in &self.steps {
            if step.system != system || step.step.name != command {
                continue;
            }
            if !self
                .execute_step_with_bindings(state, step, binding)?
                .is_empty()
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn fair_param_tuples(
        &self,
        system: &str,
        command: &str,
    ) -> Result<Option<Vec<HashMap<String, ExplicitValue>>>, String> {
        if !self
            .per_tuple_fair
            .iter()
            .any(|(fair_system, fair_command)| fair_system == system && fair_command == command)
        {
            return Ok(None);
        }
        let Some(step) = self
            .steps
            .iter()
            .find(|step| step.system == system && step.step.name == command)
        else {
            return Ok(None);
        };
        if step.step.params.is_empty() {
            return Ok(None);
        }
        Ok(Some(enumerate_param_bindings(&step.step.params)?))
    }

    fn edge_fired_tuple(
        &self,
        edge: &ExplicitEdge,
        system: &str,
        command: &str,
        tuple: &HashMap<String, ExplicitValue>,
    ) -> bool {
        let ExplicitEdge::Step {
            system: edge_system,
            step_name,
            params,
            ..
        } = edge
        else {
            return false;
        };
        if edge_system != system || step_name != command || params.len() != tuple.len() {
            return false;
        }
        params
            .iter()
            .all(|binding| tuple.get(&binding.name) == Some(&binding.value))
    }

    fn edge_choice_tuple(
        &self,
        edge: &ExplicitEdge,
        system: &str,
        command: &str,
    ) -> Option<Vec<ExplicitChoiceBinding>> {
        let ExplicitEdge::Step {
            system: edge_system,
            step_name,
            choices,
            ..
        } = edge
        else {
            return None;
        };
        if edge_system != system || step_name != command {
            return None;
        }
        let tuple: Vec<_> = choices
            .iter()
            .filter_map(|choice| match choice {
                op::Choice::Choose { binder, selected } => Some(ExplicitChoiceBinding {
                    binder: binder.clone(),
                    selected: selected.clone(),
                }),
                op::Choice::ForAll { .. } | op::Choice::Create { .. } => None,
            })
            .collect();
        (!tuple.is_empty()).then_some(tuple)
    }

    fn fair_choice_tuples_in_cycle(
        &self,
        adjacency: &[Vec<(usize, ExplicitEdge)>],
        cycle_nodes: &[usize],
        system: &str,
        command: &str,
    ) -> HashSet<Vec<ExplicitChoiceBinding>> {
        cycle_nodes
            .iter()
            .flat_map(|node_index| adjacency[*node_index].iter())
            .filter_map(|(_, edge)| self.edge_choice_tuple(edge, system, command))
            .collect()
    }

    fn edge_fired_choice_tuple(
        &self,
        edge: &ExplicitEdge,
        system: &str,
        command: &str,
        tuple: &[ExplicitChoiceBinding],
    ) -> bool {
        self.edge_choice_tuple(edge, system, command)
            .is_some_and(|edge_tuple| edge_tuple == tuple)
    }

    fn build_behavior(
        &self,
        trace_states: &[ExplicitState],
        trace_edges: &[ExplicitEdge],
    ) -> Result<op::Behavior, String> {
        let mut behavior = op::Behavior::builder();
        for state in trace_states {
            behavior = behavior.state(self.witness_state(state));
        }

        for (index, edge) in trace_edges.iter().enumerate() {
            let mut transition = op::Transition::builder();
            match edge {
                ExplicitEdge::Step {
                    system,
                    step_name,
                    params,
                    choices,
                } => {
                    let mut atomic_step = op::AtomicStep::builder(
                        AtomicStepId::new(format!("{system}::{step_name}#{index}"))
                            .map_err(|err| err.to_string())?,
                        system.clone(),
                        step_name.clone(),
                    )
                    .step_name(step_name.clone());
                    for binding in params {
                        atomic_step = atomic_step.param(
                            Binding::new(binding.name.clone(), witness_value(&binding.value))
                                .map_err(|err| err.to_string())?,
                        );
                    }
                    for choice in choices {
                        atomic_step = atomic_step.choice(choice.clone());
                    }
                    transition =
                        transition.atomic_step(atomic_step.build().map_err(|err| err.to_string())?);
                }
                ExplicitEdge::Stutter => {
                    transition = transition.observation(
                        op::TransitionObservation::new("stutter", op::WitnessValue::Bool(true))
                            .map_err(|err| err.to_string())?,
                    );
                }
            }
            behavior =
                behavior.transition(transition.build().map_err(|err| {
                    format!("explicit-state transition validation failed: {err}")
                })?);
        }

        behavior
            .build()
            .map_err(|err| format!("explicit-state behavior validation failed: {err}"))
    }

    fn build_prefix_trace(
        &self,
        nodes: &[ExplicitProductState],
        parents: &[Option<(usize, ExplicitEdge)>],
        mut leaf: usize,
    ) -> Result<(Vec<ExplicitState>, Vec<ExplicitEdge>), String> {
        let mut path = vec![leaf];
        while let Some((parent, _)) = &parents[leaf] {
            leaf = *parent;
            path.push(leaf);
        }
        path.reverse();

        let mut states = Vec::with_capacity(path.len());
        let mut edges = Vec::with_capacity(path.len().saturating_sub(1));
        for (pos, node_index) in path.iter().enumerate() {
            states.push(nodes[*node_index].state.clone());
            if pos > 0 {
                let edge = parents[*node_index]
                    .as_ref()
                    .ok_or_else(|| "missing explicit-state parent edge".to_owned())?
                    .1
                    .clone();
                edges.push(edge);
            }
        }
        Ok((states, edges))
    }

    fn build_liveness_trace(
        &self,
        nodes: &[ExplicitProductState],
        parents: &[Option<(usize, ExplicitEdge)>],
        cycle_nodes: &[usize],
        cycle_edges: &[ExplicitEdge],
    ) -> Result<(op::Behavior, usize), String> {
        let start = *cycle_nodes
            .first()
            .ok_or_else(|| "explicit-state liveness cycle is empty".to_owned())?;
        let (mut states, mut edges) = self.build_prefix_trace(nodes, parents, start)?;
        let loop_start = states
            .len()
            .checked_sub(1)
            .ok_or_else(|| "explicit-state liveness trace is missing its loop start".to_owned())?;

        if cycle_nodes.len() == 1 {
            states.push(nodes[start].state.clone());
            edges.push(
                cycle_edges
                    .first()
                    .cloned()
                    .ok_or_else(|| "explicit-state self-loop is missing its edge".to_owned())?,
            );
        } else {
            for node_index in cycle_nodes.iter().skip(1) {
                states.push(nodes[*node_index].state.clone());
            }
            for edge in cycle_edges.iter().take(cycle_nodes.len() - 1) {
                edges.push(edge.clone());
            }
        }

        let behavior = self.build_behavior(&states, &edges)?;
        Ok((behavior, loop_start))
    }

    fn evaluate_fair_cycle(
        &self,
        nodes: &[ExplicitProductState],
        adjacency: &[Vec<(usize, ExplicitEdge)>],
        cycle_nodes: &[usize],
        cycle_edges: &[ExplicitEdge],
    ) -> Result<Option<Vec<FairnessEventAnalysis>>, String> {
        let mut analyses = Vec::new();

        for (system, command) in &self.weak_fair {
            if let Some(tuples) = self.fair_param_tuples(system, command)? {
                for tuple in &tuples {
                    let mut enabled_somewhere = false;
                    let mut enabled_everywhere = true;
                    for node_index in cycle_nodes {
                        let enabled = self.step_enabled_by_binding(
                            &nodes[*node_index].state,
                            system,
                            command,
                            tuple,
                        )?;
                        enabled_somewhere |= enabled;
                        enabled_everywhere &= enabled;
                    }
                    let fired = cycle_edges
                        .iter()
                        .any(|edge| self.edge_fired_tuple(edge, system, command, tuple));
                    let fairness_premise_met = enabled_everywhere;
                    if !fired && fairness_premise_met {
                        return Ok(None);
                    }
                    analyses.push(FairnessEventAnalysis {
                        system: system.clone(),
                        event: format!("{command}{}", render_tuple_suffix(tuple)),
                        kind: FairnessKind::Weak,
                        status: if fired {
                            FairnessStatus::EnabledAndFired
                        } else if enabled_somewhere {
                            FairnessStatus::NeverEnabled
                        } else {
                            FairnessStatus::NeverEnabled
                        },
                    });
                }
                continue;
            }

            let choice_tuples =
                self.fair_choice_tuples_in_cycle(adjacency, cycle_nodes, system, command);
            if !choice_tuples.is_empty() {
                for tuple in &choice_tuples {
                    let mut enabled_somewhere = false;
                    let mut enabled_everywhere = true;
                    for node_index in cycle_nodes {
                        let enabled = adjacency[*node_index].iter().any(|(_, edge)| {
                            self.edge_fired_choice_tuple(edge, system, command, tuple)
                        });
                        enabled_somewhere |= enabled;
                        enabled_everywhere &= enabled;
                    }
                    let fired = cycle_edges
                        .iter()
                        .any(|edge| self.edge_fired_choice_tuple(edge, system, command, tuple));
                    let fairness_premise_met = enabled_everywhere;
                    if !fired && fairness_premise_met {
                        return Ok(None);
                    }
                    analyses.push(FairnessEventAnalysis {
                        system: system.clone(),
                        event: format!("{command}{}", render_choice_suffix(tuple)),
                        kind: FairnessKind::Weak,
                        status: if fired {
                            FairnessStatus::EnabledAndFired
                        } else if enabled_somewhere {
                            FairnessStatus::EnabledButStarved
                        } else {
                            FairnessStatus::NeverEnabled
                        },
                    });
                }
                continue;
            }

            let mut enabled_somewhere = false;
            let mut enabled_everywhere = true;
            for node_index in cycle_nodes {
                let enabled =
                    self.step_enabled_by_key(&nodes[*node_index].state, system, command)?;
                enabled_somewhere |= enabled;
                enabled_everywhere &= enabled;
            }
            let fired = cycle_edges.iter().any(|edge| {
                matches!(
                    edge,
                    ExplicitEdge::Step {
                        system: edge_system,
                        step_name,
                        ..
                    } if edge_system == system && step_name == command
                )
            });
            let fairness_premise_met = enabled_everywhere;
            if !fired && fairness_premise_met {
                return Ok(None);
            }
            analyses.push(FairnessEventAnalysis {
                system: system.clone(),
                event: command.clone(),
                kind: FairnessKind::Weak,
                status: if fired {
                    FairnessStatus::EnabledAndFired
                } else if enabled_somewhere {
                    FairnessStatus::EnabledButStarved
                } else {
                    FairnessStatus::NeverEnabled
                },
            });
        }

        for (system, command) in &self.strong_fair {
            if let Some(tuples) = self.fair_param_tuples(system, command)? {
                for tuple in &tuples {
                    let mut enabled_somewhere = false;
                    for node_index in cycle_nodes {
                        enabled_somewhere |= self.step_enabled_by_binding(
                            &nodes[*node_index].state,
                            system,
                            command,
                            tuple,
                        )?;
                    }
                    let fired = cycle_edges
                        .iter()
                        .any(|edge| self.edge_fired_tuple(edge, system, command, tuple));
                    let fairness_premise_met = enabled_somewhere;
                    if !fired && fairness_premise_met {
                        return Ok(None);
                    }
                    analyses.push(FairnessEventAnalysis {
                        system: system.clone(),
                        event: format!("{command}{}", render_tuple_suffix(tuple)),
                        kind: FairnessKind::Strong,
                        status: if fired {
                            FairnessStatus::EnabledAndFired
                        } else {
                            FairnessStatus::NeverEnabled
                        },
                    });
                }
                continue;
            }

            let choice_tuples =
                self.fair_choice_tuples_in_cycle(adjacency, cycle_nodes, system, command);
            if !choice_tuples.is_empty() {
                for tuple in &choice_tuples {
                    let mut enabled_somewhere = false;
                    for node_index in cycle_nodes {
                        enabled_somewhere |= adjacency[*node_index].iter().any(|(_, edge)| {
                            self.edge_fired_choice_tuple(edge, system, command, tuple)
                        });
                    }
                    let fired = cycle_edges
                        .iter()
                        .any(|edge| self.edge_fired_choice_tuple(edge, system, command, tuple));
                    let fairness_premise_met = enabled_somewhere;
                    if !fired && fairness_premise_met {
                        return Ok(None);
                    }
                    analyses.push(FairnessEventAnalysis {
                        system: system.clone(),
                        event: format!("{command}{}", render_choice_suffix(tuple)),
                        kind: FairnessKind::Strong,
                        status: if fired {
                            FairnessStatus::EnabledAndFired
                        } else if enabled_somewhere {
                            FairnessStatus::EnabledButStarved
                        } else {
                            FairnessStatus::NeverEnabled
                        },
                    });
                }
                continue;
            }

            let mut enabled_somewhere = false;
            for node_index in cycle_nodes {
                enabled_somewhere |=
                    self.step_enabled_by_key(&nodes[*node_index].state, system, command)?;
            }
            let fired = cycle_edges.iter().any(|edge| {
                matches!(
                    edge,
                    ExplicitEdge::Step {
                        system: edge_system,
                        step_name,
                        ..
                    } if edge_system == system && step_name == command
                )
            });
            let fairness_premise_met = enabled_somewhere;
            if !fired && fairness_premise_met {
                return Ok(None);
            }
            analyses.push(FairnessEventAnalysis {
                system: system.clone(),
                event: command.clone(),
                kind: FairnessKind::Strong,
                status: if fired {
                    FairnessStatus::EnabledAndFired
                } else if enabled_somewhere {
                    FairnessStatus::EnabledButStarved
                } else {
                    FairnessStatus::NeverEnabled
                },
            });
        }

        Ok(Some(analyses))
    }

    fn find_liveness_violation(
        &self,
        nodes: &[ExplicitProductState],
        adjacency: &[Vec<(usize, ExplicitEdge)>],
        parents: &[Option<(usize, ExplicitEdge)>],
        verify_block: &IRVerify,
        assumptions: Vec<super::TrustedAssumption>,
    ) -> Result<Option<VerificationResult>, String> {
        if !self.has_liveness() {
            return Ok(None);
        }

        for monitor_index in 0..self.liveness_monitors.len() {
            let pending_nodes: HashSet<usize> = nodes
                .iter()
                .enumerate()
                .filter_map(|(index, node)| {
                    (node.monitors[monitor_index] == MonitorStatus::Pending).then_some(index)
                })
                .collect();
            if pending_nodes.is_empty() {
                continue;
            }

            for scc in strongly_connected_components(adjacency, &pending_nodes) {
                let has_cycle = scc.len() > 1
                    || scc.iter().any(|node| {
                        adjacency[*node]
                            .iter()
                            .any(|(next, _)| *next == *node && pending_nodes.contains(next))
                    });
                if !has_cycle {
                    continue;
                }

                if let Some((cycle_nodes, cycle_edges, fairness_analysis)) =
                    self.find_fair_cycle_in_scc(nodes, adjacency, &scc)?
                {
                    let (behavior, loop_start) =
                        self.build_liveness_trace(nodes, parents, &cycle_nodes, &cycle_edges)?;
                    let evidence = operational_evidence_from_behavior(
                        behavior,
                        WitnessKind::Liveness { loop_start },
                    )
                    .ok();
                    return Ok(Some(VerificationResult::LivenessViolation {
                        name: verify_block.name.clone(),
                        evidence,
                        evidence_extraction_error: None,
                        loop_start,
                        fairness_analysis,
                        assumptions,
                        span: verify_block.span,
                        file: verify_block.file.clone(),
                    }));
                }
            }
        }

        Ok(None)
    }

    fn find_fair_cycle_in_scc(
        &self,
        nodes: &[ExplicitProductState],
        adjacency: &[Vec<(usize, ExplicitEdge)>],
        scc: &HashSet<usize>,
    ) -> Result<Option<(Vec<usize>, Vec<ExplicitEdge>, Vec<FairnessEventAnalysis>)>, String> {
        for start in scc {
            let mut path_nodes = vec![*start];
            let mut path_edges = Vec::new();
            let mut in_path = HashSet::from([*start]);
            if let Some(found) = self.search_cycle_from(
                nodes,
                adjacency,
                scc,
                *start,
                *start,
                &mut path_nodes,
                &mut path_edges,
                &mut in_path,
            )? {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    fn search_cycle_from(
        &self,
        nodes: &[ExplicitProductState],
        adjacency: &[Vec<(usize, ExplicitEdge)>],
        scc: &HashSet<usize>,
        start: usize,
        current: usize,
        path_nodes: &mut Vec<usize>,
        path_edges: &mut Vec<ExplicitEdge>,
        in_path: &mut HashSet<usize>,
    ) -> Result<Option<(Vec<usize>, Vec<ExplicitEdge>, Vec<FairnessEventAnalysis>)>, String> {
        for (next, edge) in &adjacency[current] {
            if !scc.contains(next) {
                continue;
            }
            if *next == start {
                let mut cycle_edges = path_edges.clone();
                cycle_edges.push(edge.clone());
                if let Some(fairness_analysis) =
                    self.evaluate_fair_cycle(nodes, adjacency, path_nodes, &cycle_edges)?
                {
                    return Ok(Some((path_nodes.clone(), cycle_edges, fairness_analysis)));
                }
                continue;
            }
            if in_path.contains(next) {
                continue;
            }
            in_path.insert(*next);
            path_nodes.push(*next);
            path_edges.push(edge.clone());
            if let Some(found) = self.search_cycle_from(
                nodes, adjacency, scc, start, *next, path_nodes, path_edges, in_path,
            )? {
                return Ok(Some(found));
            }
            path_edges.pop();
            path_nodes.pop();
            in_path.remove(next);
        }
        Ok(None)
    }

    fn witness_state(&self, state: &ExplicitState) -> op::State {
        let mut builder = op::State::builder();
        for (index, field) in self.system_fields.iter().enumerate() {
            builder = builder.system_field(
                field.system.clone(),
                field.field.clone(),
                witness_value(&state.system_values[index]),
            );
        }
        for (entity_index, entity_spec) in self.entity_specs.iter().enumerate() {
            for (slot, slot_state) in state.entity_slots[entity_index].iter().enumerate() {
                let mut entity_builder = op::EntityState::builder(slot_state.active);
                for (field_index, field) in entity_spec.fields.iter().enumerate() {
                    entity_builder = entity_builder.field(
                        field.name.clone(),
                        witness_value(&slot_state.values[field_index]),
                    );
                }
                builder = builder.entity_slot(
                    op::EntitySlotRef::new(entity_spec.name.clone(), slot),
                    entity_builder.build(),
                );
            }
        }
        builder.build()
    }

    fn step_by_key(&self, system: &str, command: &str) -> Option<&ExplicitStepRef<'a>> {
        self.step_indices
            .get(&(system.to_owned(), command.to_owned()))
            .and_then(|index| self.steps.get(*index))
    }

    fn steps_by_key(&self, system: &str, command: &str) -> Vec<&ExplicitStepRef<'a>> {
        self.steps
            .iter()
            .filter(|step| step.system == system && step.step.name == command)
            .collect()
    }
}

pub fn explore_verify_state_space(
    ir: &IRProgram,
    verify_block: &IRVerify,
    config: &super::VerifyConfig,
) -> Result<Option<ExplicitStateSpace>, String> {
    let vctx = VerifyContext::from_ir(ir);
    let defs = defenv::DefEnv::from_ir(ir);
    let obligation =
        match transition::TransitionVerifyObligation::for_verify(ir, &vctx, verify_block, &defs) {
            Some(obligation) => obligation,
            None => return Ok(None),
        };
    let (model, initial_state) = match ExplicitModel::from_obligation(&obligation)? {
        Some(pair) => pair,
        None => return Ok(None),
    };

    let deadline = super::verification_deadline(config);
    let depth_bound = verify_block.depth;
    let mut nodes = vec![initial_state.clone()];
    let mut depths = vec![0usize];
    let mut seen: HashMap<ExplicitState, usize> = HashMap::from([(initial_state, 0)]);
    let mut queue = VecDeque::from([0usize]);
    let mut transitions = Vec::new();

    while let Some(index) = queue.pop_front() {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(super::verification_timeout_hint(config));
        }

        if depth_bound.is_some_and(|bound| depths[index] >= bound) {
            continue;
        }

        let state = nodes[index].clone();
        let step_successors = model.step_successors(&state)?;
        let all_successors = if model.stutter {
            let mut out = step_successors;
            out.push((state.clone(), ExplicitEdge::Stutter));
            out
        } else {
            step_successors
        };

        for (next_state, edge) in all_successors {
            let next_index = if let Some(existing) = seen.get(&next_state).copied() {
                existing
            } else {
                let next_index = nodes.len();
                seen.insert(next_state.clone(), next_index);
                nodes.push(next_state);
                depths.push(depths[index] + 1);
                queue.push_back(next_index);
                next_index
            };
            transitions.push(ExplicitStateSpaceTransition {
                from: index,
                to: next_index,
                label: render_explicit_edge_label(&edge),
            });
        }
    }

    Ok(Some(ExplicitStateSpace {
        systems: model.roots.clone(),
        stutter: model.stutter,
        depth_bound,
        store_bounds: verify_block
            .stores
            .iter()
            .map(|store| ExplicitStateSpaceStoreBound {
                name: store.name.clone(),
                entity_type: store.entity_type.clone(),
                slots: usize::try_from(store.hi.max(1)).unwrap_or(1),
            })
            .collect(),
        states: nodes
            .iter()
            .map(|state| model.witness_state(state))
            .collect(),
        initial_state: 0,
        transitions,
    }))
}

pub(super) fn try_check_verify_block_explicit(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    verify_block: &IRVerify,
    config: &super::VerifyConfig,
    deadline: Option<Instant>,
) -> Option<VerificationResult> {
    if config.witness_semantics != super::WitnessSemantics::Operational {
        return None;
    }

    let obligation =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)?;
    let Ok(Some((model, initial_state))) = ExplicitModel::from_obligation(&obligation) else {
        return None;
    };

    let started = Instant::now();
    let assumptions =
        build_assumptions_for_system_scope(ir, &model.roots, &verify_block.assumption_set, &[]);

    let initial_product = ExplicitProductState {
        state: initial_state,
        monitors: vec![MonitorStatus::Idle; model.liveness_monitors.len()],
    };
    let mut nodes = vec![initial_product.clone()];
    let mut parents: Vec<Option<(usize, ExplicitEdge)>> = vec![None];
    let mut adjacency: Vec<Vec<(usize, ExplicitEdge)>> = vec![Vec::new()];
    let mut seen: HashMap<ExplicitProductState, usize> = HashMap::from([(initial_product, 0)]);
    let mut queue = VecDeque::from([0usize]);

    while let Some(index) = queue.pop_front() {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Some(VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: verification_timeout_hint(config),
                span: verify_block.span,
                file: verify_block.file.clone(),
            });
        }

        let node = nodes[index].clone();
        let safe = match model.property_holds(&node.state) {
            Ok(value) => value,
            Err(_) => return None,
        };
        if !safe {
            let (trace_states, trace_edges) =
                model.build_prefix_trace(&nodes, &parents, index).ok()?;
            let evidence = model
                .build_behavior(&trace_states, &trace_edges)
                .ok()
                .and_then(|behavior| {
                    operational_evidence_from_behavior(behavior, WitnessKind::Counterexample).ok()
                });
            return Some(VerificationResult::Counterexample {
                name: verify_block.name.clone(),
                evidence,
                evidence_extraction_error: None,
                assumptions,
                span: verify_block.span,
                file: verify_block.file.clone(),
            });
        }

        let step_successors = match model.step_successors(&node.state) {
            Ok(successors) => successors,
            Err(_) => return None,
        };

        if step_successors.is_empty() && !model.stutter {
            let (trace_states, trace_edges) =
                model.build_prefix_trace(&nodes, &parents, index).ok()?;
            let evidence = model
                .build_behavior(&trace_states, &trace_edges)
                .ok()
                .and_then(|behavior| {
                    operational_evidence_from_behavior(behavior, WitnessKind::Deadlock).ok()
                });
            return Some(VerificationResult::Deadlock {
                name: verify_block.name.clone(),
                evidence,
                evidence_extraction_error: None,
                step: index,
                reason: "no enabled step in the explicit-state fragment and stutter is opted out"
                    .to_owned(),
                event_diagnostics: model.deadlock_diagnostics(&node.state),
                assumptions,
                span: verify_block.span,
                file: verify_block.file.clone(),
            });
        }

        let next_monitors = match model.advance_monitors(&node.monitors, &node.state) {
            Ok(next) => next,
            Err(_) => return None,
        };

        let all_successors = if model.stutter {
            let mut out = step_successors;
            out.push((node.state.clone(), ExplicitEdge::Stutter));
            out
        } else {
            step_successors
        };

        for (next_state, edge) in all_successors {
            let next_product = ExplicitProductState {
                state: next_state,
                monitors: next_monitors.clone(),
            };
            let next_index = if let Some(existing) = seen.get(&next_product).copied() {
                existing
            } else {
                let next_index = nodes.len();
                seen.insert(next_product.clone(), next_index);
                nodes.push(next_product);
                parents.push(Some((index, edge.clone())));
                adjacency.push(Vec::new());
                queue.push_back(next_index);
                next_index
            };
            adjacency[index].push((next_index, edge));
        }
    }

    if let Ok(Some(result)) = model.find_liveness_violation(
        &nodes,
        &adjacency,
        &parents,
        verify_block,
        assumptions.clone(),
    ) {
        return Some(result);
    }

    Some(VerificationResult::Proved {
        name: verify_block.name.clone(),
        method: "explicit-state exhaustive search".to_owned(),
        time_ms: started.elapsed().as_millis() as u64,
        assumptions,
        span: verify_block.span,
        file: verify_block.file.clone(),
    })
}

#[derive(Clone, Copy)]
enum WitnessKind {
    Counterexample,
    Deadlock,
    Liveness { loop_start: usize },
}

fn operational_evidence_from_behavior(
    behavior: op::Behavior,
    kind: WitnessKind,
) -> Result<EvidenceEnvelope, String> {
    let witness = match kind {
        WitnessKind::Counterexample => op::OperationalWitness::counterexample(behavior),
        WitnessKind::Deadlock => op::OperationalWitness::deadlock(behavior),
        WitnessKind::Liveness { loop_start } => {
            op::OperationalWitness::liveness(behavior, loop_start)
        }
    }
    .map_err(|err| format!("explicit-state witness validation failed: {err}"))?;
    let witness = WitnessEnvelope::operational(witness)
        .map_err(|err| format!("explicit-state witness envelope validation failed: {err}"))?;
    EvidenceEnvelope::witness(witness)
        .map_err(|err| format!("explicit-state evidence validation failed: {err}"))
}

fn strongly_connected_components(
    adjacency: &[Vec<(usize, ExplicitEdge)>],
    subset: &HashSet<usize>,
) -> Vec<HashSet<usize>> {
    struct Tarjan<'a> {
        adjacency: &'a [Vec<(usize, ExplicitEdge)>],
        subset: &'a HashSet<usize>,
        index: usize,
        indices: HashMap<usize, usize>,
        lowlinks: HashMap<usize, usize>,
        stack: Vec<usize>,
        on_stack: HashSet<usize>,
        components: Vec<HashSet<usize>>,
    }

    impl<'a> Tarjan<'a> {
        fn visit(&mut self, node: usize) {
            self.indices.insert(node, self.index);
            self.lowlinks.insert(node, self.index);
            self.index += 1;
            self.stack.push(node);
            self.on_stack.insert(node);

            for (next, _) in &self.adjacency[node] {
                if !self.subset.contains(next) {
                    continue;
                }
                if !self.indices.contains_key(next) {
                    self.visit(*next);
                    let low = self.lowlinks[&node].min(self.lowlinks[next]);
                    self.lowlinks.insert(node, low);
                } else if self.on_stack.contains(next) {
                    let low = self.lowlinks[&node].min(self.indices[next]);
                    self.lowlinks.insert(node, low);
                }
            }

            if self.lowlinks[&node] == self.indices[&node] {
                let mut component = HashSet::new();
                while let Some(popped) = self.stack.pop() {
                    self.on_stack.remove(&popped);
                    component.insert(popped);
                    if popped == node {
                        break;
                    }
                }
                self.components.push(component);
            }
        }
    }

    let mut tarjan = Tarjan {
        adjacency,
        subset,
        index: 0,
        indices: HashMap::new(),
        lowlinks: HashMap::new(),
        stack: Vec::new(),
        on_stack: HashSet::new(),
        components: Vec::new(),
    };

    for node in subset {
        if !tarjan.indices.contains_key(node) {
            tarjan.visit(*node);
        }
    }

    tarjan.components
}

fn build_entity_spec<'a>(
    entity: &'a IREntity,
    slot_count: usize,
) -> Result<ExplicitEntitySpec<'a>, String> {
    let mut field_indices = HashMap::new();
    for (index, field) in entity.fields.iter().enumerate() {
        if field.initial_constraint.is_some() {
            return Err(format!(
                "unsupported explicit-state entity field `{}`; nondeterministic initial constraints are not supported",
                field.name
            ));
        }
        finite_default_value(field)?;
        field_indices.insert(field.name.clone(), index);
    }
    let mut transitions = HashMap::new();
    for transition in &entity.transitions {
        if transition.postcondition.is_some() {
            return Err(format!(
                "unsupported explicit-state transition `{}::{}`",
                entity.name, transition.name
            ));
        }
        for param in &transition.params {
            ensure_supported_explicit_param_type(&param.ty)?;
        }
        transitions.insert(transition.name.clone(), transition);
    }
    Ok(ExplicitEntitySpec {
        name: entity.name.clone(),
        slot_count,
        fields: entity.fields.clone(),
        field_indices,
        transitions,
        fsm_decls: entity.fsm_decls.clone(),
    })
}

fn validate_actions(
    actions: &[IRAction],
    current_system: &str,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    steps: &[ExplicitStepRef<'_>],
    step_indices: &HashMap<(String, String), usize>,
    value_locals: &HashSet<String>,
    slot_locals: &HashMap<String, usize>,
    active_calls: &mut HashSet<(String, String)>,
) -> Result<HashSet<String>, String> {
    let mut current_locals = value_locals.clone();
    for action in actions {
        current_locals = validate_action(
            action,
            current_system,
            system_fields,
            entity_specs,
            steps,
            step_indices,
            &current_locals,
            slot_locals,
            active_calls,
        )?;
    }
    Ok(current_locals)
}

fn validate_action(
    action: &IRAction,
    current_system: &str,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    steps: &[ExplicitStepRef<'_>],
    step_indices: &HashMap<(String, String), usize>,
    value_locals: &HashSet<String>,
    slot_locals: &HashMap<String, usize>,
    active_calls: &mut HashSet<(String, String)>,
) -> Result<HashSet<String>, String> {
    match action {
        IRAction::ExprStmt { expr } => {
            let IRExpr::BinOp {
                op, left, right, ..
            } = expr
            else {
                return Err("explicit-state step action must be an assignment equality".to_owned());
            };
            if op != "OpEq" && op != "==" {
                return Err("explicit-state step action must use equality assignment".to_owned());
            }
            if !supports_assignment_target(
                left,
                Some(current_system),
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            ) || !supports_state_expr(
                right,
                Some(current_system),
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            ) {
                return Err("unsupported assignment in explicit-state fragment".to_owned());
            }
            Ok(value_locals.clone())
        }
        IRAction::Create { entity, fields } => {
            let Some(spec) = entity_specs.iter().find(|spec| spec.name == *entity) else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            for IRCreateField { name, value } in fields {
                if !spec.field_indices.contains_key(name)
                    || !supports_state_expr(
                        value,
                        Some(current_system),
                        system_fields,
                        entity_specs,
                        value_locals,
                        slot_locals,
                    )
                {
                    return Err("unsupported create field in explicit-state fragment".to_owned());
                }
            }
            Ok(value_locals.clone())
        }
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } => {
            let Some(spec) = entity_specs.iter().find(|spec| spec.name == *entity) else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            let Some((entity_index, _)) = entity_specs
                .iter()
                .enumerate()
                .find(|(_, candidate)| candidate.name == *entity)
            else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            let mut nested_slot_locals = slot_locals.clone();
            nested_slot_locals.insert(var.clone(), entity_index);
            if !supports_state_expr(
                filter,
                Some(current_system),
                system_fields,
                entity_specs,
                value_locals,
                &nested_slot_locals,
            ) {
                return Err("unsupported choose filter in explicit-state fragment".to_owned());
            }
            if ops.is_empty() || spec.slot_count == 0 {
                return Err("unsupported choose body in explicit-state fragment".to_owned());
            }
            validate_actions(
                ops,
                current_system,
                system_fields,
                entity_specs,
                steps,
                step_indices,
                value_locals,
                &nested_slot_locals,
                active_calls,
            )?;
            Ok(value_locals.clone())
        }
        IRAction::LetCrossCall {
            name,
            system,
            command,
            args,
        } => {
            if !validate_cross_call_like(
                system,
                command,
                &[],
                args,
                Some(current_system),
                system_fields,
                entity_specs,
                steps,
                step_indices,
                value_locals,
                active_calls,
            )? {
                return Err("unsupported LetCrossCall in explicit-state fragment".to_owned());
            }
            let mut locals = value_locals.clone();
            locals.insert(name.clone());
            Ok(locals)
        }
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => {
            if !slot_locals.contains_key(target) {
                if step_indices.contains_key(&(target.clone(), transition.clone())) {
                    validate_cross_call_like(
                        target,
                        transition,
                        refs,
                        args,
                        Some(current_system),
                        system_fields,
                        entity_specs,
                        steps,
                        step_indices,
                        value_locals,
                        active_calls,
                    )?;
                    return Ok(value_locals.clone());
                }
                return Err("unsupported apply in explicit-state fragment".to_owned());
            }
            let Some(spec) = entity_spec_for_binding(entity_specs, slot_locals, target) else {
                return Err("unsupported apply in explicit-state fragment".to_owned());
            };
            let Some(trans) = spec.transitions.get(transition) else {
                return Err(format!(
                    "unknown explicit-state transition `{}::{transition}`",
                    spec.name
                ));
            };
            let mut transition_value_locals = value_locals.clone();
            transition_value_locals.extend(trans.params.iter().map(|param| param.name.clone()));
            transition_value_locals.extend(spec.fields.iter().map(|field| field.name.clone()));
            if args.len() != trans.params.len() || refs.len() != trans.refs.len() {
                return Err("unsupported apply in explicit-state fragment".to_owned());
            }
            let mut transition_slot_locals = slot_locals.clone();
            for (ref_name, decl) in refs.iter().zip(&trans.refs) {
                let Some(&entity_index) = slot_locals.get(ref_name) else {
                    return Err("unsupported apply in explicit-state fragment".to_owned());
                };
                let Some((decl_entity_index, _)) = entity_specs
                    .iter()
                    .enumerate()
                    .find(|(_, candidate)| candidate.name == decl.entity)
                else {
                    return Err("unsupported apply in explicit-state fragment".to_owned());
                };
                if entity_index != decl_entity_index {
                    return Err("unsupported apply in explicit-state fragment".to_owned());
                }
                transition_slot_locals.insert(decl.name.clone(), entity_index);
            }
            for (arg, param) in args.iter().zip(&trans.params) {
                if !supports_explicit_param_type(&param.ty)
                    || !supports_state_expr(
                        arg,
                        Some(current_system),
                        system_fields,
                        entity_specs,
                        value_locals,
                        &transition_slot_locals,
                    )
                {
                    return Err("unsupported apply in explicit-state fragment".to_owned());
                }
            }
            if !supports_state_expr(
                &trans.guard,
                Some(current_system),
                system_fields,
                entity_specs,
                &transition_value_locals,
                &transition_slot_locals,
            ) {
                return Err("unsupported transition guard in explicit-state fragment".to_owned());
            }
            for update in &trans.updates {
                if !spec.field_indices.contains_key(&update.field)
                    || !supports_state_expr(
                        &update.value,
                        Some(current_system),
                        system_fields,
                        entity_specs,
                        &transition_value_locals,
                        &transition_slot_locals,
                    )
                {
                    return Err(
                        "unsupported transition update in explicit-state fragment".to_owned()
                    );
                }
            }
            Ok(value_locals.clone())
        }
        IRAction::CrossCall {
            system,
            command,
            args,
        } => {
            validate_cross_call_like(
                system,
                command,
                &[],
                args,
                Some(current_system),
                system_fields,
                entity_specs,
                steps,
                step_indices,
                value_locals,
                active_calls,
            )?;
            Ok(value_locals.clone())
        }
        IRAction::Match { scrutinee, arms } => {
            match scrutinee {
                crate::ir::types::IRActionMatchScrutinee::Var { name } => {
                    if !value_locals.contains(name) {
                        return Err("unsupported match in explicit-state fragment".to_owned());
                    }
                }
                crate::ir::types::IRActionMatchScrutinee::CrossCall {
                    system,
                    command,
                    args,
                } => {
                    if !validate_cross_call_like(
                        system,
                        command,
                        &[],
                        args,
                        Some(current_system),
                        system_fields,
                        entity_specs,
                        steps,
                        step_indices,
                        value_locals,
                        active_calls,
                    )? {
                        return Err("unsupported match in explicit-state fragment".to_owned());
                    }
                }
            }
            for arm in arms {
                if !pattern_supported(&arm.pattern) {
                    return Err("unsupported match pattern in explicit-state fragment".to_owned());
                }
                if let Some(guard) = &arm.guard {
                    if !supports_state_expr(
                        guard,
                        Some(current_system),
                        system_fields,
                        entity_specs,
                        value_locals,
                        slot_locals,
                    ) {
                        return Err("unsupported match guard in explicit-state fragment".to_owned());
                    }
                }
                validate_actions(
                    &arm.body,
                    current_system,
                    system_fields,
                    entity_specs,
                    steps,
                    step_indices,
                    value_locals,
                    slot_locals,
                    active_calls,
                )?;
            }
            Ok(value_locals.clone())
        }
        _ => Err("unsupported action in explicit-state fragment".to_owned()),
    }
}

fn validate_cross_call_like(
    system: &str,
    command: &str,
    refs: &[String],
    args: &[IRExpr],
    caller_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    steps: &[ExplicitStepRef<'_>],
    step_indices: &HashMap<(String, String), usize>,
    value_locals: &HashSet<String>,
    active_calls: &mut HashSet<(String, String)>,
) -> Result<bool, String> {
    let Some(step_index) = step_indices.get(&(system.to_owned(), command.to_owned())) else {
        return Err("unsupported cross-call in explicit-state fragment".to_owned());
    };
    let callee = &steps[*step_index];
    if args.len() != callee.step.params.len()
        || (!refs.is_empty() && refs.len() != callee.store_param_count)
    {
        return Err("unsupported cross-call in explicit-state fragment".to_owned());
    }
    let call_key = (system.to_owned(), command.to_owned());
    if !active_calls.insert(call_key.clone()) {
        return Err("unsupported recursive cross-call in explicit-state fragment".to_owned());
    }
    let mut callee_value_locals = HashSet::new();
    for (arg, param) in args.iter().zip(&callee.step.params) {
        if !supports_explicit_param_type(&param.ty)
            || !supports_state_expr(
                arg,
                caller_system,
                system_fields,
                entity_specs,
                value_locals,
                &HashMap::new(),
            )
        {
            active_calls.remove(&call_key);
            return Err("unsupported cross-call in explicit-state fragment".to_owned());
        }
        callee_value_locals.insert(param.name.clone());
    }
    if !supports_state_expr(
        &callee.step.guard,
        Some(&callee.system),
        system_fields,
        entity_specs,
        &callee_value_locals,
        &HashMap::new(),
    ) {
        active_calls.remove(&call_key);
        return Err("unsupported cross-call in explicit-state fragment".to_owned());
    }
    let final_locals = match validate_actions(
        &callee.step.body,
        &callee.system,
        system_fields,
        entity_specs,
        steps,
        step_indices,
        &callee_value_locals,
        &HashMap::new(),
        active_calls,
    ) {
        Ok(locals) => locals,
        Err(err) => {
            active_calls.remove(&call_key);
            return Err(err);
        }
    };
    let has_finite_return = if let Some(return_expr) = &callee.step.return_expr {
        if supports_state_expr(
            return_expr,
            Some(&callee.system),
            system_fields,
            entity_specs,
            &final_locals,
            &HashMap::new(),
        ) {
            true
        } else {
            active_calls.remove(&call_key);
            return Err("unsupported cross-call return in explicit-state fragment".to_owned());
        }
    } else {
        false
    };
    active_calls.remove(&call_key);
    Ok(has_finite_return)
}

fn entity_spec_for_binding<'a>(
    entity_specs: &'a [ExplicitEntitySpec<'a>],
    slot_locals: &HashMap<String, usize>,
    target: &str,
) -> Option<&'a ExplicitEntitySpec<'a>> {
    slot_locals
        .get(target)
        .and_then(|entity_index| entity_specs.get(*entity_index))
}

fn execute_actions(
    model: &ExplicitModel<'_>,
    state: ExplicitState,
    current_system: &str,
    actions: &[IRAction],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<Vec<ExplicitActionState>, String> {
    if actions.is_empty() {
        return Ok(vec![(state, value_locals.clone(), Vec::new())]);
    }
    let mut out = Vec::new();
    for (next_state, next_locals, mut choices) in execute_action(
        model,
        state,
        current_system,
        &actions[0],
        value_locals,
        slot_locals,
    )? {
        for (later_state, later_locals, mut later_choices) in execute_actions(
            model,
            next_state,
            current_system,
            &actions[1..],
            &next_locals,
            slot_locals,
        )? {
            choices.append(&mut later_choices);
            out.push((later_state, later_locals, choices.clone()));
        }
    }
    Ok(out)
}

fn execute_action(
    model: &ExplicitModel<'_>,
    state: ExplicitState,
    current_system: &str,
    action: &IRAction,
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<Vec<ExplicitActionState>, String> {
    match action {
        IRAction::ExprStmt { expr } => {
            let mut next = state;
            apply_assignment(
                &mut next,
                expr,
                Some(current_system),
                &model.system_field_indices,
                &model.entity_specs,
                value_locals,
                slot_locals,
            )?;
            Ok(vec![(next, value_locals.clone(), Vec::new())])
        }
        IRAction::Create { entity, fields } => {
            let Some(&entity_index) = model.entity_indices.get(entity) else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            let spec = &model.entity_specs[entity_index];
            let mut out = Vec::new();
            for slot in 0..spec.slot_count {
                if state.entity_slots[entity_index][slot].active {
                    continue;
                }
                let mut next = state.clone();
                let mut values = spec
                    .fields
                    .iter()
                    .map(|field| entity_field_default_value(field, &spec.name, slot))
                    .collect::<Result<Vec<_>, _>>()?;
                for field in fields {
                    let index = *spec
                        .field_indices
                        .get(&field.name)
                        .ok_or_else(|| format!("unknown explicit-state field `{}`", field.name))?;
                    values[index] = eval_expr(
                        &next,
                        &field.value,
                        Some(current_system),
                        &model.system_field_indices,
                        &model.entity_specs,
                        value_locals,
                        slot_locals,
                    )?;
                }
                next.entity_slots[entity_index][slot] = ExplicitEntitySlotState {
                    active: true,
                    values,
                };
                out.push((
                    next,
                    value_locals.clone(),
                    vec![op::Choice::Create {
                        created: op::EntitySlotRef::new(entity.clone(), slot),
                    }],
                ));
            }
            Ok(out)
        }
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } => {
            let Some(&entity_index) = model.entity_indices.get(entity) else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            let mut out = Vec::new();
            for slot in 0..model.entity_specs[entity_index].slot_count {
                if !state.entity_slots[entity_index][slot].active {
                    continue;
                }
                let mut nested_slots = slot_locals.clone();
                nested_slots.insert(var.clone(), ExplicitSlotBinding { entity_index, slot });
                if !eval_bool_with_locals(
                    &state,
                    filter,
                    Some(current_system),
                    &model.system_field_indices,
                    &model.entity_specs,
                    value_locals,
                    &nested_slots,
                )? {
                    continue;
                }
                for (next, nested_locals, mut choices) in execute_actions(
                    model,
                    state.clone(),
                    current_system,
                    ops,
                    value_locals,
                    &nested_slots,
                )? {
                    let mut all_choices = vec![op::Choice::Choose {
                        binder: var.clone(),
                        selected: op::EntitySlotRef::new(entity.clone(), slot),
                    }];
                    all_choices.append(&mut choices);
                    out.push((next, nested_locals, all_choices));
                }
            }
            Ok(out)
        }
        IRAction::LetCrossCall {
            name,
            system,
            command,
            args,
        } => {
            let mut out = Vec::new();
            for (next, result, choices) in execute_cross_call_like_result(
                model,
                state,
                system,
                command,
                &[],
                args,
                Some(current_system),
                value_locals,
            )? {
                let Some(result) = result else {
                    return Err("unsupported LetCrossCall in explicit-state fragment".to_owned());
                };
                let mut locals = value_locals.clone();
                locals.insert(name.clone(), result);
                out.push((next, locals, choices));
            }
            Ok(out)
        }
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => {
            if !slot_locals.contains_key(target) {
                if model.step_by_key(target, transition).is_some() {
                    return execute_cross_call_like(
                        model,
                        state,
                        target,
                        transition,
                        refs,
                        args,
                        Some(current_system),
                        value_locals,
                    );
                }
                return Err("unsupported apply in explicit-state fragment".to_owned());
            }
            let Some(binding) = slot_locals.get(target) else {
                return Err("unsupported apply in explicit-state fragment".to_owned());
            };
            let spec = &model.entity_specs[binding.entity_index];
            let Some(trans) = spec.transitions.get(transition) else {
                return Err(format!(
                    "unknown explicit-state transition `{}::{transition}`",
                    spec.name
                ));
            };
            if args.len() != trans.params.len() || refs.len() != trans.refs.len() {
                return Err("unsupported apply in explicit-state fragment".to_owned());
            }
            let mut transition_slot_locals = slot_locals.clone();
            for (ref_name, decl) in refs.iter().zip(&trans.refs) {
                let Some(ref_binding) = slot_locals.get(ref_name) else {
                    return Err("unsupported apply in explicit-state fragment".to_owned());
                };
                if model.entity_specs[ref_binding.entity_index].name != decl.entity {
                    return Err("unsupported apply in explicit-state fragment".to_owned());
                }
                transition_slot_locals.insert(decl.name.clone(), *ref_binding);
            }
            let transition_args = trans
                .params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| {
                    Ok::<_, String>((
                        param.name.clone(),
                        eval_expr(
                            &state,
                            arg,
                            Some(current_system),
                            &model.system_field_indices,
                            &model.entity_specs,
                            value_locals,
                            &transition_slot_locals,
                        )?,
                    ))
                })
                .collect::<Result<HashMap<_, _>, _>>()?;
            let transition_locals = transition_value_locals(
                value_locals,
                state.entity_slots[binding.entity_index][binding.slot]
                    .values
                    .as_slice(),
                spec,
                &transition_args,
            );
            if !eval_bool_with_locals(
                &state,
                &trans.guard,
                Some(current_system),
                &model.system_field_indices,
                &model.entity_specs,
                &transition_locals,
                &transition_slot_locals,
            )? {
                return Ok(Vec::new());
            }
            let mut next = state;
            let update_values = trans
                .updates
                .iter()
                .map(|update| {
                    let index = *spec.field_indices.get(&update.field).ok_or_else(|| {
                        format!("unknown explicit-state field `{}`", update.field)
                    })?;
                    let value = eval_expr(
                        &next,
                        &update.value,
                        Some(current_system),
                        &model.system_field_indices,
                        &model.entity_specs,
                        &transition_locals,
                        &transition_slot_locals,
                    )?;
                    Ok::<_, String>((index, value))
                })
                .collect::<Result<Vec<_>, _>>()?;
            if !fsm_updates_are_allowed(
                spec,
                next.entity_slots[binding.entity_index][binding.slot]
                    .values
                    .as_slice(),
                &update_values,
            ) {
                return Ok(Vec::new());
            }
            for (index, value) in update_values {
                next.entity_slots[binding.entity_index][binding.slot].values[index] = value;
            }
            Ok(vec![(next, value_locals.clone(), Vec::new())])
        }
        IRAction::CrossCall {
            system,
            command,
            args,
        } => execute_cross_call_like(
            model,
            state,
            system,
            command,
            &[],
            args,
            Some(current_system),
            value_locals,
        ),
        IRAction::Match { scrutinee, arms } => {
            let mut branches = Vec::new();
            match scrutinee {
                crate::ir::types::IRActionMatchScrutinee::Var { name } => {
                    let Some(value) = value_locals.get(name) else {
                        return Err("unsupported match in explicit-state fragment".to_owned());
                    };
                    branches.push((state, value.clone(), Vec::new()));
                }
                crate::ir::types::IRActionMatchScrutinee::CrossCall {
                    system,
                    command,
                    args,
                } => {
                    for (next, result, choices) in execute_cross_call_like_result(
                        model,
                        state,
                        system,
                        command,
                        &[],
                        args,
                        Some(current_system),
                        value_locals,
                    )? {
                        let Some(result) = result else {
                            return Err("unsupported match in explicit-state fragment".to_owned());
                        };
                        branches.push((next, result, choices));
                    }
                }
            }
            let mut out = Vec::new();
            for (branch_state, scrutinee_value, branch_choices) in branches {
                for arm in arms {
                    if !pattern_matches(&scrutinee_value, &arm.pattern) {
                        continue;
                    }
                    if let Some(guard) = &arm.guard {
                        if !eval_bool_with_locals(
                            &branch_state,
                            guard,
                            Some(current_system),
                            &model.system_field_indices,
                            &model.entity_specs,
                            value_locals,
                            slot_locals,
                        )? {
                            continue;
                        }
                    }
                    for (next, locals, mut choices) in execute_actions(
                        model,
                        branch_state.clone(),
                        current_system,
                        &arm.body,
                        value_locals,
                        slot_locals,
                    )? {
                        let mut all_choices = branch_choices.clone();
                        all_choices.append(&mut choices);
                        out.push((next, locals, all_choices));
                    }
                }
            }
            Ok(out)
        }
        _ => Err("unsupported action in explicit-state fragment".to_owned()),
    }
}

fn execute_cross_call_like(
    model: &ExplicitModel<'_>,
    state: ExplicitState,
    system: &str,
    command: &str,
    refs: &[String],
    args: &[IRExpr],
    caller_system: Option<&str>,
    value_locals: &HashMap<String, ExplicitValue>,
) -> Result<Vec<ExplicitActionState>, String> {
    Ok(execute_cross_call_like_result(
        model,
        state,
        system,
        command,
        refs,
        args,
        caller_system,
        value_locals,
    )?
    .into_iter()
    .map(|(state, _, choices)| (state, value_locals.clone(), choices))
    .collect())
}

fn execute_cross_call_like_result(
    model: &ExplicitModel<'_>,
    state: ExplicitState,
    system: &str,
    command: &str,
    refs: &[String],
    args: &[IRExpr],
    caller_system: Option<&str>,
    value_locals: &HashMap<String, ExplicitValue>,
) -> Result<Vec<(ExplicitState, Option<ExplicitValue>, Vec<op::Choice>)>, String> {
    let callees = model.steps_by_key(system, command);
    if callees.is_empty() {
        return Err("unsupported cross-call in explicit-state fragment".to_owned());
    }
    let mut out = Vec::new();
    for callee in callees {
        if args.len() != callee.step.params.len()
            || (!refs.is_empty() && refs.len() != callee.store_param_count)
        {
            return Err("unsupported cross-call in explicit-state fragment".to_owned());
        }
        let callee_bindings = callee
            .step
            .params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| {
                Ok::<_, String>((
                    param.name.clone(),
                    eval_expr(
                        &state,
                        arg,
                        caller_system,
                        &model.system_field_indices,
                        &model.entity_specs,
                        value_locals,
                        &HashMap::new(),
                    )?,
                ))
            })
            .collect::<Result<HashMap<_, _>, _>>()?;
        if !eval_bool_with_locals(
            &state,
            &callee.step.guard,
            Some(&callee.system),
            &model.system_field_indices,
            &model.entity_specs,
            &callee_bindings,
            &HashMap::new(),
        )? {
            continue;
        }
        for (next, callee_locals, choices) in execute_actions(
            model,
            state.clone(),
            &callee.system,
            &callee.step.body,
            &callee_bindings,
            &HashMap::new(),
        )? {
            let result = callee
                .step
                .return_expr
                .as_ref()
                .map(|expr| {
                    eval_expr(
                        &next,
                        expr,
                        Some(&callee.system),
                        &model.system_field_indices,
                        &model.entity_specs,
                        &callee_locals,
                        &HashMap::new(),
                    )
                })
                .transpose()?;
            out.push((next, result, choices));
        }
    }
    Ok(out)
}

fn pattern_supported(pattern: &crate::ir::types::IRPattern) -> bool {
    match pattern {
        crate::ir::types::IRPattern::PWild | crate::ir::types::IRPattern::PVar { .. } => true,
        crate::ir::types::IRPattern::PCtor { name: _, fields } => fields.is_empty(),
        crate::ir::types::IRPattern::POr { left, right } => {
            pattern_supported(left) && pattern_supported(right)
        }
    }
}

fn pattern_matches(value: &ExplicitValue, pattern: &crate::ir::types::IRPattern) -> bool {
    match pattern {
        crate::ir::types::IRPattern::PWild | crate::ir::types::IRPattern::PVar { .. } => true,
        crate::ir::types::IRPattern::PCtor { name, fields } => {
            fields.is_empty()
                && matches!(
                    value,
                    ExplicitValue::Enum { variant, .. } if variant == name
                )
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            pattern_matches(value, left) || pattern_matches(value, right)
        }
    }
}

fn fsm_updates_are_allowed(
    spec: &ExplicitEntitySpec<'_>,
    old_values: &[ExplicitValue],
    update_values: &[(usize, ExplicitValue)],
) -> bool {
    for fsm in &spec.fsm_decls {
        let Some(&field_index) = spec.field_indices.get(&fsm.field) else {
            continue;
        };
        let Some((_, new_value)) = update_values
            .iter()
            .find(|(index, _)| *index == field_index)
        else {
            continue;
        };
        let Some(old_value) = old_values.get(field_index) else {
            continue;
        };
        if old_value == new_value {
            continue;
        }
        let (
            ExplicitValue::Enum {
                enum_name: old_enum,
                variant: old_variant,
            },
            ExplicitValue::Enum {
                enum_name: new_enum,
                variant: new_variant,
            },
        ) = (old_value, new_value)
        else {
            return false;
        };
        if old_enum != &fsm.enum_name || new_enum != &fsm.enum_name {
            return false;
        }
        if !fsm
            .transitions
            .iter()
            .any(|transition| transition.from == *old_variant && transition.to == *new_variant)
        {
            return false;
        }
    }
    true
}

fn transition_value_locals(
    value_locals: &HashMap<String, ExplicitValue>,
    slot_values: &[ExplicitValue],
    spec: &ExplicitEntitySpec<'_>,
    transition_args: &HashMap<String, ExplicitValue>,
) -> HashMap<String, ExplicitValue> {
    let mut locals = value_locals.clone();
    locals.extend(transition_args.clone());
    for (field, value) in spec.fields.iter().zip(slot_values.iter()) {
        locals.insert(field.name.clone(), value.clone());
    }
    locals
}

fn apply_assignment(
    state: &mut ExplicitState,
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<(), String> {
    let IRExpr::BinOp { left, right, .. } = expr else {
        return Err("explicit-state step action must be an assignment equality".to_owned());
    };
    let value = eval_expr(
        state,
        right,
        current_system,
        system_fields,
        entity_specs,
        value_locals,
        slot_locals,
    )?;
    match assignment_target(
        left,
        current_system,
        system_fields,
        entity_specs,
        value_locals,
        slot_locals,
    )? {
        AssignmentTarget::SystemField(index) => {
            state.system_values[index] = value;
        }
        AssignmentTarget::EntityField {
            binding,
            field_index,
        } => {
            state.entity_slots[binding.entity_index][binding.slot].values[field_index] = value;
        }
    }
    Ok(())
}

enum AssignmentTarget {
    SystemField(usize),
    EntityField {
        binding: ExplicitSlotBinding,
        field_index: usize,
    },
}

fn assignment_target(
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<AssignmentTarget, String> {
    let IRExpr::Prime { expr, .. } = expr else {
        return Err(
            "explicit-state assignment target must be a primed system or entity field".to_owned(),
        );
    };

    match expr.as_ref() {
        IRExpr::Var { name, .. } => {
            let index = resolve_system_field_index(name, current_system, system_fields)
                .ok_or_else(|| format!("unknown explicit-state field `{name}`"))?;
            Ok(AssignmentTarget::SystemField(index))
        }
        IRExpr::Field {
            expr: owner, field, ..
        } => {
            let IRExpr::Var { name, .. } = owner.as_ref() else {
                return Err(
                    "explicit-state assignment target must be a primed system or entity field"
                        .to_owned(),
                );
            };
            let binding = if let Some(binding) = slot_locals.get(name) {
                *binding
            } else if let Some(ExplicitValue::SlotRef(selected)) = value_locals.get(name) {
                explicit_slot_binding_for_ref(entity_specs, selected)?
            } else {
                return Err(format!("unknown explicit-state slot binding `{name}`"));
            };
            let spec = &entity_specs[binding.entity_index];
            let field_index = *spec
                .field_indices
                .get(field)
                .ok_or_else(|| format!("unknown explicit-state field `{field}`"))?;
            Ok(AssignmentTarget::EntityField {
                binding,
                field_index,
            })
        }
        _ => Err(
            "explicit-state assignment target must be a primed system or entity field".to_owned(),
        ),
    }
}

fn supports_assignment_target(
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashSet<String>,
    slot_locals: &HashMap<String, usize>,
) -> bool {
    let IRExpr::Prime { expr, .. } = expr else {
        return false;
    };
    match expr.as_ref() {
        IRExpr::Var { name, .. } => {
            resolve_system_field_index(name, current_system, system_fields).is_some()
        }
        IRExpr::Field {
            expr: owner, field, ..
        } => {
            let IRExpr::Var { name, .. } = owner.as_ref() else {
                return false;
            };
            if let Some(entity_index) = slot_locals.get(name) {
                return entity_specs
                    .get(*entity_index)
                    .is_some_and(|spec| spec.field_indices.contains_key(field));
            }
            value_locals.contains(name)
        }
        _ => false,
    }
}

fn supports_state_expr(
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashSet<String>,
    slot_locals: &HashMap<String, usize>,
) -> bool {
    match expr {
        IRExpr::Lit { value, .. } => matches!(value, LitVal::Bool { .. }),
        IRExpr::Ctor { args, .. } => args.is_empty(),
        IRExpr::Var { name, .. } => {
            resolve_system_field_index(name, current_system, system_fields).is_some()
                || value_locals.contains(name)
        }
        IRExpr::Field { expr, field, .. } => match expr.as_ref() {
            IRExpr::Var { name, .. } => {
                slot_locals
                    .get(name)
                    .and_then(|entity_index| entity_specs.get(*entity_index))
                    .is_some_and(|spec| spec.field_indices.contains_key(field))
                    || (value_locals.contains(name)
                        && entity_specs
                            .iter()
                            .any(|spec| spec.field_indices.contains_key(field)))
            }
            _ => false,
        },
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            matches!(
                op.as_str(),
                "==" | "OpEq"
                    | "!="
                    | "OpNEq"
                    | "and"
                    | "&&"
                    | "OpAnd"
                    | "or"
                    | "||"
                    | "OpOr"
                    | "implies"
                    | "=>"
                    | "OpImplies"
            ) && supports_state_expr(
                left,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            ) && supports_state_expr(
                right,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )
        }
        IRExpr::UnOp { op, operand, .. } => {
            matches!(op.as_str(), "not" | "!" | "OpNot")
                && supports_state_expr(
                    operand,
                    current_system,
                    system_fields,
                    entity_specs,
                    value_locals,
                    slot_locals,
                )
        }
        IRExpr::Forall {
            var, domain, body, ..
        }
        | IRExpr::Exists {
            var, domain, body, ..
        } => match domain {
            IRType::Entity { name } if entity_specs.iter().any(|spec| spec.name == *name) => {
                let Some((entity_index, _)) = entity_specs
                    .iter()
                    .enumerate()
                    .find(|(_, spec)| spec.name == *name)
                else {
                    return false;
                };
                let mut nested_slot_locals = slot_locals.clone();
                nested_slot_locals.insert(var.clone(), entity_index);
                supports_state_expr(
                    body,
                    current_system,
                    system_fields,
                    entity_specs,
                    value_locals,
                    &nested_slot_locals,
                )
            }
            _ => false,
        },
        _ => false,
    }
}

fn eval_expr(
    state: &ExplicitState,
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<ExplicitValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Bool { value } => Ok(ExplicitValue::Bool(*value)),
            _ => Err("explicit-state only supports bool literals".to_owned()),
        },
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } if args.is_empty() => Ok(ExplicitValue::Enum {
            enum_name: enum_name.clone(),
            variant: ctor.clone(),
        }),
        IRExpr::Var { name, .. } => {
            if let Some(value) = value_locals.get(name) {
                return Ok(value.clone());
            }
            let index = resolve_system_field_index(name, current_system, system_fields)
                .ok_or_else(|| format!("unknown explicit-state field `{name}`"))?;
            Ok(state.system_values[index].clone())
        }
        IRExpr::Field { expr, field, .. } => {
            let IRExpr::Var { name, .. } = expr.as_ref() else {
                return Err("unsupported field projection in explicit-state fragment".to_owned());
            };
            let binding = if let Some(binding) = slot_locals.get(name) {
                *binding
            } else if let Some(ExplicitValue::SlotRef(selected)) = value_locals.get(name) {
                explicit_slot_binding_for_ref(entity_specs, selected)?
            } else {
                return Err(format!("unknown explicit-state slot binding `{name}`"));
            };
            let spec = &entity_specs[binding.entity_index];
            let field_index = *spec
                .field_indices
                .get(field)
                .ok_or_else(|| format!("unknown explicit-state field `{field}`"))?;
            Ok(state.entity_slots[binding.entity_index][binding.slot].values[field_index].clone())
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let left = eval_expr(
                state,
                left,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )?;
            let right = eval_expr(
                state,
                right,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )?;
            eval_binop(op, left, right)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let value = eval_expr(
                state,
                operand,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )?;
            eval_unop(op, value)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let IRType::Entity { name } = domain else {
                return Err("unsupported quantifier domain in explicit-state fragment".to_owned());
            };
            let Some((entity_index, spec)) = entity_specs
                .iter()
                .enumerate()
                .find(|(_, spec)| spec.name == *name)
            else {
                return Err("unknown explicit-state quantifier entity".to_owned());
            };
            let mut nested_slots = slot_locals.clone();
            for slot in 0..spec.slot_count {
                if !state.entity_slots[entity_index][slot].active {
                    continue;
                }
                nested_slots.insert(var.clone(), ExplicitSlotBinding { entity_index, slot });
                if !eval_bool_with_locals(
                    state,
                    body,
                    current_system,
                    system_fields,
                    entity_specs,
                    value_locals,
                    &nested_slots,
                )? {
                    return Ok(ExplicitValue::Bool(false));
                }
            }
            Ok(ExplicitValue::Bool(true))
        }
        IRExpr::Exists {
            var, domain, body, ..
        } => {
            let IRType::Entity { name } = domain else {
                return Err("unsupported quantifier domain in explicit-state fragment".to_owned());
            };
            let Some((entity_index, spec)) = entity_specs
                .iter()
                .enumerate()
                .find(|(_, spec)| spec.name == *name)
            else {
                return Err("unknown explicit-state quantifier entity".to_owned());
            };
            let mut nested_slots = slot_locals.clone();
            for slot in 0..spec.slot_count {
                if !state.entity_slots[entity_index][slot].active {
                    continue;
                }
                nested_slots.insert(var.clone(), ExplicitSlotBinding { entity_index, slot });
                if eval_bool_with_locals(
                    state,
                    body,
                    current_system,
                    system_fields,
                    entity_specs,
                    value_locals,
                    &nested_slots,
                )? {
                    return Ok(ExplicitValue::Bool(true));
                }
            }
            Ok(ExplicitValue::Bool(false))
        }
        _ => Err("unsupported expression in explicit-state fragment".to_owned()),
    }
}

fn eval_bool_with_locals(
    state: &ExplicitState,
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<bool, String> {
    match eval_expr(
        state,
        expr,
        current_system,
        system_fields,
        entity_specs,
        value_locals,
        slot_locals,
    )? {
        ExplicitValue::Bool(value) => Ok(value),
        other => Err(format!("expected bool expression, found {other:?}")),
    }
}

fn eval_binop(
    op: &str,
    left: ExplicitValue,
    right: ExplicitValue,
) -> Result<ExplicitValue, String> {
    match op {
        "==" | "OpEq" => Ok(ExplicitValue::Bool(left == right)),
        "!=" | "OpNEq" => Ok(ExplicitValue::Bool(left != right)),
        "and" | "&&" | "OpAnd" => Ok(ExplicitValue::Bool(
            expect_bool(left)? && expect_bool(right)?,
        )),
        "or" | "||" | "OpOr" => Ok(ExplicitValue::Bool(
            expect_bool(left)? || expect_bool(right)?,
        )),
        "implies" | "=>" | "OpImplies" => Ok(ExplicitValue::Bool(
            !expect_bool(left)? || expect_bool(right)?,
        )),
        _ => Err(format!("unsupported explicit-state operator `{op}`")),
    }
}

fn eval_unop(op: &str, value: ExplicitValue) -> Result<ExplicitValue, String> {
    match op {
        "not" | "!" | "OpNot" => Ok(ExplicitValue::Bool(!expect_bool(value)?)),
        _ => Err(format!("unsupported explicit-state unary operator `{op}`")),
    }
}

fn expect_bool(value: ExplicitValue) -> Result<bool, String> {
    match value {
        ExplicitValue::Bool(value) => Ok(value),
        other => Err(format!("expected bool, found {other:?}")),
    }
}

fn finite_default_value(field: &IRField) -> Result<ExplicitValue, String> {
    match (&field.ty, field.default.as_ref()) {
        (IRType::Bool, Some(IRExpr::Lit { value: LitVal::Bool { value }, .. })) => {
            Ok(ExplicitValue::Bool(*value))
        }
        (IRType::Bool, None) => Ok(ExplicitValue::Bool(false)),
        (
            IRType::Enum { name, variants },
            Some(IRExpr::Ctor { ctor, args, .. }),
        ) if args.is_empty() && variants.iter().all(|variant| variant.fields.is_empty()) => {
            Ok(ExplicitValue::Enum {
                enum_name: name.clone(),
                variant: ctor.clone(),
            })
        }
        (IRType::Enum { name, variants }, None)
            if variants.iter().all(|variant| variant.fields.is_empty()) =>
        {
            let first = variants
                .first()
                .ok_or_else(|| format!("enum `{name}` has no variants"))?;
            Ok(ExplicitValue::Enum {
                enum_name: name.clone(),
                variant: first.name.clone(),
            })
        }
        (IRType::Identity, None) => Ok(ExplicitValue::Identity("__explicit_identity__".to_owned())),
        _ => Err(format!(
            "unsupported explicit-state field `{}`; only Bool, identity, and fieldless enums with deterministic defaults are supported",
            field.name
        )),
    }
}

fn entity_field_default_value(
    field: &IRField,
    entity_name: &str,
    slot: usize,
) -> Result<ExplicitValue, String> {
    match (&field.ty, field.default.as_ref()) {
        (IRType::Identity, None) => Ok(ExplicitValue::Identity(format!("{entity_name}#{slot}"))),
        _ => finite_default_value(field),
    }
}

fn finite_values_for_type(ty: &IRType) -> Result<Vec<ExplicitValue>, String> {
    match ty {
        IRType::Bool => Ok(vec![ExplicitValue::Bool(false), ExplicitValue::Bool(true)]),
        IRType::Enum { name, variants }
            if variants.iter().all(|variant| variant.fields.is_empty()) =>
        {
            Ok(variants
                .iter()
                .map(|variant| ExplicitValue::Enum {
                    enum_name: name.clone(),
                    variant: variant.name.clone(),
                })
                .collect())
        }
        _ => Err("explicit-state only supports Bool and fieldless-enum step parameters".to_owned()),
    }
}

fn supports_explicit_param_type(ty: &IRType) -> bool {
    matches!(ty, IRType::Entity { .. }) || finite_values_for_type(ty).is_ok()
}

fn ensure_supported_explicit_param_type(ty: &IRType) -> Result<(), String> {
    if supports_explicit_param_type(ty) {
        Ok(())
    } else {
        Err(
            "explicit-state only supports Bool, fieldless-enum, and entity step parameters"
                .to_owned(),
        )
    }
}

fn finite_values_for_param(
    ty: &IRType,
    state: &ExplicitState,
    entity_specs: &[ExplicitEntitySpec<'_>],
) -> Result<Vec<ExplicitValue>, String> {
    match ty {
        IRType::Entity { name } => {
            let Some((entity_index, spec)) = entity_specs
                .iter()
                .enumerate()
                .find(|(_, spec)| spec.name == *name)
            else {
                return Err(format!(
                    "unknown explicit-state entity parameter domain `{name}`"
                ));
            };
            Ok((0..spec.slot_count)
                .filter(|slot| state.entity_slots[entity_index][*slot].active)
                .map(|slot| ExplicitValue::SlotRef(op::EntitySlotRef::new(name.clone(), slot)))
                .collect())
        }
        _ => finite_values_for_type(ty),
    }
}

fn enumerate_param_bindings(
    params: &[IRTransParam],
) -> Result<Vec<HashMap<String, ExplicitValue>>, String> {
    let mut out = vec![HashMap::new()];
    for param in params {
        let domain = finite_values_for_type(&param.ty)?;
        let mut next = Vec::new();
        for bindings in &out {
            for value in &domain {
                let mut extended = bindings.clone();
                extended.insert(param.name.clone(), value.clone());
                next.push(extended);
            }
        }
        out = next;
    }
    Ok(out)
}

fn enumerate_param_bindings_for_state(
    params: &[IRTransParam],
    state: &ExplicitState,
    entity_specs: &[ExplicitEntitySpec<'_>],
) -> Result<Vec<HashMap<String, ExplicitValue>>, String> {
    let mut out = vec![HashMap::new()];
    for param in params {
        let domain = finite_values_for_param(&param.ty, state, entity_specs)?;
        let mut next = Vec::new();
        for bindings in &out {
            for value in &domain {
                let mut extended = bindings.clone();
                extended.insert(param.name.clone(), value.clone());
                next.push(extended);
            }
        }
        out = next;
    }
    Ok(out)
}

fn witness_value(value: &ExplicitValue) -> op::WitnessValue {
    match value {
        ExplicitValue::Bool(value) => op::WitnessValue::Bool(*value),
        ExplicitValue::Enum { enum_name, variant } => op::WitnessValue::EnumVariant {
            enum_name: enum_name.clone(),
            variant: variant.clone(),
        },
        ExplicitValue::Identity(value) => op::WitnessValue::Identity(value.clone()),
        ExplicitValue::SlotRef(slot_ref) => op::WitnessValue::SlotRef(slot_ref.clone()),
    }
}

fn render_tuple_suffix(tuple: &HashMap<String, ExplicitValue>) -> String {
    let mut fields = tuple.iter().collect::<Vec<_>>();
    fields.sort_by(|(left, _), (right, _)| left.cmp(right));
    let rendered = fields
        .into_iter()
        .map(|(name, value)| format!("{name}={}", render_explicit_value(value)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("({rendered})")
}

fn render_choice_suffix(tuple: &[ExplicitChoiceBinding]) -> String {
    if tuple.is_empty() {
        return String::new();
    }
    let parts = tuple
        .iter()
        .map(|binding| {
            format!(
                "{}={}[{}]",
                binding.binder,
                binding.selected.entity(),
                binding.selected.slot()
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("[{parts}]")
}

fn render_explicit_value(value: &ExplicitValue) -> String {
    match value {
        ExplicitValue::Bool(value) => value.to_string(),
        ExplicitValue::Enum { variant, .. } => variant.clone(),
        ExplicitValue::Identity(value) => value.clone(),
        ExplicitValue::SlotRef(slot_ref) => format!("{}#{}", slot_ref.entity(), slot_ref.slot()),
    }
}

fn explicit_slot_binding_for_ref(
    entity_specs: &[ExplicitEntitySpec<'_>],
    selected: &op::EntitySlotRef,
) -> Result<ExplicitSlotBinding, String> {
    let Some((entity_index, _)) = entity_specs
        .iter()
        .enumerate()
        .find(|(_, spec)| spec.name == selected.entity())
    else {
        return Err(format!(
            "unknown explicit-state entity slot reference `{}#{}`",
            selected.entity(),
            selected.slot()
        ));
    };
    Ok(ExplicitSlotBinding {
        entity_index,
        slot: selected.slot(),
    })
}

fn render_explicit_edge_label(edge: &ExplicitEdge) -> String {
    match edge {
        ExplicitEdge::Step {
            system,
            step_name,
            params,
            choices,
        } => {
            let mut parts = Vec::new();
            if !params.is_empty() {
                parts.push(format!(
                    "params({})",
                    params
                        .iter()
                        .map(|binding| {
                            format!("{}={}", binding.name, render_explicit_value(&binding.value))
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            if !choices.is_empty() {
                parts.push(format!(
                    "choices({})",
                    choices
                        .iter()
                        .map(|choice| match choice {
                            op::Choice::Choose { binder, selected } => {
                                format!("{binder}={}#{}", selected.entity(), selected.slot())
                            }
                            op::Choice::ForAll { binder, iterated } => format!(
                                "{binder}=[{}]",
                                iterated
                                    .iter()
                                    .map(|slot| format!("{}#{}", slot.entity(), slot.slot()))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            op::Choice::Create { created } => {
                                format!("create={}#{}", created.entity(), created.slot())
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            if parts.is_empty() {
                format!("{system}::{step_name}")
            } else {
                format!("{system}::{step_name} [{}]", parts.join("; "))
            }
        }
        ExplicitEdge::Stutter => "stutter".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{IRFieldPat, IRPattern, IRVariant};

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn bool_field(name: &str, default: Option<bool>) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Bool,
            default: default.map(bool_lit),
            initial_constraint: None,
        }
    }

    fn enum_type() -> IRType {
        IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        }
    }

    fn enum_ctor(variant: &str) -> IRExpr {
        IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: variant.to_owned(),
            args: vec![],
            span: None,
        }
    }

    fn var(name: &str, ty: IRType) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty,
            span: None,
        }
    }

    fn prime(expr: IRExpr) -> IRExpr {
        IRExpr::Prime {
            expr: Box::new(expr),
            span: None,
        }
    }

    fn bin(op: &str, left: IRExpr, right: IRExpr) -> IRExpr {
        IRExpr::BinOp {
            op: op.to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty: IRType::Bool,
            span: None,
        }
    }

    fn entity_spec() -> ExplicitEntitySpec<'static> {
        let fields = vec![bool_field("active", Some(false))];
        let field_indices = HashMap::from([("active".to_owned(), 0)]);
        ExplicitEntitySpec {
            name: "Task".to_owned(),
            slot_count: 2,
            fields,
            field_indices,
            transitions: HashMap::new(),
            fsm_decls: Vec::new(),
        }
    }

    fn sample_state() -> ExplicitState {
        ExplicitState {
            system_values: vec![ExplicitValue::Bool(false)],
            entity_slots: vec![vec![
                ExplicitEntitySlotState {
                    active: true,
                    values: vec![ExplicitValue::Bool(true)],
                },
                ExplicitEntitySlotState {
                    active: false,
                    values: vec![ExplicitValue::Bool(false)],
                },
            ]],
        }
    }

    fn empty_state() -> ExplicitState {
        ExplicitState {
            system_values: vec![],
            entity_slots: vec![],
        }
    }

    fn leaked_step(name: &str, params: Vec<IRTransParam>) -> &'static IRSystemAction {
        Box::leak(Box::new(IRSystemAction {
            name: name.to_owned(),
            params,
            guard: bool_lit(true),
            body: vec![],
            return_expr: None,
        }))
    }

    fn simple_model<'a>(step: &'a IRSystemAction) -> ExplicitModel<'a> {
        ExplicitModel {
            roots: vec!["Sys".to_owned()],
            system_fields: vec![],
            system_field_indices: HashMap::new(),
            entity_specs: vec![],
            entity_indices: HashMap::new(),
            steps: vec![ExplicitStepRef {
                system: "Sys".to_owned(),
                store_param_count: 0,
                step,
            }],
            step_indices: HashMap::from([(("Sys".to_owned(), step.name.clone()), 0usize)]),
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        }
    }

    #[test]
    fn explicit_finite_defaults_and_param_domains_cover_supported_and_error_paths() {
        assert_eq!(
            finite_default_value(&bool_field("flag", None)).unwrap(),
            ExplicitValue::Bool(false)
        );
        assert_eq!(
            finite_default_value(&bool_field("flag", Some(true))).unwrap(),
            ExplicitValue::Bool(true)
        );
        let enum_field = IRField {
            name: "status".to_owned(),
            ty: enum_type(),
            default: Some(enum_ctor("Closed")),
            initial_constraint: None,
        };
        assert_eq!(
            finite_default_value(&enum_field).unwrap(),
            ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Closed".to_owned()
            }
        );
        let identity_field = IRField {
            name: "id".to_owned(),
            ty: IRType::Identity,
            default: None,
            initial_constraint: None,
        };
        assert_eq!(
            entity_field_default_value(&identity_field, "Task", 3).unwrap(),
            ExplicitValue::Identity("Task#3".to_owned())
        );
        assert!(finite_values_for_type(&IRType::Int).is_err());
        assert!(ensure_supported_explicit_param_type(&IRType::Bool).is_ok());
        assert!(ensure_supported_explicit_param_type(&IRType::Real).is_err());

        let params = vec![
            IRTransParam {
                name: "flag".to_owned(),
                ty: IRType::Bool,
            },
            IRTransParam {
                name: "status".to_owned(),
                ty: enum_type(),
            },
        ];
        let bindings = enumerate_param_bindings(&params).unwrap();
        assert_eq!(bindings.len(), 4);
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_fields_quantifiers_and_errors() {
        let state = sample_state();
        let specs = vec![entity_spec()];
        let system_fields = HashMap::from([
            ("Orders::flag".to_owned(), 0usize),
            ("flag".to_owned(), 0usize),
        ]);
        let value_locals = HashMap::from([("local".to_owned(), ExplicitValue::Bool(true))]);
        let slot_locals = HashMap::from([(
            "task".to_owned(),
            ExplicitSlotBinding {
                entity_index: 0,
                slot: 0,
            },
        )]);
        let value_names = HashSet::from(["local".to_owned()]);
        let slot_names = HashMap::from([("task".to_owned(), 0usize)]);

        assert!(supports_state_expr(
            &var("flag", IRType::Bool),
            Some("Orders"),
            &system_fields,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert!(supports_state_expr(
            &IRExpr::Field {
                expr: Box::new(var(
                    "task",
                    IRType::Entity {
                        name: "Task".to_owned()
                    }
                )),
                field: "active".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            Some("Orders"),
            &system_fields,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert!(!supports_state_expr(
            &IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            },
            Some("Orders"),
            &system_fields,
            &specs,
            &value_names,
            &slot_names,
        ));

        let field_value = eval_expr(
            &state,
            &IRExpr::Field {
                expr: Box::new(var(
                    "task",
                    IRType::Entity {
                        name: "Task".to_owned(),
                    },
                )),
                field: "active".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            Some("Orders"),
            &system_fields,
            &specs,
            &value_locals,
            &slot_locals,
        )
        .unwrap();
        assert_eq!(field_value, ExplicitValue::Bool(true));

        let forall_active = IRExpr::Forall {
            var: "t".to_owned(),
            domain: IRType::Entity {
                name: "Task".to_owned(),
            },
            body: Box::new(IRExpr::Field {
                expr: Box::new(var(
                    "t",
                    IRType::Entity {
                        name: "Task".to_owned(),
                    },
                )),
                field: "active".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };
        assert_eq!(
            eval_expr(
                &state,
                &forall_active,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &HashMap::new(),
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert!(eval_expr(
            &state,
            &var("missing", IRType::Bool),
            Some("Orders"),
            &system_fields,
            &specs,
            &value_locals,
            &slot_locals,
        )
        .is_err());
    }

    #[test]
    fn explicit_assignment_targets_and_application_update_state() {
        let mut state = sample_state();
        let specs = vec![entity_spec()];
        let system_fields = HashMap::from([
            ("Orders::flag".to_owned(), 0usize),
            ("flag".to_owned(), 0usize),
        ]);
        let value_locals = HashMap::new();
        let slot_locals = HashMap::from([(
            "task".to_owned(),
            ExplicitSlotBinding {
                entity_index: 0,
                slot: 0,
            },
        )]);

        apply_assignment(
            &mut state,
            &bin("OpEq", prime(var("flag", IRType::Bool)), bool_lit(true)),
            Some("Orders"),
            &system_fields,
            &specs,
            &value_locals,
            &slot_locals,
        )
        .unwrap();
        assert_eq!(state.system_values[0], ExplicitValue::Bool(true));

        apply_assignment(
            &mut state,
            &bin(
                "OpEq",
                prime(IRExpr::Field {
                    expr: Box::new(var(
                        "task",
                        IRType::Entity {
                            name: "Task".to_owned(),
                        },
                    )),
                    field: "active".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                bool_lit(false),
            ),
            Some("Orders"),
            &system_fields,
            &specs,
            &value_locals,
            &slot_locals,
        )
        .unwrap();
        assert_eq!(
            state.entity_slots[0][0].values[0],
            ExplicitValue::Bool(false)
        );

        assert!(apply_assignment(
            &mut state,
            &bool_lit(true),
            Some("Orders"),
            &system_fields,
            &specs,
            &value_locals,
            &slot_locals,
        )
        .is_err());
    }

    #[test]
    fn explicit_patterns_rendering_and_scc_helpers_cover_branchy_paths() {
        let ctor = IRPattern::PCtor {
            name: "Open".to_owned(),
            fields: vec![],
        };
        let unsupported_ctor = IRPattern::PCtor {
            name: "Open".to_owned(),
            fields: vec![IRFieldPat {
                name: "value".to_owned(),
                pattern: IRPattern::PWild,
            }],
        };
        assert!(pattern_supported(&IRPattern::POr {
            left: Box::new(IRPattern::PWild),
            right: Box::new(ctor.clone()),
        }));
        assert!(!pattern_supported(&unsupported_ctor));
        assert!(pattern_matches(
            &ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Open".to_owned()
            },
            &ctor
        ));
        assert!(!pattern_matches(
            &ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Closed".to_owned()
            },
            &ctor
        ));

        let tuple = HashMap::from([
            ("b".to_owned(), ExplicitValue::Bool(false)),
            ("a".to_owned(), ExplicitValue::Identity("id".to_owned())),
        ]);
        assert_eq!(render_tuple_suffix(&tuple), "(a=id, b=false)");
        assert_eq!(render_choice_suffix(&[]), "");
        assert_eq!(
            render_choice_suffix(&[ExplicitChoiceBinding {
                binder: "x".to_owned(),
                selected: op::EntitySlotRef::new("Task", 1)
            }]),
            "[x=Task[1]]"
        );

        let adjacency = vec![
            vec![(1, ExplicitEdge::Stutter)],
            vec![(0, ExplicitEdge::Stutter), (2, ExplicitEdge::Stutter)],
            vec![],
        ];
        let subset = HashSet::from([0usize, 1usize, 2usize]);
        let components = strongly_connected_components(&adjacency, &subset);
        assert!(components
            .iter()
            .any(|component| component == &HashSet::from([0, 1])));
        assert!(components
            .iter()
            .any(|component| component == &HashSet::from([2])));
    }

    #[test]
    fn explicit_edge_labels_include_params_choices_and_stutter() {
        let label = render_explicit_edge_label(&ExplicitEdge::Step {
            system: "Orders".to_owned(),
            step_name: "advance".to_owned(),
            params: vec![ExplicitParamBinding {
                name: "flag".to_owned(),
                value: ExplicitValue::Bool(true),
            }],
            choices: vec![
                op::Choice::Choose {
                    binder: "task".to_owned(),
                    selected: op::EntitySlotRef::new("Task", 0),
                },
                op::Choice::ForAll {
                    binder: "each".to_owned(),
                    iterated: vec![op::EntitySlotRef::new("Task", 1)],
                },
                op::Choice::Create {
                    created: op::EntitySlotRef::new("Task", 2),
                },
            ],
        });
        assert!(label.contains("Orders::advance"));
        assert!(label.contains("params(flag=true)"));
        assert!(label.contains("task=Task#0"));
        assert!(label.contains("each=[Task#1]"));
        assert!(label.contains("create=Task#2"));
        assert_eq!(
            render_explicit_edge_label(&ExplicitEdge::Stutter),
            "stutter"
        );
    }

    #[test]
    fn explicit_model_fairness_helpers_cover_key_tuple_and_choice_paths() {
        let step = leaked_step(
            "go",
            vec![IRTransParam {
                name: "flag".to_owned(),
                ty: IRType::Bool,
            }],
        );
        let mut model = simple_model(step);
        let state = empty_state();

        assert!(model.system_is_scheduled("Sys"));
        assert!(!model.system_is_scheduled("Other"));
        assert!(model.step_enabled_by_key(&state, "Sys", "go").unwrap());
        assert!(!model.step_enabled_by_key(&state, "Other", "go").unwrap());

        model.per_tuple_fair = vec![("Sys".to_owned(), "go".to_owned())];
        let tuples = model.fair_param_tuples("Sys", "go").unwrap().unwrap();
        assert_eq!(tuples.len(), 2);
        assert!(model.fair_param_tuples("Sys", "missing").unwrap().is_none());
        model.per_tuple_fair.clear();

        let fired_edge = ExplicitEdge::Step {
            system: "Sys".to_owned(),
            step_name: "go".to_owned(),
            params: vec![ExplicitParamBinding {
                name: "flag".to_owned(),
                value: ExplicitValue::Bool(true),
            }],
            choices: vec![op::Choice::Choose {
                binder: "picked".to_owned(),
                selected: op::EntitySlotRef::new("Task", 0),
            }],
        };
        let tuple = HashMap::from([("flag".to_owned(), ExplicitValue::Bool(true))]);
        assert!(model.edge_fired_tuple(&fired_edge, "Sys", "go", &tuple));
        assert!(!model.edge_fired_tuple(&ExplicitEdge::Stutter, "Sys", "go", &tuple));

        let choice_tuple = model
            .edge_choice_tuple(&fired_edge, "Sys", "go")
            .expect("choose edge should expose a choice tuple");
        assert!(model.edge_fired_choice_tuple(&fired_edge, "Sys", "go", &choice_tuple));
        assert_eq!(
            model
                .fair_choice_tuples_in_cycle(&[vec![(0, fired_edge.clone())]], &[0], "Sys", "go")
                .len(),
            1
        );

        model.weak_fair = vec![("Sys".to_owned(), "go".to_owned())];
        model.strong_fair = vec![("Sys".to_owned(), "go".to_owned())];
        let nodes = vec![ExplicitProductState {
            state,
            monitors: vec![],
        }];
        let adjacency = vec![vec![(0, fired_edge.clone())]];
        let fairness = model
            .evaluate_fair_cycle(&nodes, &adjacency, &[0], &[fired_edge])
            .unwrap()
            .expect("fired self-loop satisfies weak and strong fairness");
        assert_eq!(fairness.len(), 2);
        assert!(fairness
            .iter()
            .all(|analysis| analysis.status == FairnessStatus::EnabledAndFired));
    }
}
