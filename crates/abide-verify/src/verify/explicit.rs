//! Narrow explicit-state backend for finite transition fragments.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
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

use super::context::{EntityInfo, VerifyContext};
use super::defenv;
use super::transition;
use super::{
    build_assumptions_for_system_scope, verification_timeout_hint, DeadlockEventDiag,
    FairnessEventAnalysis, FairnessKind, FairnessStatus, VerificationResult,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ExplicitValue {
    Bool(bool),
    Enum {
        enum_name: String,
        variant: String,
        fields: Vec<(String, ExplicitValue)>,
    },
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

fn resolve_system_field_type<'a>(
    name: &str,
    current_system: Option<&str>,
    system_field_types: &'a HashMap<String, IRType>,
) -> Option<&'a IRType> {
    if let Some(system) = current_system {
        let qualified = qualified_system_field_name(system, name);
        if let Some(ty) = system_field_types.get(&qualified) {
            return Some(ty);
        }
    }
    system_field_types.get(name)
}

fn field_types_with_params(
    base: &HashMap<String, IRType>,
    params: &[IRTransParam],
) -> HashMap<String, IRType> {
    let mut out = base.clone();
    out.extend(
        params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone())),
    );
    out
}

fn field_types_with_params_and_fields(
    base: &HashMap<String, IRType>,
    params: &[IRTransParam],
    fields: &[IRField],
) -> HashMap<String, IRType> {
    let mut out = field_types_with_params(base, params);
    out.extend(fields.iter().map(|field| (field.name.clone(), field.ty.clone())));
    out
}

impl<'a> ExplicitModel<'a> {
    fn system_is_scheduled(&self, system: &str) -> bool {
        self.roots.iter().any(|root| root == system)
    }

    fn from_obligation(
        obligation: &'a transition::TransitionVerifyObligation<'a>,
        vctx: &VerifyContext,
    ) -> Result<Option<(Self, Vec<ExplicitState>)>, String> {
        let system = obligation.system();

        let mut system_fields = Vec::new();
        let mut system_field_indices = HashMap::new();
        let mut system_field_types = HashMap::new();
        let mut initial_system_values = Vec::new();
        let mut entity_specs = Vec::new();
        let mut entity_indices = HashMap::new();
        for entity in system.relevant_entities() {
            let Some(&slot_count) = system.slots_per_entity().get(entity.name.as_str()) else {
                continue;
            };
            let spec = build_entity_spec(entity, slot_count, vctx.entities.get(&entity.name))?;
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
                system_field_types.insert(
                    qualified_system_field_name(&sys.name, &field.name),
                    field.ty.clone(),
                );
                if !ambiguous_field_names.contains(&field.name) {
                    if system_field_indices.contains_key(&field.name) {
                        system_field_indices.remove(&field.name);
                        system_field_types.remove(&field.name);
                        ambiguous_field_names.insert(field.name.clone());
                    } else {
                        system_field_indices.insert(field.name.clone(), idx);
                        system_field_types.insert(field.name.clone(), field.ty.clone());
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
            let step_field_types = field_types_with_params(&system_field_types, &step.step.params);
            let final_locals = validate_actions(
                &step.step.body,
                &step.system,
                &system_field_indices,
                &step_field_types,
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
                    &step_field_types,
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
                    &system_field_types,
                    &entity_specs,
                    &HashSet::new(),
                    &static_slot_locals,
                ) || !supports_state_expr(
                    &response,
                    None,
                    &system_field_indices,
                    &system_field_types,
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
                &system_field_types,
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
                &system_field_types,
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
            let step_field_types = field_types_with_params(&system_field_types, &step.step.params);
            if !supports_state_expr(
                &step.step.guard,
                Some(&step.system),
                &system_field_indices,
                &step_field_types,
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
                &step_field_types,
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
                    &step_field_types,
                    &entity_specs,
                    &final_locals,
                    &HashMap::new(),
                ) {
                    return Ok(None);
                }
            }
        }

        let mut active_slots: HashMap<(usize, usize), bool> = HashMap::new();
        for range in system.store_ranges().values() {
            if range.max_active != range.slot_count {
                return Ok(None);
            }
            let Some(&entity_index) = entity_indices.get(&range.entity_type) else {
                continue;
            };
            for slot in range.start_slot..range.start_slot + range.min_active {
                active_slots.insert((entity_index, slot), true);
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
        let initial_states =
            enumerate_initial_states(&model.entity_specs, &active_slots, initial_system_values)?
                .into_iter()
                .filter(|state| {
                    model
                        .state_satisfies_extern_assumptions(state)
                        .unwrap_or(false)
                })
                .collect::<Vec<_>>();
        if initial_states.is_empty() {
            return Ok(None);
        }

        Ok(Some((model, initial_states)))
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
    let (model, initial_states) = match ExplicitModel::from_obligation(&obligation, &vctx)? {
        Some(pair) => pair,
        None => return Ok(None),
    };

    let deadline = super::verification_deadline(config);
    let depth_bound = verify_block.depth;
    let mut nodes = initial_states;
    let mut depths = vec![0usize; nodes.len()];
    let mut seen: HashMap<ExplicitState, usize> = nodes
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, state)| (state, index))
        .collect();
    let mut queue = (0..nodes.len()).collect::<VecDeque<_>>();
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
    let obligation =
        transition::TransitionVerifyObligation::for_verify(ir, vctx, verify_block, defs)?;
    let (model, initial_states) = match ExplicitModel::from_obligation(&obligation, vctx) {
        Ok(Some(model)) => model,
        Ok(None) => return None,
        Err(err) if err.contains("unsupported explicit-state finite enum payload expression") => {
            return Some(VerificationResult::Unprovable {
                name: verify_block.name.clone(),
                hint: err,
                span: verify_block.span,
                file: verify_block.file.clone(),
            });
        }
        Err(_) => return None,
    };

    let started = Instant::now();
    let assumptions =
        build_assumptions_for_system_scope(ir, &model.roots, &verify_block.assumption_set, &[]);

    let mut nodes = initial_states
        .into_iter()
        .map(|state| ExplicitProductState {
            state,
            monitors: vec![MonitorStatus::Idle; model.liveness_monitors.len()],
        })
        .collect::<Vec<_>>();
    let mut parents: Vec<Option<(usize, ExplicitEdge)>> = vec![None; nodes.len()];
    let mut adjacency: Vec<Vec<(usize, ExplicitEdge)>> = vec![Vec::new(); nodes.len()];
    let mut seen: HashMap<ExplicitProductState, usize> = nodes
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, state)| (state, index))
        .collect();
    let mut queue = (0..nodes.len()).collect::<VecDeque<_>>();

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

fn enumerate_initial_states(
    entity_specs: &[ExplicitEntitySpec<'_>],
    active_slots: &HashMap<(usize, usize), bool>,
    system_values: Vec<ExplicitValue>,
) -> Result<Vec<ExplicitState>, String> {
    let mut states = vec![ExplicitState {
        system_values,
        entity_slots: vec![Vec::new(); entity_specs.len()],
    }];

    for (entity_index, spec) in entity_specs.iter().enumerate() {
        for slot in 0..spec.slot_count {
            let active = active_slots.contains_key(&(entity_index, slot));
            let mut slot_options = enumerate_slot_initial_values(spec, slot)?;
            if !active {
                slot_options.truncate(1);
            }
            let mut next_states = Vec::new();
            for state in &states {
                for values in &slot_options {
                    let mut next = state.clone();
                    next.entity_slots[entity_index].push(ExplicitEntitySlotState {
                        active,
                        values: values.clone(),
                    });
                    next_states.push(next);
                }
            }
            states = next_states;
        }
    }

    Ok(states)
}

fn enumerate_slot_initial_values(
    spec: &ExplicitEntitySpec<'_>,
    slot: usize,
) -> Result<Vec<Vec<ExplicitValue>>, String> {
    let mut out = vec![Vec::new()];
    for field in &spec.fields {
        let values = field_initial_values(field, &spec.name, slot)?;
        let mut next = Vec::new();
        for prefix in &out {
            for value in &values {
                let mut extended = prefix.clone();
                extended.push(value.clone());
                next.push(extended);
            }
        }
        out = next;
    }
    Ok(out)
}

fn field_initial_values(
    field: &IRField,
    entity_name: &str,
    slot: usize,
) -> Result<Vec<ExplicitValue>, String> {
    let Some(initial_constraint) = &field.initial_constraint else {
        return Ok(vec![entity_field_default_value(field, entity_name, slot)?]);
    };
    let candidates = finite_values_for_type(&field.ty)?;
    let accepted = field_values_satisfying_constraint(initial_constraint, candidates)?;
    if accepted.is_empty() {
        return Err(format!(
            "explicit-state initial constraint for field `{}` has no finite values",
            field.name
        ));
    }
    Ok(accepted)
}

fn field_create_values(
    field: &IRField,
    entity_name: &str,
    slot: usize,
    provided: Option<ExplicitValue>,
) -> Result<Vec<ExplicitValue>, String> {
    let candidates = match provided {
        Some(value) => vec![value],
        None => field_initial_values(field, entity_name, slot)?,
    };
    let Some(initial_constraint) = &field.initial_constraint else {
        return Ok(candidates);
    };
    field_values_satisfying_constraint(initial_constraint, candidates)
}

fn field_values_satisfying_constraint(
    initial_constraint: &IRExpr,
    candidates: Vec<ExplicitValue>,
) -> Result<Vec<ExplicitValue>, String> {
    let empty_state = ExplicitState {
        system_values: vec![],
        entity_slots: vec![],
    };
    let mut accepted = Vec::new();
    for candidate in candidates {
        let value_locals = HashMap::from([("$".to_owned(), candidate.clone())]);
        if eval_bool_with_locals(
            &empty_state,
            initial_constraint,
            None,
            &HashMap::new(),
            &[],
            &value_locals,
            &HashMap::new(),
        )? {
            accepted.push(candidate);
        }
    }
    Ok(accepted)
}

fn build_entity_spec<'a>(
    entity: &'a IREntity,
    slot_count: usize,
    entity_info: Option<&EntityInfo>,
) -> Result<ExplicitEntitySpec<'a>, String> {
    let fields = entity
        .fields
        .iter()
        .map(|field| {
            let mut field = field.clone();
            if let Some(default) = entity_info
                .and_then(|info| info.fields.iter().find(|item| item.name == field.name))
                .and_then(|info| info.default_expr())
            {
                field.default = Some(default.clone());
            }
            field
        })
        .collect::<Vec<_>>();
    let mut field_indices = HashMap::new();
    for (index, field) in fields.iter().enumerate() {
        if let Some(initial_constraint) = &field.initial_constraint {
            finite_values_for_type(&field.ty)?;
            let value_locals = HashSet::from(["$".to_owned()]);
            let initial_constraint_field_types =
                HashMap::from([("$".to_owned(), field.ty.clone())]);
            if !supports_state_expr(
                initial_constraint,
                None,
                &HashMap::new(),
                &initial_constraint_field_types,
                &[],
                &value_locals,
                &HashMap::new(),
            ) {
                return Err(format!(
                    "unsupported explicit-state initial constraint for entity field `{}`",
                    field.name
                ));
            }
        } else {
            finite_default_value(field)?;
        }
        field_indices.insert(field.name.clone(), index);
    }
    let mut transitions = HashMap::new();
    for transition in &entity.transitions {
        for param in &transition.params {
            ensure_supported_explicit_param_type(&param.ty)?;
        }
        transitions.insert(transition.name.clone(), transition);
    }
    Ok(ExplicitEntitySpec {
        name: entity.name.clone(),
        slot_count,
        fields,
        field_indices,
        transitions,
        fsm_decls: entity.fsm_decls.clone(),
    })
}

fn validate_actions(
    actions: &[IRAction],
    current_system: &str,
    system_fields: &HashMap<String, usize>,
    system_field_types: &HashMap<String, IRType>,
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
            system_field_types,
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
    system_field_types: &HashMap<String, IRType>,
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
                system_field_types,
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
                        system_field_types,
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
                system_field_types,
                entity_specs,
                value_locals,
                &nested_slot_locals,
            ) {
                return Err("unsupported choose filter in explicit-state fragment".to_owned());
            }
            validate_actions(
                ops,
                current_system,
                system_fields,
                system_field_types,
                entity_specs,
                steps,
                step_indices,
                value_locals,
                &nested_slot_locals,
                active_calls,
            )?;
            Ok(value_locals.clone())
        }
        IRAction::ForAll { var, entity, ops } => {
            let Some((entity_index, _)) = entity_specs
                .iter()
                .enumerate()
                .find(|(_, candidate)| candidate.name == *entity)
            else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            let mut nested_slot_locals = slot_locals.clone();
            nested_slot_locals.insert(var.clone(), entity_index);
            validate_actions(
                ops,
                current_system,
                system_fields,
                system_field_types,
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
                system_field_types,
                entity_specs,
                steps,
                step_indices,
                value_locals,
                slot_locals,
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
            if !slot_locals.contains_key(target)
                && step_indices.contains_key(&(target.clone(), transition.clone()))
            {
                validate_cross_call_like(
                    target,
                    transition,
                    refs,
                    args,
                    Some(current_system),
                    system_fields,
                    system_field_types,
                    entity_specs,
                    steps,
                    step_indices,
                    value_locals,
                    slot_locals,
                    active_calls,
                )?;
                return Ok(value_locals.clone());
            };
            let Some(spec) = entity_spec_for_binding_or_value_local(
                entity_specs,
                slot_locals,
                system_field_types,
                value_locals,
                target,
            ) else {
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
            let transition_field_types =
                field_types_with_params_and_fields(system_field_types, &trans.params, &spec.fields);
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
                        &transition_field_types,
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
                &transition_field_types,
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
                        &transition_field_types,
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
            if let Some(postcondition) = &trans.postcondition {
                if !supports_state_expr(
                    postcondition,
                    Some(current_system),
                    system_fields,
                    &transition_field_types,
                    entity_specs,
                    &transition_value_locals,
                    &transition_slot_locals,
                ) {
                    return Err(
                        "unsupported transition postcondition in explicit-state fragment"
                            .to_owned(),
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
                system_field_types,
                entity_specs,
                steps,
                step_indices,
                value_locals,
                slot_locals,
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
                        system_field_types,
                        entity_specs,
                        steps,
                        step_indices,
                        value_locals,
                        slot_locals,
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
                let arm_value_locals = pattern_value_local_names(value_locals, &arm.pattern);
                if let Some(guard) = &arm.guard {
                    if !supports_state_expr(
                        guard,
                        Some(current_system),
                        system_fields,
                        system_field_types,
                        entity_specs,
                        &arm_value_locals,
                        slot_locals,
                    ) {
                        return Err("unsupported match guard in explicit-state fragment".to_owned());
                    }
                }
                validate_actions(
                    &arm.body,
                    current_system,
                    system_fields,
                    system_field_types,
                    entity_specs,
                    steps,
                    step_indices,
                    &arm_value_locals,
                    slot_locals,
                    active_calls,
                )?;
            }
            Ok(value_locals.clone())
        }
    }
}

fn validate_cross_call_like(
    system: &str,
    command: &str,
    refs: &[String],
    args: &[IRExpr],
    caller_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    system_field_types: &HashMap<String, IRType>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    steps: &[ExplicitStepRef<'_>],
    step_indices: &HashMap<(String, String), usize>,
    value_locals: &HashSet<String>,
    slot_locals: &HashMap<String, usize>,
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
    let callee_field_types = field_types_with_params(system_field_types, &callee.step.params);
    for (arg, param) in args.iter().zip(&callee.step.params) {
        if !supports_explicit_param_type(&param.ty)
            || !supports_state_expr(
                arg,
                caller_system,
                system_fields,
                system_field_types,
                entity_specs,
                value_locals,
                slot_locals,
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
        &callee_field_types,
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
        &callee_field_types,
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
            &callee_field_types,
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

fn entity_spec_for_binding_or_value_local<'a>(
    entity_specs: &'a [ExplicitEntitySpec<'a>],
    slot_locals: &HashMap<String, usize>,
    system_field_types: &HashMap<String, IRType>,
    value_locals: &HashSet<String>,
    target: &str,
) -> Option<&'a ExplicitEntitySpec<'a>> {
    entity_spec_for_binding(entity_specs, slot_locals, target).or_else(|| {
        if !value_locals.contains(target) {
            return None;
        }
        let Some(IRType::Entity { name }) = system_field_types.get(target) else {
            return None;
        };
        entity_specs.iter().find(|spec| spec.name == *name)
    })
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
            for field in fields {
                if !spec.field_indices.contains_key(&field.name) {
                    return Err(format!("unknown explicit-state field `{}`", field.name));
                }
            }
            let mut out = Vec::new();
            for slot in 0..spec.slot_count {
                if state.entity_slots[entity_index][slot].active {
                    continue;
                }
                let mut value_options = vec![Vec::new()];
                for spec_field in &spec.fields {
                    let provided = fields
                        .iter()
                        .find(|field| field.name == spec_field.name)
                        .map(|field| {
                            eval_expr(
                                &state,
                                &field.value,
                                Some(current_system),
                                &model.system_field_indices,
                                &model.entity_specs,
                                value_locals,
                                slot_locals,
                            )
                        })
                        .transpose()?;
                    let values = field_create_values(spec_field, &spec.name, slot, provided)?;
                    let mut next_options = Vec::new();
                    for prefix in &value_options {
                        for value in &values {
                            let mut extended = prefix.clone();
                            extended.push(value.clone());
                            next_options.push(extended);
                        }
                    }
                    value_options = next_options;
                    if value_options.is_empty() {
                        break;
                    }
                }
                for values in value_options {
                    let mut next = state.clone();
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
        IRAction::ForAll { var, entity, ops } => {
            let Some(&entity_index) = model.entity_indices.get(entity) else {
                return Err(format!("unknown explicit-state entity `{entity}`"));
            };
            let iterated = (0..model.entity_specs[entity_index].slot_count)
                .filter(|slot| state.entity_slots[entity_index][*slot].active)
                .map(|slot| op::EntitySlotRef::new(entity.clone(), slot))
                .collect::<Vec<_>>();
            let mut frontier = vec![(state, value_locals.clone(), Vec::new())];
            for selected in &iterated {
                let mut next_frontier = Vec::new();
                for (frontier_state, frontier_locals, frontier_choices) in frontier {
                    let mut nested_slots = slot_locals.clone();
                    nested_slots.insert(
                        var.clone(),
                        ExplicitSlotBinding {
                            entity_index,
                            slot: selected.slot(),
                        },
                    );
                    for (next, nested_locals, mut choices) in execute_actions(
                        model,
                        frontier_state,
                        current_system,
                        ops,
                        &frontier_locals,
                        &nested_slots,
                    )? {
                        let mut all_choices = frontier_choices.clone();
                        all_choices.append(&mut choices);
                        next_frontier.push((next, nested_locals, all_choices));
                    }
                }
                frontier = next_frontier;
                if frontier.is_empty() {
                    return Ok(Vec::new());
                }
            }
            Ok(frontier
                .into_iter()
                .map(|(next, locals, choices)| {
                    let mut all_choices = vec![op::Choice::ForAll {
                        binder: var.clone(),
                        iterated: iterated.clone(),
                    }];
                    all_choices.extend(choices);
                    (next, locals, all_choices)
                })
                .collect())
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
                slot_locals,
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
            if !slot_locals.contains_key(target) && model.step_by_key(target, transition).is_some()
            {
                return execute_cross_call_like(
                    model,
                    state,
                    target,
                    transition,
                    refs,
                    args,
                    Some(current_system),
                    value_locals,
                    slot_locals,
                );
            }
            let binding = if let Some(binding) = slot_locals.get(target) {
                *binding
            } else if let Some(ExplicitValue::SlotRef(selected)) = value_locals.get(target) {
                explicit_slot_binding_for_ref(&model.entity_specs, selected)?
            } else {
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
            if let Some(postcondition) = &trans.postcondition {
                let post_locals = transition_value_locals(
                    value_locals,
                    next.entity_slots[binding.entity_index][binding.slot]
                        .values
                        .as_slice(),
                    spec,
                    &transition_args,
                );
                if !eval_bool_with_locals(
                    &next,
                    postcondition,
                    Some(current_system),
                    &model.system_field_indices,
                    &model.entity_specs,
                    &post_locals,
                    &transition_slot_locals,
                )? {
                    return Ok(Vec::new());
                }
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
            slot_locals,
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
                        slot_locals,
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
                    let arm_value_locals =
                        pattern_value_locals(value_locals, &arm.pattern, &scrutinee_value);
                    if let Some(guard) = &arm.guard {
                        if !eval_bool_with_locals(
                            &branch_state,
                            guard,
                            Some(current_system),
                            &model.system_field_indices,
                            &model.entity_specs,
                            &arm_value_locals,
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
                        &arm_value_locals,
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
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
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
        slot_locals,
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
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
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
                        slot_locals,
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
        crate::ir::types::IRPattern::PCtor { name: _, fields } => {
            fields.iter().all(|field| pattern_supported(&field.pattern))
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            pattern_supported(left) && pattern_supported(right)
        }
    }
}

fn pattern_matches(value: &ExplicitValue, pattern: &crate::ir::types::IRPattern) -> bool {
    match pattern {
        crate::ir::types::IRPattern::PWild | crate::ir::types::IRPattern::PVar { .. } => true,
        crate::ir::types::IRPattern::PCtor { name, fields } => {
            let ExplicitValue::Enum {
                variant,
                fields: value_fields,
                ..
            } = value
            else {
                return false;
            };
            variant == name
                && fields.iter().all(|field_pat| {
                    value_fields
                        .iter()
                        .find(|(field_name, _)| field_name == &field_pat.name)
                        .is_some_and(|(_, field_value)| {
                            pattern_matches(field_value, &field_pat.pattern)
                        })
                })
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            pattern_matches(value, left) || pattern_matches(value, right)
        }
    }
}

fn pattern_value_local_names(
    value_locals: &HashSet<String>,
    pattern: &crate::ir::types::IRPattern,
) -> HashSet<String> {
    let mut out = value_locals.clone();
    collect_pattern_value_local_names(pattern, &mut out);
    out
}

fn collect_pattern_value_local_names(
    pattern: &crate::ir::types::IRPattern,
    out: &mut HashSet<String>,
) {
    match pattern {
        crate::ir::types::IRPattern::PVar { name } => {
            out.insert(name.clone());
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            collect_pattern_value_local_names(left, out);
            collect_pattern_value_local_names(right, out);
        }
        crate::ir::types::IRPattern::PCtor { fields, .. } => {
            for field in fields {
                collect_pattern_value_local_names(&field.pattern, out);
            }
        }
        crate::ir::types::IRPattern::PWild => {}
    }
}

fn pattern_value_locals(
    value_locals: &HashMap<String, ExplicitValue>,
    pattern: &crate::ir::types::IRPattern,
    value: &ExplicitValue,
) -> HashMap<String, ExplicitValue> {
    let mut out = value_locals.clone();
    bind_pattern_value_locals(pattern, value, &mut out);
    out
}

fn bind_pattern_value_locals(
    pattern: &crate::ir::types::IRPattern,
    value: &ExplicitValue,
    out: &mut HashMap<String, ExplicitValue>,
) {
    match pattern {
        crate::ir::types::IRPattern::PVar { name } => {
            out.insert(name.clone(), value.clone());
        }
        crate::ir::types::IRPattern::POr { left, right } => {
            bind_pattern_value_locals(left, value, out);
            bind_pattern_value_locals(right, value, out);
        }
        crate::ir::types::IRPattern::PCtor { fields, .. } => {
            let ExplicitValue::Enum {
                fields: value_fields,
                ..
            } = value
            else {
                return;
            };
            for field in fields {
                if let Some((_, field_value)) = value_fields
                    .iter()
                    .find(|(field_name, _)| field_name == &field.name)
                {
                    bind_pattern_value_locals(&field.pattern, field_value, out);
                }
            }
        }
        crate::ir::types::IRPattern::PWild => {}
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
                ..
            },
            ExplicitValue::Enum {
                enum_name: new_enum,
                variant: new_variant,
                ..
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

fn explicit_expr_type(expr: &IRExpr) -> Option<&IRType> {
    match expr {
        IRExpr::Lit { ty, .. }
        | IRExpr::Var { ty, .. }
        | IRExpr::BinOp { ty, .. }
        | IRExpr::UnOp { ty, .. }
        | IRExpr::Field { ty, .. }
        | IRExpr::App { ty, .. }
        | IRExpr::Choose { ty, .. }
        | IRExpr::Lam { param_type: ty, .. } => Some(ty),
        IRExpr::IfElse { then_body: body, .. }
        | IRExpr::Let { body, .. }
        | IRExpr::Prime { expr: body, .. } => explicit_expr_type(body),
        IRExpr::Match { arms, .. } => arms.first().and_then(|arm| explicit_expr_type(&arm.body)),
        IRExpr::Ctor { .. } => None,
        _ => None,
    }
}

fn enum_payload_type_has_field(ty: &IRType, field: &str) -> bool {
    matches!(
        ty,
        IRType::Enum { variants, .. }
            if variants
                .iter()
                .any(|variant| variant.fields.iter().any(|payload| payload.name == field))
    )
}

fn fieldless_enum_variant_value(
    variant_name: &str,
    entity_specs: &[ExplicitEntitySpec<'_>],
) -> Option<ExplicitValue> {
    let mut matches = entity_specs
        .iter()
        .flat_map(|spec| spec.fields.iter())
        .filter_map(|field| {
            let IRType::Enum { name, variants } = &field.ty else {
                return None;
            };
            variants
                .iter()
                .find(|variant| variant.name == variant_name && variant.fields.is_empty())
                .map(|variant| ExplicitValue::Enum {
                    enum_name: name.clone(),
                    variant: variant.name.clone(),
                    fields: vec![],
                })
        });
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn fieldless_enum_variant_value_for_type(
    variant_name: &str,
    expected_ty: Option<&IRType>,
) -> Option<ExplicitValue> {
    let Some(IRType::Enum { name, variants }) = expected_ty else {
        return None;
    };
    variants
        .iter()
        .find(|variant| variant.name == variant_name && variant.fields.is_empty())
        .map(|variant| ExplicitValue::Enum {
            enum_name: name.clone(),
            variant: variant.name.clone(),
            fields: vec![],
        })
}

fn supports_state_expr(
    expr: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    system_field_types: &HashMap<String, IRType>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashSet<String>,
    slot_locals: &HashMap<String, usize>,
) -> bool {
    match expr {
        IRExpr::Lit { value, .. } => matches!(value, LitVal::Bool { .. }),
        IRExpr::Ctor { args, .. } => args.iter().all(|(_, arg)| {
            supports_state_expr(
                arg,
                current_system,
                system_fields,
                system_field_types,
                entity_specs,
                value_locals,
                slot_locals,
            )
        }),
        IRExpr::Var { name, .. } => {
            resolve_system_field_index(name, current_system, system_fields).is_some()
                || value_locals.contains(name)
                || fieldless_enum_variant_value(name, entity_specs).is_some()
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
                    || resolve_system_field_type(name, current_system, system_field_types)
                        .is_some_and(|ty| enum_payload_type_has_field(ty, field))
                    || explicit_expr_type(expr)
                        .is_some_and(|ty| enum_payload_type_has_field(ty, field))
            }
            _ => {
                explicit_expr_type(expr).is_some_and(|ty| enum_payload_type_has_field(ty, field))
                    && supports_state_expr(
                        expr,
                        current_system,
                        system_fields,
                        system_field_types,
                        entity_specs,
                        value_locals,
                        slot_locals,
                    )
            }
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
                system_field_types,
                entity_specs,
                value_locals,
                slot_locals,
            ) && supports_state_expr(
                right,
                current_system,
                system_fields,
                system_field_types,
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
                    system_field_types,
                    entity_specs,
                    value_locals,
                    slot_locals,
                )
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut nested_value_locals = value_locals.clone();
            for binding in bindings {
                if !supports_state_expr(
                    &binding.expr,
                    current_system,
                    system_fields,
                    system_field_types,
                    entity_specs,
                    &nested_value_locals,
                    slot_locals,
                ) {
                    return false;
                }
                nested_value_locals.insert(binding.name.clone());
            }
            supports_state_expr(
                body,
                current_system,
                system_fields,
                system_field_types,
                entity_specs,
                &nested_value_locals,
                slot_locals,
            )
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body: Some(else_body),
            ..
        } => {
            supports_state_expr(
                cond,
                current_system,
                system_fields,
                system_field_types,
                entity_specs,
                value_locals,
                slot_locals,
            ) && supports_state_expr(
                then_body,
                current_system,
                system_fields,
                system_field_types,
                entity_specs,
                value_locals,
                slot_locals,
            ) && supports_state_expr(
                else_body,
                current_system,
                system_fields,
                system_field_types,
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
        }
        | IRExpr::One {
            var, domain, body, ..
        }
        | IRExpr::Lone {
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
                    system_field_types,
                    entity_specs,
                    value_locals,
                    &nested_slot_locals,
                )
            }
            _ if finite_values_for_type(domain).is_ok() => {
                let mut nested_value_locals = value_locals.clone();
                nested_value_locals.insert(var.clone());
                supports_state_expr(
                    body,
                    current_system,
                    system_fields,
                    system_field_types,
                    entity_specs,
                    &nested_value_locals,
                    slot_locals,
                )
            }
            _ => false,
        },
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => {
            finite_values_for_type(domain).is_ok() && {
                let mut nested_value_locals = value_locals.clone();
                nested_value_locals.insert(var.clone());
                predicate.as_ref().is_none_or(|pred| {
                    supports_state_expr(
                        pred,
                        current_system,
                        system_fields,
                        system_field_types,
                        entity_specs,
                        &nested_value_locals,
                        slot_locals,
                    )
                })
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            supports_state_expr(
                scrutinee,
                current_system,
                system_fields,
                system_field_types,
                entity_specs,
                value_locals,
                slot_locals,
            ) && arms.iter().all(|arm| {
                if !pattern_supported(&arm.pattern) {
                    return false;
                }
                let arm_value_locals = pattern_value_local_names(value_locals, &arm.pattern);
                arm.guard.as_ref().is_none_or(|guard| {
                    supports_state_expr(
                        guard,
                        current_system,
                        system_fields,
                        system_field_types,
                        entity_specs,
                        &arm_value_locals,
                        slot_locals,
                    )
                }) && supports_state_expr(
                    &arm.body,
                    current_system,
                    system_fields,
                    system_field_types,
                    entity_specs,
                    &arm_value_locals,
                    slot_locals,
                )
            })
        }
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
        } => eval_ctor_value(
            state,
            current_system,
            system_fields,
            entity_specs,
            value_locals,
            slot_locals,
            enum_name,
            ctor,
            args,
        ),
        IRExpr::Var { name, .. } => {
            if let Some(value) = value_locals.get(name) {
                return Ok(value.clone());
            }
            if let Some(index) = resolve_system_field_index(name, current_system, system_fields) {
                return Ok(state.system_values[index].clone());
            }
            fieldless_enum_variant_value(name, entity_specs)
                .ok_or_else(|| format!("unknown explicit-state field `{name}`"))
        }
        IRExpr::Field { expr, field, .. } => {
            if let IRExpr::Var { name, .. } = expr.as_ref() {
                if let Some(binding) = slot_locals.get(name) {
                    let spec = &entity_specs[binding.entity_index];
                    let field_index = *spec
                        .field_indices
                        .get(field)
                        .ok_or_else(|| format!("unknown explicit-state field `{field}`"))?;
                    return Ok(
                        state.entity_slots[binding.entity_index][binding.slot].values[field_index]
                            .clone(),
                    );
                }
                if let Some(ExplicitValue::SlotRef(selected)) = value_locals.get(name) {
                    let binding = explicit_slot_binding_for_ref(entity_specs, selected)?;
                    let spec = &entity_specs[binding.entity_index];
                    let field_index = *spec
                        .field_indices
                        .get(field)
                        .ok_or_else(|| format!("unknown explicit-state field `{field}`"))?;
                    return Ok(
                        state.entity_slots[binding.entity_index][binding.slot].values[field_index]
                            .clone(),
                    );
                }
            }
            match eval_expr(
                state,
                expr,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )? {
                ExplicitValue::Enum { fields, .. } => fields
                    .into_iter()
                    .find_map(|(name, value)| (name == *field).then_some(value))
                    .ok_or_else(|| format!("unknown explicit-state enum payload field `{field}`")),
                _ => Err("unsupported field projection in explicit-state fragment".to_owned()),
            }
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
        IRExpr::Let { bindings, body, .. } => {
            let mut nested_value_locals = value_locals.clone();
            for binding in bindings {
                let value = eval_expr(
                    state,
                    &binding.expr,
                    current_system,
                    system_fields,
                    entity_specs,
                    &nested_value_locals,
                    slot_locals,
                )?;
                nested_value_locals.insert(binding.name.clone(), value);
            }
            eval_expr(
                state,
                body,
                current_system,
                system_fields,
                entity_specs,
                &nested_value_locals,
                slot_locals,
            )
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let condition = eval_expr(
                state,
                cond,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )?;
            let selected = if expect_bool(condition)? {
                then_body
            } else {
                else_body
                    .as_ref()
                    .ok_or_else(|| "unsupported expression in explicit-state fragment".to_owned())?
            };
            eval_expr(
                state,
                selected,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => eval_quantifier(
            state,
            var,
            domain,
            body,
            current_system,
            system_fields,
            entity_specs,
            value_locals,
            slot_locals,
            QuantifierMode::Forall,
        ),
        IRExpr::Exists {
            var, domain, body, ..
        } => eval_quantifier(
            state,
            var,
            domain,
            body,
            current_system,
            system_fields,
            entity_specs,
            value_locals,
            slot_locals,
            QuantifierMode::Exists,
        ),
        IRExpr::One {
            var, domain, body, ..
        } => eval_quantifier(
            state,
            var,
            domain,
            body,
            current_system,
            system_fields,
            entity_specs,
            value_locals,
            slot_locals,
            QuantifierMode::One,
        ),
        IRExpr::Lone {
            var, domain, body, ..
        } => eval_quantifier(
            state,
            var,
            domain,
            body,
            current_system,
            system_fields,
            entity_specs,
            value_locals,
            slot_locals,
            QuantifierMode::Lone,
        ),
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => eval_choose(
            state,
            var,
            domain,
            predicate.as_deref(),
            current_system,
            system_fields,
            entity_specs,
            value_locals,
            slot_locals,
        ),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let scrutinee_value = eval_expr(
                state,
                scrutinee,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )?;
            for arm in arms {
                if !pattern_matches(&scrutinee_value, &arm.pattern) {
                    continue;
                }
                let arm_value_locals =
                    pattern_value_locals(value_locals, &arm.pattern, &scrutinee_value);
                if let Some(guard) = &arm.guard {
                    if !eval_bool_with_locals(
                        state,
                        guard,
                        current_system,
                        system_fields,
                        entity_specs,
                        &arm_value_locals,
                        slot_locals,
                    )? {
                        continue;
                    }
                }
                return eval_expr(
                    state,
                    &arm.body,
                    current_system,
                    system_fields,
                    entity_specs,
                    &arm_value_locals,
                    slot_locals,
                );
            }
            Err("non-exhaustive match in explicit-state fragment".to_owned())
        }
        _ => Err("unsupported expression in explicit-state fragment".to_owned()),
    }
}

fn eval_ctor_value(
    state: &ExplicitState,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
) -> Result<ExplicitValue, String> {
    let fields = args
        .iter()
        .map(|(name, expr)| {
            eval_expr(
                state,
                expr,
                current_system,
                system_fields,
                entity_specs,
                value_locals,
                slot_locals,
            )
            .map(|value| (name.clone(), value))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ExplicitValue::Enum {
        enum_name: enum_name.to_owned(),
        variant: ctor.to_owned(),
        fields,
    })
}

#[derive(Clone, Copy)]
enum QuantifierMode {
    Forall,
    Exists,
    One,
    Lone,
}

fn eval_quantifier(
    state: &ExplicitState,
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
    mode: QuantifierMode,
) -> Result<ExplicitValue, String> {
    let mut matches = 0usize;
    for (nested_values, nested_slots) in
        quantifier_bindings(state, var, domain, entity_specs, value_locals, slot_locals)?
    {
        if eval_bool_with_locals(
            state,
            body,
            current_system,
            system_fields,
            entity_specs,
            &nested_values,
            &nested_slots,
        )? {
            matches += 1;
            if matches > 1 && matches!(mode, QuantifierMode::Lone | QuantifierMode::One) {
                return Ok(ExplicitValue::Bool(false));
            }
            if matches == 1 && matches!(mode, QuantifierMode::Exists) {
                return Ok(ExplicitValue::Bool(true));
            }
        } else if matches!(mode, QuantifierMode::Forall) {
            return Ok(ExplicitValue::Bool(false));
        }
    }

    let result = match mode {
        QuantifierMode::Forall => true,
        QuantifierMode::Exists => false,
        QuantifierMode::One => matches == 1,
        QuantifierMode::Lone => true,
    };
    Ok(ExplicitValue::Bool(result))
}

fn eval_choose(
    state: &ExplicitState,
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    current_system: Option<&str>,
    system_fields: &HashMap<String, usize>,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<ExplicitValue, String> {
    for (nested_values, nested_slots) in
        quantifier_bindings(state, var, domain, entity_specs, value_locals, slot_locals)?
    {
        let selected = nested_values.get(var).cloned().or_else(|| {
            nested_slots.get(var).map(|binding| {
                ExplicitValue::SlotRef(op::EntitySlotRef::new(
                    entity_specs[binding.entity_index].name.clone(),
                    binding.slot,
                ))
            })
        });
        let predicate_holds = match predicate {
            Some(pred) => eval_bool_with_locals(
                state,
                pred,
                current_system,
                system_fields,
                entity_specs,
                &nested_values,
                &nested_slots,
            )?,
            None => true,
        };
        if predicate_holds {
            return selected
                .ok_or_else(|| format!("unknown explicit-state choose binding `{var}`"));
        }
    }
    Err("empty explicit-state choose domain".to_owned())
}

fn quantifier_bindings(
    state: &ExplicitState,
    var: &str,
    domain: &IRType,
    entity_specs: &[ExplicitEntitySpec<'_>],
    value_locals: &HashMap<String, ExplicitValue>,
    slot_locals: &HashMap<String, ExplicitSlotBinding>,
) -> Result<
    Vec<(
        HashMap<String, ExplicitValue>,
        HashMap<String, ExplicitSlotBinding>,
    )>,
    String,
> {
    if let IRType::Entity { name } = domain {
        let Some((entity_index, spec)) = entity_specs
            .iter()
            .enumerate()
            .find(|(_, spec)| spec.name == *name)
        else {
            return Err("unknown explicit-state quantifier entity".to_owned());
        };
        let mut bindings = Vec::new();
        for slot in 0..spec.slot_count {
            if !state.entity_slots[entity_index][slot].active {
                continue;
            }
            let mut nested_slots = slot_locals.clone();
            nested_slots.insert(var.to_owned(), ExplicitSlotBinding { entity_index, slot });
            bindings.push((value_locals.clone(), nested_slots));
        }
        return Ok(bindings);
    }

    finite_values_for_type(domain)
        .map_err(|_| "unsupported quantifier domain in explicit-state fragment".to_owned())
        .map(|values| {
            values
                .into_iter()
                .map(|value| {
                    let mut nested_values = value_locals.clone();
                    nested_values.insert(var.to_owned(), value);
                    (nested_values, slot_locals.clone())
                })
                .collect()
        })
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
        (IRType::Bool, Some(default)) => match eval_static_finite_expr_for_type(default, &field.ty)?
        {
            ExplicitValue::Bool(value) => Ok(ExplicitValue::Bool(value)),
            _ => Err(format!(
                "unsupported explicit-state field `{}`; bool default must evaluate to bool",
                field.name
            )),
        },
        (IRType::Bool, None) => Ok(ExplicitValue::Bool(false)),
        (IRType::Enum { variants, .. }, Some(default))
            if variants.iter().all(|variant| {
                variant
                    .fields
                    .iter()
                    .all(|field| finite_values_for_type(&field.ty).is_ok())
            }) =>
        {
            match eval_static_finite_expr_for_type(default, &field.ty)? {
                value @ ExplicitValue::Enum { .. } => Ok(value),
                _ => Err(format!(
                    "unsupported explicit-state field `{}`; enum default must evaluate to enum",
                    field.name
                )),
            }
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
                fields: vec![],
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
            if variants.iter().all(|variant| {
                variant
                    .fields
                    .iter()
                    .all(|field| finite_values_for_type(&field.ty).is_ok())
            }) =>
        {
            let mut values = Vec::new();
            for variant in variants {
                for fields in enumerate_variant_field_values(&variant.fields)? {
                    values.push(ExplicitValue::Enum {
                        enum_name: name.clone(),
                        variant: variant.name.clone(),
                        fields,
                    });
                }
            }
            Ok(values)
        }
        _ => Err("explicit-state only supports Bool and finite-enum step parameters".to_owned()),
    }
}

fn enumerate_variant_field_values(
    fields: &[crate::ir::types::IRVariantField],
) -> Result<Vec<Vec<(String, ExplicitValue)>>, String> {
    let mut out = vec![Vec::new()];
    for field in fields {
        let values = finite_values_for_type(&field.ty)?;
        let mut next = Vec::new();
        for prefix in &out {
            for value in &values {
                let mut extended = prefix.clone();
                extended.push((field.name.clone(), value.clone()));
                next.push(extended);
            }
        }
        out = next;
    }
    Ok(out)
}

#[cfg(test)]
fn eval_static_finite_expr(expr: &IRExpr) -> Result<ExplicitValue, String> {
    eval_static_finite_expr_with_locals(expr, &HashMap::new(), None)
}

fn eval_static_finite_expr_for_type(
    expr: &IRExpr,
    expected_ty: &IRType,
) -> Result<ExplicitValue, String> {
    eval_static_finite_expr_with_locals(expr, &HashMap::new(), Some(expected_ty))
}

fn eval_static_bool_expr_with_locals(
    expr: &IRExpr,
    value_locals: &HashMap<String, ExplicitValue>,
) -> Result<bool, String> {
    match eval_static_finite_expr_with_locals(expr, value_locals, Some(&IRType::Bool))? {
        ExplicitValue::Bool(value) => Ok(value),
        _ => Err("explicit-state static finite expression must be bool".to_owned()),
    }
}

fn eval_static_finite_expr_with_locals(
    expr: &IRExpr,
    value_locals: &HashMap<String, ExplicitValue>,
    expected_ty: Option<&IRType>,
) -> Result<ExplicitValue, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(ExplicitValue::Bool(*value)),
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            let variant_field_types = expected_ty.and_then(|ty| {
                let IRType::Enum { variants, .. } = ty else {
                    return None;
                };
                variants.iter().find(|variant| variant.name == *ctor)
            });
            let fields = args
                .iter()
                .map(|(name, expr)| {
                    let field_ty = variant_field_types.and_then(|variant| {
                        variant
                            .fields
                            .iter()
                            .find(|field| field.name == *name)
                            .map(|field| &field.ty)
                    });
                    eval_static_finite_expr_with_locals(expr, value_locals, field_ty)
                        .map(|value| (name.clone(), value))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ExplicitValue::Enum {
                enum_name: enum_name.clone(),
                variant: ctor.clone(),
                fields,
            })
        }
        IRExpr::Var { name, .. } => value_locals
            .get(name)
            .cloned()
            .or_else(|| fieldless_enum_variant_value_for_type(name, expected_ty))
            .ok_or_else(|| format!("unknown explicit-state static finite local `{name}`")),
        IRExpr::Field { expr, field, .. } => {
            match eval_static_finite_expr_with_locals(expr, value_locals, None)? {
                ExplicitValue::Enum { fields, .. } => fields
                    .into_iter()
                    .find_map(|(name, value)| (name == *field).then_some(value))
                    .ok_or_else(|| format!("unknown explicit-state enum payload field `{field}`")),
                _ => Err("unsupported field projection in explicit-state fragment".to_owned()),
            }
        }
        IRExpr::UnOp { op, operand, .. } => {
            eval_unop(
                op,
                eval_static_finite_expr_with_locals(operand, value_locals, None)?,
            )
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => eval_binop(
            op,
            eval_static_finite_expr_with_locals(left, value_locals, None)?,
            eval_static_finite_expr_with_locals(right, value_locals, None)?,
        ),
        IRExpr::Let { bindings, body, .. } => {
            let mut nested_value_locals = value_locals.clone();
            for binding in bindings {
                let value =
                    eval_static_finite_expr_with_locals(&binding.expr, &nested_value_locals, None)?;
                nested_value_locals.insert(binding.name.clone(), value);
            }
            eval_static_finite_expr_with_locals(body, &nested_value_locals, expected_ty)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body: Some(else_body),
            ..
        } => {
            if eval_static_bool_expr_with_locals(cond, value_locals)? {
                eval_static_finite_expr_with_locals(then_body, value_locals, expected_ty)
            } else {
                eval_static_finite_expr_with_locals(else_body, value_locals, expected_ty)
            }
        }
        IRExpr::IfElse {
            else_body: None, ..
        } => Err("unsupported explicit-state finite enum payload expression".to_owned()),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let scrutinee_value =
                eval_static_finite_expr_with_locals(scrutinee, value_locals, None)?;
            for arm in arms {
                if !pattern_matches(&scrutinee_value, &arm.pattern) {
                    continue;
                }
                let arm_value_locals =
                    pattern_value_locals(value_locals, &arm.pattern, &scrutinee_value);
                if let Some(guard) = &arm.guard {
                    if !eval_static_bool_expr_with_locals(guard, &arm_value_locals)? {
                        continue;
                    }
                }
                return eval_static_finite_expr_with_locals(
                    &arm.body,
                    &arm_value_locals,
                    expected_ty,
                );
            }
            Err("non-exhaustive match in explicit-state fragment".to_owned())
        }
        _ => Err("unsupported explicit-state finite enum payload expression".to_owned()),
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
            "explicit-state only supports Bool, finite-enum, and entity step parameters"
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
        ExplicitValue::Enum {
            enum_name,
            variant,
            fields,
        } => op::WitnessValue::EnumVariant {
            enum_name: enum_name.clone(),
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|(name, value)| (name.clone(), witness_value(value)))
                .collect::<BTreeMap<_, _>>(),
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
    use crate::ir::types::{
        IRActionMatchArm, IRActionMatchScrutinee, IRFieldPat, IRMatchArm, IRPattern, IRUpdate,
        IRVariant,
    };

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

    fn payload_enum_type() -> IRType {
        IRType::Enum {
            name: "Decision".to_owned(),
            variants: vec![
                IRVariant {
                    name: "Accept".to_owned(),
                    fields: vec![crate::ir::types::IRVariantField {
                        name: "allowed".to_owned(),
                        ty: IRType::Bool,
                    }],
                },
                IRVariant::simple("Reject"),
            ],
        }
    }

    fn total_payload_enum_type() -> IRType {
        IRType::Enum {
            name: "Decision".to_owned(),
            variants: vec![
                IRVariant {
                    name: "Accept".to_owned(),
                    fields: vec![crate::ir::types::IRVariantField {
                        name: "allowed".to_owned(),
                        ty: IRType::Bool,
                    }],
                },
                IRVariant {
                    name: "Reject".to_owned(),
                    fields: vec![crate::ir::types::IRVariantField {
                        name: "allowed".to_owned(),
                        ty: IRType::Bool,
                    }],
                },
            ],
        }
    }

    fn payload_enum_ctor(allowed: bool) -> IRExpr {
        IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Accept".to_owned(),
            args: vec![("allowed".to_owned(), bool_lit(allowed))],
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
                variant: "Closed".to_owned(),
                fields: vec![],
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

        let payload_params = vec![IRTransParam {
            name: "decision".to_owned(),
            ty: payload_enum_type(),
        }];
        let payload_bindings = enumerate_param_bindings(&payload_params).unwrap();
        assert_eq!(payload_bindings.len(), 3);
        assert!(field_types_with_params(&HashMap::new(), &payload_params)
            .get("decision")
            .is_some_and(|ty| enum_payload_type_has_field(ty, "allowed")));
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_fields_quantifiers_and_errors() {
        let state = sample_state();
        let specs = vec![entity_spec()];
        let system_fields = HashMap::from([
            ("Orders::flag".to_owned(), 0usize),
            ("flag".to_owned(), 0usize),
        ]);
        let system_field_types = HashMap::from([
            ("Orders::flag".to_owned(), IRType::Bool),
            ("flag".to_owned(), IRType::Bool),
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
            &system_field_types,
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
            &system_field_types,
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
            &system_field_types,
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
    fn explicit_state_initial_constraints_enumerate_finite_field_values() {
        let constrained_field = IRField {
            name: "heads".to_owned(),
            ty: IRType::Bool,
            default: None,
            initial_constraint: Some(bin("OpEq", var("$", IRType::Bool), bool_lit(true))),
        };
        let spec = ExplicitEntitySpec {
            name: "Coin".to_owned(),
            slot_count: 1,
            fields: vec![constrained_field],
            field_indices: HashMap::from([("heads".to_owned(), 0)]),
            transitions: HashMap::new(),
            fsm_decls: Vec::new(),
        };

        let states =
            enumerate_initial_states(&[spec], &HashMap::from([((0usize, 0usize), true)]), vec![])
                .unwrap();

        assert_eq!(states.len(), 1);
        assert!(states[0].entity_slots[0][0].active);
        assert_eq!(
            states[0].entity_slots[0][0].values[0],
            ExplicitValue::Bool(true)
        );
    }

    #[test]
    fn explicit_state_initial_constraints_support_payload_field_projection() {
        let constrained_field = IRField {
            name: "decision".to_owned(),
            ty: total_payload_enum_type(),
            default: None,
            initial_constraint: Some(bin(
                "OpEq",
                IRExpr::Field {
                    expr: Box::new(var("$", total_payload_enum_type())),
                    field: "allowed".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
                bool_lit(true),
            )),
        };
        let entity = IREntity {
            name: "Ticket".to_owned(),
            fields: vec![constrained_field],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let spec = build_entity_spec(&entity, 1, None)
            .expect("payload initial constraints should validate as explicit-state finite");
        let states =
            enumerate_initial_states(&[spec], &HashMap::from([((0usize, 0usize), true)]), vec![])
                .expect("payload initial constraints should enumerate finite values");

        assert_eq!(states.len(), 2);
        assert!(states[0].entity_slots[0][0].active);
        assert!(
            states.iter().all(|state| matches!(
                &state.entity_slots[0][0].values[0],
                ExplicitValue::Enum { fields, .. }
                    if fields.iter().any(|(name, value)| name == "allowed" && value == &ExplicitValue::Bool(true))
            )),
            "all enumerated payload values should satisfy allowed=true: {states:?}"
        );
    }

    #[test]
    fn explicit_state_create_enumerates_payload_field_constraints() {
        let constrained_field = IRField {
            name: "decision".to_owned(),
            ty: total_payload_enum_type(),
            default: None,
            initial_constraint: Some(bin(
                "OpEq",
                IRExpr::Field {
                    expr: Box::new(var("$", total_payload_enum_type())),
                    field: "allowed".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
                bool_lit(true),
            )),
        };
        let entity = IREntity {
            name: "Ticket".to_owned(),
            fields: vec![constrained_field],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let spec = build_entity_spec(&entity, 1, None)
            .expect("payload create constraints should validate as explicit-state finite");
        let model = ExplicitModel {
            roots: vec!["Queue".to_owned()],
            system_fields: vec![],
            system_field_indices: HashMap::new(),
            entity_specs: vec![spec],
            entity_indices: HashMap::from([("Ticket".to_owned(), 0usize)]),
            steps: vec![],
            step_indices: HashMap::new(),
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        };
        let state = ExplicitState {
            system_values: vec![],
            entity_slots: vec![vec![ExplicitEntitySlotState {
                active: false,
                values: vec![ExplicitValue::Enum {
                    enum_name: "Decision".to_owned(),
                    variant: "Accept".to_owned(),
                    fields: vec![("allowed".to_owned(), ExplicitValue::Bool(true))],
                }],
            }]],
        };

        let outcomes = execute_actions(
            &model,
            state,
            "Queue",
            &[IRAction::Create {
                entity: "Ticket".to_owned(),
                fields: vec![],
            }],
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("create should enumerate finite constrained payload values");

        assert_eq!(outcomes.len(), 2);
        assert!(outcomes.iter().all(|(next, _, _)| {
            next.entity_slots[0][0].active
                && matches!(
                    &next.entity_slots[0][0].values[0],
                    ExplicitValue::Enum { fields, .. }
                        if fields.iter().any(|(name, value)| name == "allowed" && value == &ExplicitValue::Bool(true))
                )
        }));
    }

    #[test]
    fn explicit_state_witness_value_preserves_enum_payload_fields() {
        let value = ExplicitValue::Enum {
            enum_name: "Decision".to_owned(),
            variant: "Accept".to_owned(),
            fields: vec![("allowed".to_owned(), ExplicitValue::Bool(false))],
        };

        let witness = witness_value(&value);
        let encoded = serde_json::to_value(witness).expect("witness value should serialize");

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
    fn explicit_state_static_finite_enum_payload_defaults_allow_bool_exprs() {
        let field = IRField {
            name: "decision".to_owned(),
            ty: payload_enum_type(),
            default: Some(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Accept".to_owned(),
                args: vec![(
                    "allowed".to_owned(),
                    IRExpr::UnOp {
                        op: "OpNot".to_owned(),
                        operand: Box::new(bool_lit(false)),
                        ty: IRType::Bool,
                        span: None,
                    },
                )],
                span: None,
            }),
            initial_constraint: None,
        };

        assert_eq!(
            finite_default_value(&field).expect("static payload bool expression should evaluate"),
            ExplicitValue::Enum {
                enum_name: "Decision".to_owned(),
                variant: "Accept".to_owned(),
                fields: vec![("allowed".to_owned(), ExplicitValue::Bool(true))],
            }
        );
    }

    #[test]
    fn explicit_state_static_finite_enum_payload_defaults_allow_core_exprs() {
        let let_default = IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "accepted".to_owned(),
                ty: IRType::Bool,
                expr: bool_lit(true),
            }],
            body: Box::new(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Accept".to_owned(),
                args: vec![("allowed".to_owned(), var("accepted", IRType::Bool))],
                span: None,
            }),
            span: None,
        };
        let if_default = IRExpr::IfElse {
            cond: Box::new(bool_lit(true)),
            then_body: Box::new(payload_enum_ctor(true)),
            else_body: Some(Box::new(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Reject".to_owned(),
                args: vec![],
                span: None,
            })),
            span: None,
        };
        let match_default = IRExpr::Match {
            scrutinee: Box::new(payload_enum_ctor(true)),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Accept".to_owned(),
                        fields: vec![IRFieldPat {
                            name: "allowed".to_owned(),
                            pattern: IRPattern::PVar {
                                name: "accepted".to_owned(),
                            },
                        }],
                    },
                    guard: Some(var("accepted", IRType::Bool)),
                    body: IRExpr::Ctor {
                        enum_name: "Decision".to_owned(),
                        ctor: "Accept".to_owned(),
                        args: vec![("allowed".to_owned(), var("accepted", IRType::Bool))],
                        span: None,
                    },
                },
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Reject".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: IRExpr::Ctor {
                        enum_name: "Decision".to_owned(),
                        ctor: "Reject".to_owned(),
                        args: vec![],
                        span: None,
                    },
                },
            ],
            span: None,
        };

        for default in [let_default, if_default, match_default] {
            assert_eq!(
                eval_static_finite_expr(&default)
                    .expect("static core expression default should evaluate"),
                ExplicitValue::Enum {
                    enum_name: "Decision".to_owned(),
                    variant: "Accept".to_owned(),
                    fields: vec![("allowed".to_owned(), ExplicitValue::Bool(true))],
                }
            );
        }

        let fieldless_atom_default = IRExpr::IfElse {
            cond: Box::new(bool_lit(false)),
            then_body: Box::new(payload_enum_ctor(true)),
            else_body: Some(Box::new(var("Reject", IRType::Int))),
            span: None,
        };
        assert_eq!(
            eval_static_finite_expr_for_type(&fieldless_atom_default, &payload_enum_type())
                .expect("expected enum type should resolve fieldless constructor atoms"),
            ExplicitValue::Enum {
                enum_name: "Decision".to_owned(),
                variant: "Reject".to_owned(),
                fields: vec![],
            }
        );
    }

    #[test]
    fn explicit_state_forall_action_iterates_active_slots() {
        let state = sample_state();
        let spec = entity_spec();
        let model = ExplicitModel {
            roots: vec!["Sys".to_owned()],
            system_fields: vec![],
            system_field_indices: HashMap::new(),
            entity_specs: vec![spec],
            entity_indices: HashMap::from([("Task".to_owned(), 0)]),
            steps: vec![],
            step_indices: HashMap::new(),
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        };

        let outcomes = execute_actions(
            &model,
            state.clone(),
            "Sys",
            &[IRAction::ForAll {
                var: "task".to_owned(),
                entity: "Task".to_owned(),
                ops: vec![],
            }],
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("forall action should execute over finite active slots");

        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].0, state);
        assert_eq!(
            outcomes[0].2,
            vec![op::Choice::ForAll {
                binder: "task".to_owned(),
                iterated: vec![op::EntitySlotRef::new("Task", 0)],
            }]
        );
    }

    #[test]
    fn explicit_state_empty_choose_body_validates_and_records_choice() {
        let state = sample_state();
        let spec = entity_spec();
        let model = ExplicitModel {
            roots: vec!["Sys".to_owned()],
            system_fields: vec![],
            system_field_indices: HashMap::new(),
            entity_specs: vec![spec],
            entity_indices: HashMap::from([("Task".to_owned(), 0)]),
            steps: vec![],
            step_indices: HashMap::new(),
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        };
        let action = IRAction::Choose {
            var: "task".to_owned(),
            entity: "Task".to_owned(),
            filter: Box::new(bool_lit(true)),
            ops: vec![],
        };

        let validated = validate_actions(
            std::slice::from_ref(&action),
            "Sys",
            &HashMap::new(),
            &HashMap::new(),
            &model.entity_specs,
            &[],
            &HashMap::new(),
            &HashSet::new(),
            &HashMap::new(),
            &mut HashSet::new(),
        )
        .expect("empty choose bodies are finite no-op choices");

        assert!(validated.is_empty());

        let outcomes = execute_actions(
            &model,
            state.clone(),
            "Sys",
            &[action],
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("empty choose body should execute over matching active slots");

        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].0, state);
        assert_eq!(
            outcomes[0].2,
            vec![op::Choice::Choose {
                binder: "task".to_owned(),
                selected: op::EntitySlotRef::new("Task", 0),
            }]
        );
    }

    #[test]
    fn explicit_state_action_match_payload_bindings_scope_guards_and_bodies() {
        let state = ExplicitState {
            system_values: vec![ExplicitValue::Bool(false)],
            entity_slots: vec![],
        };
        let system_fields = HashMap::from([
            ("Billing::charged".to_owned(), 0usize),
            ("charged".to_owned(), 0usize),
        ]);
        let system_field_types = HashMap::from([
            ("Billing::charged".to_owned(), IRType::Bool),
            ("charged".to_owned(), IRType::Bool),
        ]);
        let model = ExplicitModel {
            roots: vec!["Billing".to_owned()],
            system_fields: vec![ExplicitFieldRef {
                system: "Billing".to_owned(),
                field: "charged".to_owned(),
            }],
            system_field_indices: system_fields.clone(),
            entity_specs: vec![],
            entity_indices: HashMap::new(),
            steps: vec![],
            step_indices: HashMap::new(),
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        };
        let payload = ExplicitValue::Enum {
            enum_name: "Outcome".to_owned(),
            variant: "ok".to_owned(),
            fields: vec![("accepted".to_owned(), ExplicitValue::Bool(true))],
        };
        let value_locals = HashMap::from([("result".to_owned(), payload)]);
        let value_names = HashSet::from(["result".to_owned()]);
        let action = IRAction::Match {
            scrutinee: IRActionMatchScrutinee::Var {
                name: "result".to_owned(),
            },
            arms: vec![IRActionMatchArm {
                pattern: IRPattern::PCtor {
                    name: "ok".to_owned(),
                    fields: vec![IRFieldPat {
                        name: "accepted".to_owned(),
                        pattern: IRPattern::PVar {
                            name: "accepted".to_owned(),
                        },
                    }],
                },
                guard: Some(var("accepted", IRType::Bool)),
                body: vec![IRAction::ExprStmt {
                    expr: bin(
                        "OpEq",
                        prime(var("charged", IRType::Bool)),
                        var("accepted", IRType::Bool),
                    ),
                }],
            }],
        };

        validate_actions(
            std::slice::from_ref(&action),
            "Billing",
            &system_fields,
            &system_field_types,
            &model.entity_specs,
            &[],
            &HashMap::new(),
            &value_names,
            &HashMap::new(),
            &mut HashSet::new(),
        )
        .expect("action match payload bindings should scope over guards and bodies");

        let outcomes = execute_actions(
            &model,
            state,
            "Billing",
            &[action],
            &value_locals,
            &HashMap::new(),
        )
        .expect("action match payload bindings should execute guards and bodies");

        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].0.system_values[0], ExplicitValue::Bool(true));
    }

    #[test]
    fn explicit_state_cross_call_args_can_read_choose_slot_fields() {
        let ticket_spec = ExplicitEntitySpec {
            name: "Ticket".to_owned(),
            slot_count: 1,
            fields: vec![IRField {
                name: "decision".to_owned(),
                ty: total_payload_enum_type(),
                default: None,
                initial_constraint: None,
            }],
            field_indices: HashMap::from([("decision".to_owned(), 0usize)]),
            transitions: HashMap::new(),
            fsm_decls: Vec::new(),
        };
        let record_step = Box::leak(Box::new(IRSystemAction {
            name: "record".to_owned(),
            params: vec![IRTransParam {
                name: "flag".to_owned(),
                ty: IRType::Bool,
            }],
            guard: bool_lit(true),
            body: vec![IRAction::ExprStmt {
                expr: bin(
                    "OpEq",
                    prime(var("recorded", IRType::Bool)),
                    var("flag", IRType::Bool),
                ),
            }],
            return_expr: None,
        }));
        let system_fields = HashMap::from([
            ("Audit::recorded".to_owned(), 0usize),
            ("recorded".to_owned(), 0usize),
        ]);
        let system_field_types = HashMap::from([
            ("Audit::recorded".to_owned(), IRType::Bool),
            ("recorded".to_owned(), IRType::Bool),
        ]);
        let steps = vec![ExplicitStepRef {
            system: "Audit".to_owned(),
            store_param_count: 0,
            step: record_step,
        }];
        let step_indices = HashMap::from([(("Audit".to_owned(), "record".to_owned()), 0usize)]);
        let arg = IRExpr::Field {
            expr: Box::new(IRExpr::Field {
                expr: Box::new(var(
                    "ticket",
                    IRType::Entity {
                        name: "Ticket".to_owned(),
                    },
                )),
                field: "decision".to_owned(),
                ty: total_payload_enum_type(),
                span: None,
            }),
            field: "allowed".to_owned(),
            ty: IRType::Bool,
            span: None,
        };
        let action = IRAction::Choose {
            var: "ticket".to_owned(),
            entity: "Ticket".to_owned(),
            filter: Box::new(bool_lit(true)),
            ops: vec![IRAction::CrossCall {
                system: "Audit".to_owned(),
                command: "record".to_owned(),
                args: vec![arg],
            }],
        };
        let entity_specs = vec![ticket_spec];

        validate_actions(
            std::slice::from_ref(&action),
            "Queue",
            &system_fields,
            &system_field_types,
            &entity_specs,
            &steps,
            &step_indices,
            &HashSet::new(),
            &HashMap::new(),
            &mut HashSet::new(),
        )
        .expect("cross-call args should validate against choose slot fields");

        let model = ExplicitModel {
            roots: vec!["Audit".to_owned(), "Queue".to_owned()],
            system_fields: vec![ExplicitFieldRef {
                system: "Audit".to_owned(),
                field: "recorded".to_owned(),
            }],
            system_field_indices: system_fields,
            entity_specs,
            entity_indices: HashMap::from([("Ticket".to_owned(), 0usize)]),
            steps,
            step_indices,
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        };
        let state = ExplicitState {
            system_values: vec![ExplicitValue::Bool(false)],
            entity_slots: vec![vec![ExplicitEntitySlotState {
                active: true,
                values: vec![ExplicitValue::Enum {
                    enum_name: "Decision".to_owned(),
                    variant: "Accept".to_owned(),
                    fields: vec![("allowed".to_owned(), ExplicitValue::Bool(true))],
                }],
            }]],
        };

        let outcomes = execute_actions(
            &model,
            state,
            "Queue",
            &[action],
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("cross-call args should execute against choose slot fields");

        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].0.system_values[0], ExplicitValue::Bool(true));
    }

    #[test]
    fn explicit_state_entity_step_params_can_target_entity_actions() {
        let ticket_ty = IRType::Entity {
            name: "Ticket".to_owned(),
        };
        let status_field = IRField {
            name: "status".to_owned(),
            ty: enum_type(),
            default: Some(enum_ctor("Open")),
            initial_constraint: None,
        };
        let close: &'static IRTransition = Box::leak(Box::new(IRTransition {
            name: "close".to_owned(),
            refs: vec![],
            params: vec![],
            guard: bin("OpEq", var("status", enum_type()), enum_ctor("Open")),
            updates: vec![IRUpdate {
                field: "status".to_owned(),
                value: enum_ctor("Closed"),
            }],
            postcondition: None,
        }));
        let ticket_spec = ExplicitEntitySpec {
            name: "Ticket".to_owned(),
            slot_count: 1,
            fields: vec![status_field],
            field_indices: HashMap::from([("status".to_owned(), 0usize)]),
            transitions: HashMap::from([("close".to_owned(), close)]),
            fsm_decls: Vec::new(),
        };
        let action = IRAction::Apply {
            target: "ticket".to_owned(),
            transition: "close".to_owned(),
            refs: vec![],
            args: vec![],
        };
        let system_field_types = HashMap::from([("ticket".to_owned(), ticket_ty.clone())]);
        let value_names = HashSet::from(["ticket".to_owned()]);
        let entity_specs = vec![ticket_spec];

        validate_actions(
            std::slice::from_ref(&action),
            "Queue",
            &HashMap::new(),
            &system_field_types,
            &entity_specs,
            &[],
            &HashMap::new(),
            &value_names,
            &HashMap::new(),
            &mut HashSet::new(),
        )
        .expect("entity step parameters should validate as entity action targets");

        let model = ExplicitModel {
            roots: vec!["Queue".to_owned()],
            system_fields: vec![],
            system_field_indices: HashMap::new(),
            entity_specs,
            entity_indices: HashMap::from([("Ticket".to_owned(), 0usize)]),
            steps: vec![],
            step_indices: HashMap::new(),
            safety_properties: vec![],
            liveness_monitors: vec![],
            extern_assume_exprs: vec![],
            stutter: true,
            weak_fair: vec![],
            strong_fair: vec![],
            per_tuple_fair: vec![],
        };
        let state = ExplicitState {
            system_values: vec![],
            entity_slots: vec![vec![ExplicitEntitySlotState {
                active: true,
                values: vec![ExplicitValue::Enum {
                    enum_name: "Status".to_owned(),
                    variant: "Open".to_owned(),
                    fields: vec![],
                }],
            }]],
        };
        let value_locals = HashMap::from([(
            "ticket".to_owned(),
            ExplicitValue::SlotRef(op::EntitySlotRef::new("Ticket", 0)),
        )]);

        let outcomes = execute_actions(
            &model,
            state,
            "Queue",
            &[action],
            &value_locals,
            &HashMap::new(),
        )
        .expect("entity step parameters should execute as entity action targets");

        assert_eq!(outcomes.len(), 1);
        assert_eq!(
            outcomes[0].0.entity_slots[0][0].values[0],
            ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Closed".to_owned(),
                fields: vec![],
            }
        );
    }

    #[test]
    fn explicit_state_payload_step_param_field_projection_validates() {
        let system_fields = HashMap::from([
            ("Gate::allowed".to_owned(), 0usize),
            ("allowed".to_owned(), 0usize),
        ]);
        let params = vec![IRTransParam {
            name: "decision".to_owned(),
            ty: payload_enum_type(),
        }];
        let system_field_types = field_types_with_params(
            &HashMap::from([
                ("Gate::allowed".to_owned(), IRType::Bool),
                ("allowed".to_owned(), IRType::Bool),
            ]),
            &params,
        );
        let value_names = HashSet::from(["decision".to_owned()]);
        let action = IRAction::ExprStmt {
            expr: bin(
                "OpEq",
                prime(var("allowed", IRType::Bool)),
                IRExpr::Field {
                    expr: Box::new(var("decision", payload_enum_type())),
                    field: "allowed".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
            ),
        };

        validate_actions(
            &[action],
            "Gate",
            &system_fields,
            &system_field_types,
            &[],
            &[],
            &HashMap::new(),
            &value_names,
            &HashMap::new(),
            &mut HashSet::new(),
        )
        .expect("payload enum step parameters should support payload field projection");
    }

    #[test]
    fn explicit_entity_spec_consumes_structured_verify_context_defaults() {
        let entity = IREntity {
            name: "Task".to_owned(),
            fields: vec![bool_field("active", Some(false))],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let entity_info = EntityInfo {
            name: "Task".to_owned(),
            fields: vec![crate::verify::context::FieldInfo {
                name: "active".to_owned(),
                ty: IRType::Bool,
                default: Some(bool_lit(true)),
            }],
            actions: vec![],
        };

        let spec = build_entity_spec(&entity, 1, Some(&entity_info))
            .expect("entity spec should consume structured context defaults");

        assert_eq!(
            entity_field_default_value(&spec.fields[0], "Task", 0).unwrap(),
            ExplicitValue::Bool(true)
        );
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_finite_quantifier_and_choose_domains() {
        let state = empty_state();
        let specs = vec![];
        let system_fields = HashMap::new();
        let system_field_types = HashMap::new();
        let value_locals = HashMap::new();
        let slot_locals = HashMap::new();
        let value_names = HashSet::new();
        let slot_names = HashMap::new();

        let forall_bool = IRExpr::Forall {
            var: "b".to_owned(),
            domain: IRType::Bool,
            body: Box::new(bin(
                "OpOr",
                var("b", IRType::Bool),
                IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(var("b", IRType::Bool)),
                    ty: IRType::Bool,
                    span: None,
                },
            )),
            span: None,
        };
        let exists_enum = IRExpr::Exists {
            var: "s".to_owned(),
            domain: enum_type(),
            body: Box::new(bin("OpEq", var("s", enum_type()), enum_ctor("Closed"))),
            span: None,
        };
        let one_enum = IRExpr::One {
            var: "s".to_owned(),
            domain: enum_type(),
            body: Box::new(bin("OpEq", var("s", enum_type()), enum_ctor("Open"))),
            span: None,
        };
        let lone_enum = IRExpr::Lone {
            var: "s".to_owned(),
            domain: enum_type(),
            body: Box::new(bin("OpEq", var("s", enum_type()), enum_ctor("Open"))),
            span: None,
        };
        let choose_enum = IRExpr::Choose {
            var: "s".to_owned(),
            domain: enum_type(),
            predicate: Some(Box::new(bin(
                "OpEq",
                var("s", enum_type()),
                enum_ctor("Closed"),
            ))),
            ty: enum_type(),
            span: None,
        };
        let choose_payload_projection = IRExpr::Field {
            expr: Box::new(IRExpr::Choose {
                var: "decision".to_owned(),
                domain: payload_enum_type(),
                predicate: Some(Box::new(bin(
                    "OpEq",
                    var("decision", payload_enum_type()),
                    payload_enum_ctor(false),
                ))),
                ty: payload_enum_type(),
                span: None,
            }),
            field: "allowed".to_owned(),
            ty: IRType::Bool,
            span: None,
        };

        for expr in [
            &forall_bool,
            &exists_enum,
            &one_enum,
            &lone_enum,
            &choose_enum,
            &choose_payload_projection,
        ] {
            assert!(supports_state_expr(
                expr,
                Some("Orders"),
                &system_fields,
                &system_field_types,
                &specs,
                &value_names,
                &slot_names,
            ));
        }
        assert_eq!(
            eval_expr(
                &state,
                &forall_bool,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            eval_expr(
                &state,
                &exists_enum,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            eval_expr(
                &state,
                &one_enum,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            eval_expr(
                &state,
                &lone_enum,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            eval_expr(
                &state,
                &choose_enum,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Closed".to_owned(),
                fields: vec![],
            }
        );
        assert_eq!(
            eval_expr(
                &state,
                &choose_payload_projection,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(false)
        );
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_match_guards() {
        let state = sample_state();
        let specs = vec![entity_spec()];
        let system_fields = HashMap::from([
            ("Orders::flag".to_owned(), 0usize),
            ("flag".to_owned(), 0usize),
        ]);
        let system_field_types = HashMap::from([
            ("Orders::flag".to_owned(), IRType::Bool),
            ("flag".to_owned(), IRType::Bool),
        ]);
        let value_locals = HashMap::new();
        let slot_locals = HashMap::new();
        let value_names = HashSet::new();
        let slot_names = HashMap::new();
        let match_expr = IRExpr::Match {
            scrutinee: Box::new(enum_ctor("Open")),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Open".to_owned(),
                        fields: vec![],
                    },
                    guard: Some(bool_lit(false)),
                    body: bool_lit(false),
                },
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Open".to_owned(),
                        fields: vec![],
                    },
                    guard: Some(bool_lit(true)),
                    body: bool_lit(true),
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: bool_lit(false),
                },
            ],
            span: None,
        };

        assert!(supports_state_expr(
            &match_expr,
            Some("Orders"),
            &system_fields,
            &system_field_types,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert_eq!(
            eval_expr(
                &state,
                &match_expr,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_let_bindings() {
        let state = sample_state();
        let specs = vec![entity_spec()];
        let system_fields = HashMap::from([
            ("Orders::flag".to_owned(), 0usize),
            ("flag".to_owned(), 0usize),
        ]);
        let system_field_types = HashMap::from([
            ("Orders::flag".to_owned(), IRType::Bool),
            ("flag".to_owned(), IRType::Bool),
        ]);
        let value_locals = HashMap::new();
        let slot_locals = HashMap::new();
        let value_names = HashSet::new();
        let slot_names = HashMap::new();
        let let_expr = IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "current".to_owned(),
                ty: IRType::Bool,
                expr: IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(var("flag", IRType::Bool)),
                    ty: IRType::Bool,
                    span: None,
                },
            }],
            body: Box::new(var("current", IRType::Bool)),
            span: None,
        };

        assert!(supports_state_expr(
            &let_expr,
            Some("Orders"),
            &system_fields,
            &system_field_types,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert_eq!(
            eval_expr(
                &state,
                &let_expr,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_ifelse() {
        let state = sample_state();
        let specs = vec![entity_spec()];
        let system_fields = HashMap::from([
            ("Orders::flag".to_owned(), 0usize),
            ("flag".to_owned(), 0usize),
        ]);
        let system_field_types = HashMap::from([
            ("Orders::flag".to_owned(), IRType::Bool),
            ("flag".to_owned(), IRType::Bool),
        ]);
        let value_locals = HashMap::new();
        let slot_locals = HashMap::new();
        let value_names = HashSet::new();
        let slot_names = HashMap::new();
        let ifelse_expr = IRExpr::IfElse {
            cond: Box::new(var("flag", IRType::Bool)),
            then_body: Box::new(bool_lit(false)),
            else_body: Some(Box::new(bool_lit(true))),
            span: None,
        };

        assert!(supports_state_expr(
            &ifelse_expr,
            Some("Orders"),
            &system_fields,
            &system_field_types,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert_eq!(
            eval_expr(
                &state,
                &ifelse_expr,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
    }

    #[test]
    fn explicit_state_expr_support_and_eval_cover_finite_enum_payloads() {
        let state = empty_state();
        let specs = vec![];
        let system_fields = HashMap::new();
        let system_field_types = HashMap::new();
        let value_locals = HashMap::from([(
            "decision".to_owned(),
            ExplicitValue::Enum {
                enum_name: "Decision".to_owned(),
                variant: "Accept".to_owned(),
                fields: vec![("allowed".to_owned(), ExplicitValue::Bool(true))],
            },
        )]);
        let slot_locals = HashMap::new();
        let value_names = HashSet::from(["decision".to_owned()]);
        let slot_names = HashMap::new();
        let payload_projection = IRExpr::Field {
            expr: Box::new(var("decision", payload_enum_type())),
            field: "allowed".to_owned(),
            ty: IRType::Bool,
            span: None,
        };
        let lowered_system_state = ExplicitState {
            system_values: vec![ExplicitValue::Enum {
                enum_name: "Decision".to_owned(),
                variant: "Accept".to_owned(),
                fields: vec![("allowed".to_owned(), ExplicitValue::Bool(true))],
            }],
            entity_slots: vec![],
        };
        let lowered_system_fields = HashMap::from([
            ("Gate::decision".to_owned(), 0usize),
            ("decision".to_owned(), 0usize),
        ]);
        let lowered_system_field_types = HashMap::from([
            ("Gate::decision".to_owned(), payload_enum_type()),
            ("decision".to_owned(), payload_enum_type()),
        ]);
        let lowered_payload_projection = IRExpr::Field {
            expr: Box::new(var("decision", IRType::Int)),
            field: "allowed".to_owned(),
            ty: IRType::Int,
            span: None,
        };
        let match_expr = IRExpr::Match {
            scrutinee: Box::new(payload_enum_ctor(true)),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Accept".to_owned(),
                        fields: vec![IRFieldPat {
                            name: "allowed".to_owned(),
                            pattern: IRPattern::PVar {
                                name: "allowed".to_owned(),
                            },
                        }],
                    },
                    guard: None,
                    body: var("allowed", IRType::Bool),
                },
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Reject".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: bool_lit(false),
                },
            ],
            span: None,
        };

        assert!(supports_state_expr(
            &payload_enum_ctor(true),
            Some("Orders"),
            &system_fields,
            &system_field_types,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert!(supports_state_expr(
            &match_expr,
            Some("Orders"),
            &system_fields,
            &system_field_types,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert!(supports_state_expr(
            &payload_projection,
            Some("Orders"),
            &system_fields,
            &system_field_types,
            &specs,
            &value_names,
            &slot_names,
        ));
        assert!(supports_state_expr(
            &lowered_payload_projection,
            Some("Gate"),
            &lowered_system_fields,
            &lowered_system_field_types,
            &specs,
            &HashSet::new(),
            &slot_names,
        ));
        assert_eq!(
            eval_expr(
                &state,
                &match_expr,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            eval_expr(
                &state,
                &payload_projection,
                Some("Orders"),
                &system_fields,
                &specs,
                &value_locals,
                &slot_locals,
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            eval_expr(
                &lowered_system_state,
                &lowered_payload_projection,
                Some("Gate"),
                &lowered_system_fields,
                &specs,
                &HashMap::new(),
                &HashMap::new(),
            )
            .unwrap(),
            ExplicitValue::Bool(true)
        );
        assert_eq!(
            finite_values_for_type(&payload_enum_type()).unwrap().len(),
            3
        );
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
        assert!(pattern_supported(&unsupported_ctor));
        assert!(pattern_matches(
            &ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Open".to_owned(),
                fields: vec![],
            },
            &ctor
        ));
        assert!(!pattern_matches(
            &ExplicitValue::Enum {
                enum_name: "Status".to_owned(),
                variant: "Closed".to_owned(),
                fields: vec![],
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
