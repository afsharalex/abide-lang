//! Backend-neutral transition-system obligation routing.
//!
//! The current implementation still uses the existing IC3/CHC encoding and
//! backend path, but callers should depend on this obligation shape rather than
//! reaching directly into solver-specific entry points.

#![allow(clippy::large_enum_variant)]

use std::collections::{HashMap, HashSet};

use crate::ir::types::{
    IRAssumptionSet, IRCommandRef, IREntity, IRExpr, IRProgram, IRStutterProvenance, IRSystem,
    IRTheorem, IRVerify,
};

use super::context::VerifyContext;
use super::defenv;
use super::encode::encode_pure_expr;
use super::harness::{
    create_slot_pool_with_systems, domain_constraints, initial_active_slots_with_store_ranges,
    initial_state_constraints_with_store_ranges, lasso_loopback,
    store_active_cardinality_constraints, symmetry_breaking_constraints, try_encode_guard_expr,
    try_entity_field_initial_constraints, try_fairness_constraints,
    try_system_field_initial_constraints, try_transition_constraints_with_fire, FireTracking,
    LassoLoop, SlotPool,
};
use super::ic3;
use super::property::{encode_prop_expr_with_ctx, PropertyCtx};
use super::scope::{
    allocate_initial_activations, compute_theorem_scope, compute_verify_scope,
    select_verify_relevant, VerifyStoreRange,
};
use super::smt::{self, AbideSolver, Bool, SatResult, SmtValue};
use super::temporal::{CompiledTemporalFormula, LivenessPattern};
use super::walkers::count_entity_quantifiers;

/// Backend-neutral assumption set for a transition obligation.
///
/// Built from an [`IRAssumptionSet`] plus any extern-boundary
/// assumption expressions in scope. Event keys are stored as
/// `(system, command)` pairs because they are projected into the
/// solver's identifier space before backend encoding.
#[derive(Debug, Clone)]
pub struct TransitionAssumptions {
    stutter: bool,
    stutter_provenance: IRStutterProvenance,
    weak_fair_event_keys: Vec<(String, String)>,
    strong_fair_event_keys: Vec<(String, String)>,
    per_tuple_fair_event_keys: Vec<(String, String)>,
    extern_assume_exprs: Vec<IRExpr>,
}

impl TransitionAssumptions {
    fn from_ir(set: &IRAssumptionSet) -> Self {
        Self {
            stutter: set.stutter,
            stutter_provenance: set.stutter_provenance,
            weak_fair_event_keys: set
                .weak_fair
                .iter()
                .map(|event| (event.system.clone(), event.command.clone()))
                .collect(),
            strong_fair_event_keys: set
                .strong_fair
                .iter()
                .map(|event| (event.system.clone(), event.command.clone()))
                .collect(),
            per_tuple_fair_event_keys: set
                .per_tuple
                .iter()
                .map(|event| (event.system.clone(), event.command.clone()))
                .collect(),
            extern_assume_exprs: Vec::new(),
        }
    }

    fn with_reachable_extern_assumptions(
        mut self,
        ir: &IRProgram,
        system_names: &[String],
    ) -> Self {
        let mut to_scan = system_names.to_vec();
        let mut scanned = HashSet::new();

        while let Some(system_name) = to_scan.pop() {
            if !scanned.insert(system_name.clone()) {
                continue;
            }
            let Some(system) = ir.systems.iter().find(|system| system.name == system_name) else {
                continue;
            };

            if system
                .preds
                .iter()
                .any(|pred| pred.name == "__abide_extern__marker")
            {
                for pred in &system.preds {
                    if let Some(command) = pred.name.strip_prefix("__abide_extern_assume_wf__") {
                        self.push_weak_fair(system.name.clone(), command.to_owned());
                    } else if let Some(command) =
                        pred.name.strip_prefix("__abide_extern_assume_sf__")
                    {
                        self.push_strong_fair(system.name.clone(), command.to_owned());
                    } else if pred
                        .name
                        .strip_prefix("__abide_extern_assume_expr__")
                        .is_some()
                    {
                        self.extern_assume_exprs.push(pred.body.clone());
                    }
                }
            }

            for action in &system.actions {
                super::scope::collect_crosscall_systems(&action.body, &mut to_scan);
            }
            for binding in &system.let_bindings {
                if !to_scan.contains(&binding.system_type) {
                    to_scan.push(binding.system_type.clone());
                }
            }
        }

        self
    }

    fn push_weak_fair(&mut self, system: String, command: String) {
        let event = (system, command);
        if !self.weak_fair_event_keys.contains(&event)
            && !self.strong_fair_event_keys.contains(&event)
        {
            self.weak_fair_event_keys.push(event);
        }
    }

    fn push_strong_fair(&mut self, system: String, command: String) {
        let event = (system, command);
        self.weak_fair_event_keys
            .retain(|existing| existing != &event);
        if !self.strong_fair_event_keys.contains(&event) {
            self.strong_fair_event_keys.push(event);
        }
    }

    pub fn as_ir_assumption_set(&self) -> IRAssumptionSet {
        IRAssumptionSet {
            stutter: self.stutter,
            stutter_provenance: self.stutter_provenance,
            weak_fair: self
                .weak_fair_event_keys
                .iter()
                .map(|(system, command)| IRCommandRef {
                    system: system.clone(),
                    command: command.clone(),
                })
                .collect(),
            strong_fair: self
                .strong_fair_event_keys
                .iter()
                .map(|(system, command)| IRCommandRef {
                    system: system.clone(),
                    command: command.clone(),
                })
                .collect(),
            per_tuple: self
                .per_tuple_fair_event_keys
                .iter()
                .map(|(system, command)| IRCommandRef {
                    system: system.clone(),
                    command: command.clone(),
                })
                .collect(),
        }
    }

    pub fn stutter(&self) -> bool {
        self.stutter
    }

    pub fn weak_fair_event_keys(&self) -> &[(String, String)] {
        &self.weak_fair_event_keys
    }

    pub fn strong_fair_event_keys(&self) -> &[(String, String)] {
        &self.strong_fair_event_keys
    }

    pub fn per_tuple_fair_event_keys(&self) -> &[(String, String)] {
        &self.per_tuple_fair_event_keys
    }

    pub fn all_fair_event_keys(&self) -> Vec<(String, String)> {
        let mut out = self.weak_fair_event_keys.clone();
        for event in &self.strong_fair_event_keys {
            if !out.contains(event) {
                out.push(event.clone());
            }
        }
        out
    }

    pub fn extern_assume_exprs(&self) -> &[IRExpr] {
        &self.extern_assume_exprs
    }
}

/// Backend-neutral transition-system specification at a verification
/// site. Bundles the IR, verifier context, the selected sub-system
/// scope, slot bounds, assumption set, and initial constraints.
#[derive(Clone)]
pub struct TransitionSystemSpec<'a> {
    pub ir: &'a IRProgram,
    pub vctx: &'a VerifyContext,
    selected_system_names: Vec<String>,
    system_names: Vec<String>,
    slots_per_entity: HashMap<String, usize>,
    bound: usize,
    store_ranges: HashMap<String, VerifyStoreRange>,
    assumptions: TransitionAssumptions,
    activations: Vec<crate::ir::types::IRActivation>,
    initial_constraints: Vec<IRExpr>,
    relevant_entities: Vec<IREntity>,
    relevant_systems: Vec<IRSystem>,
}

pub struct TransitionSelectedParts {
    pub selected_system_names: Vec<String>,
    pub relevant_entities: Vec<IREntity>,
    pub relevant_systems: Vec<IRSystem>,
    pub slots_per_entity: HashMap<String, usize>,
    pub bound: usize,
    pub store_ranges: HashMap<String, VerifyStoreRange>,
    pub activations: Vec<crate::ir::types::IRActivation>,
    pub initial_constraints: Vec<IRExpr>,
}

struct TransitionVerifyScopeParts {
    selected_system_names: Vec<String>,
    system_names: Vec<String>,
    slots_per_entity: HashMap<String, usize>,
    bound: usize,
    store_ranges: HashMap<String, VerifyStoreRange>,
    assumptions: TransitionAssumptions,
    activations: Vec<crate::ir::types::IRActivation>,
    initial_constraints: Vec<IRExpr>,
}

impl<'a> TransitionSystemSpec<'a> {
    pub fn from_selected(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        parts: TransitionSelectedParts,
        assumption_set: &IRAssumptionSet,
    ) -> Option<Self> {
        let TransitionSelectedParts {
            selected_system_names,
            relevant_entities,
            relevant_systems,
            slots_per_entity,
            bound,
            store_ranges,
            activations,
            initial_constraints,
        } = parts;
        let system_names: Vec<String> = relevant_systems.iter().map(|s| s.name.clone()).collect();
        if system_names.is_empty() {
            return None;
        }
        let assumptions = TransitionAssumptions::from_ir(assumption_set)
            .with_reachable_extern_assumptions(ir, &system_names);
        Some(Self {
            ir,
            vctx,
            selected_system_names,
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            assumptions,
            activations,
            initial_constraints,
            relevant_entities,
            relevant_systems,
        })
    }

    fn from_verify_scope_parts(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        parts: TransitionVerifyScopeParts,
    ) -> Option<Self> {
        let TransitionVerifyScopeParts {
            selected_system_names,
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            assumptions,
            activations,
            initial_constraints,
        } = parts;
        if system_names.is_empty() {
            return None;
        }
        let (relevant_entities, relevant_systems) =
            select_verify_relevant(ir, &slots_per_entity, &system_names);
        let assumptions = assumptions.with_reachable_extern_assumptions(ir, &system_names);
        Some(Self {
            ir,
            vctx,
            selected_system_names,
            system_names,
            slots_per_entity,
            bound,
            store_ranges,
            assumptions,
            activations,
            initial_constraints,
            relevant_entities,
            relevant_systems,
        })
    }

    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let (mut slots_per_entity, system_names, bound, store_ranges) =
            compute_verify_scope(ir, verify_block);
        if system_names.is_empty() {
            return None;
        }
        for assert_expr in &verify_block.asserts {
            let expanded = super::expand_through_defs(assert_expr, defs);
            let mut counts: HashMap<String, usize> = HashMap::new();
            count_entity_quantifiers(&expanded, &mut counts);
            for (entity, count) in counts {
                let min_slots = count + 1;
                if let Some(existing) = slots_per_entity.get_mut(&entity) {
                    *existing = (*existing).max(min_slots);
                }
            }
        }
        Self::from_verify_scope_parts(
            ir,
            vctx,
            TransitionVerifyScopeParts {
                selected_system_names: verify_block
                    .systems
                    .iter()
                    .map(|sys| sys.name.clone())
                    .collect(),
                system_names,
                slots_per_entity,
                bound,
                store_ranges,
                assumptions: TransitionAssumptions::from_ir(&verify_block.assumption_set),
                activations: verify_block.activations.clone(),
                initial_constraints: verify_block.initial_constraints.clone(),
            },
        )
    }

    pub fn for_verify_shallow(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
    ) -> Option<Self> {
        let (slots_per_entity, system_names, bound, store_ranges) =
            compute_verify_scope(ir, verify_block);
        Self::from_verify_scope_parts(
            ir,
            vctx,
            TransitionVerifyScopeParts {
                selected_system_names: verify_block
                    .systems
                    .iter()
                    .map(|sys| sys.name.clone())
                    .collect(),
                system_names,
                slots_per_entity,
                bound,
                store_ranges,
                assumptions: TransitionAssumptions::from_ir(&verify_block.assumption_set),
                activations: verify_block.activations.clone(),
                initial_constraints: verify_block.initial_constraints.clone(),
            },
        )
    }

    pub fn for_theorem(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        theorem: &IRTheorem,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let quantifier_exprs: Vec<&IRExpr> = theorem.shows.iter().collect();
        let scope = compute_theorem_scope(ir, theorem, &quantifier_exprs, defs);
        if scope.system_names.is_empty() {
            return None;
        }
        let (relevant_entities, relevant_systems) =
            select_verify_relevant(ir, &scope.slots_per_entity, &scope.system_names);
        let assumptions = TransitionAssumptions::from_ir(&theorem.assumption_set)
            .with_reachable_extern_assumptions(ir, &scope.system_names);

        Some(Self {
            ir,
            vctx,
            selected_system_names: theorem.systems.clone(),
            system_names: scope.system_names,
            slots_per_entity: scope.slots_per_entity,
            bound: 0,
            store_ranges: scope.store_ranges,
            assumptions,
            activations: vec![],
            initial_constraints: vec![],
            relevant_entities,
            relevant_systems,
        })
    }

    pub fn system_names(&self) -> &[String] {
        &self.system_names
    }

    pub fn selected_system_names(&self) -> &[String] {
        &self.selected_system_names
    }

    pub fn slots_per_entity(&self) -> &HashMap<String, usize> {
        &self.slots_per_entity
    }

    pub fn assumptions(&self) -> &TransitionAssumptions {
        &self.assumptions
    }

    pub fn bound(&self) -> usize {
        self.bound
    }

    pub fn store_ranges(&self) -> &HashMap<String, VerifyStoreRange> {
        &self.store_ranges
    }

    pub fn initial_constraints(&self) -> &[IRExpr] {
        &self.initial_constraints
    }

    pub fn activations(&self) -> &[crate::ir::types::IRActivation] {
        &self.activations
    }

    pub fn relevant_entities(&self) -> &[IREntity] {
        &self.relevant_entities
    }

    pub fn relevant_systems(&self) -> &[IRSystem] {
        &self.relevant_systems
    }
}

/// Safety obligation: every step of the [`TransitionSystemSpec`] must
/// satisfy each `step_properties` predicate. Used by ordinary safety
/// checking (verify blocks, prop targets).
#[derive(Clone)]
pub struct TransitionSafetySpec<'a> {
    system: TransitionSystemSpec<'a>,
    step_properties: Vec<IRExpr>,
}

impl<'a> TransitionSafetySpec<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let system = TransitionSystemSpec::for_verify(ir, vctx, verify_block, defs)?;
        let step_properties = verify_block
            .asserts
            .iter()
            .map(|assert_expr| {
                let expanded = super::expand_through_defs(assert_expr, defs);
                let step_property = match expanded {
                    IRExpr::Always { body, .. } => *body,
                    other => other,
                };
                simplify_static_bool_fragments(step_property, vctx, defs)
            })
            .collect();
        Some(Self {
            system,
            step_properties,
        })
    }

    pub fn for_theorem(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        theorem: &IRTheorem,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let system = TransitionSystemSpec::for_theorem(ir, vctx, theorem, defs)?;
        let step_properties = theorem
            .shows
            .iter()
            .map(|show_expr| super::expand_through_defs(show_expr, defs))
            .collect();
        Some(Self {
            system,
            step_properties,
        })
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn step_properties(&self) -> &[IRExpr] {
        &self.step_properties
    }

    pub fn step_property(&self, index: usize) -> Option<&IRExpr> {
        self.step_properties.get(index)
    }

    pub fn combined_step_property(&self) -> Option<IRExpr> {
        let mut iter = self.step_properties.iter().cloned();
        let first = iter.next()?;
        Some(iter.fold(first, |left, right| IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }))
    }

    pub fn obligation(&self, property_index: usize, timeout_ms: u64) -> TransitionObligation<'a> {
        TransitionObligation::SystemSafety {
            safety: self.clone(),
            property_index,
            timeout_ms,
        }
    }
}

fn simplify_static_bool_fragments(
    expr: IRExpr,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> IRExpr {
    if let Some(value) = static_bool_value(&expr, vctx, defs) {
        return bool_lit(value);
    }
    match expr {
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            span,
        } if op == "OpAnd" || op == "and" || op == "&&" => {
            simplify_static_and(op, *left, *right, ty, span, vctx, defs)
        }
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            span,
        } if op == "OpOr" || op == "or" || op == "||" => {
            simplify_static_or(op, *left, *right, ty, span, vctx, defs)
        }
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } => IRExpr::Forall {
            var,
            domain,
            body: Box::new(simplify_static_bool_fragments(*body, vctx, defs)),
            span,
        },
        IRExpr::Exists {
            var,
            domain,
            body,
            span,
        } => IRExpr::Exists {
            var,
            domain,
            body: Box::new(simplify_static_bool_fragments(*body, vctx, defs)),
            span,
        },
        other => other,
    }
}

fn simplify_static_and(
    op: String,
    left: IRExpr,
    right: IRExpr,
    ty: crate::ir::types::IRType,
    span: Option<crate::span::Span>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> IRExpr {
    let left = simplify_static_bool_fragments(left, vctx, defs);
    let right = simplify_static_bool_fragments(right, vctx, defs);
    match (literal_bool(&left), literal_bool(&right)) {
        (Some(false), _) | (_, Some(false)) => bool_lit(false),
        (Some(true), _) => right,
        (_, Some(true)) => left,
        _ => IRExpr::BinOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
            ty,
            span,
        },
    }
}

fn simplify_static_or(
    op: String,
    left: IRExpr,
    right: IRExpr,
    ty: crate::ir::types::IRType,
    span: Option<crate::span::Span>,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> IRExpr {
    let left = simplify_static_bool_fragments(left, vctx, defs);
    let right = simplify_static_bool_fragments(right, vctx, defs);
    match (literal_bool(&left), literal_bool(&right)) {
        (Some(true), _) | (_, Some(true)) => bool_lit(true),
        (Some(false), _) => right,
        (_, Some(false)) => left,
        _ => IRExpr::BinOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
            ty,
            span,
        },
    }
}

fn static_bool_value(expr: &IRExpr, vctx: &VerifyContext, defs: &defenv::DefEnv) -> Option<bool> {
    if !is_closed_static_expr(expr, &HashSet::new()) {
        return None;
    }
    let encoded = encode_pure_expr(expr, &HashMap::new(), vctx, defs)
        .ok()?
        .to_bool()
        .ok()?;
    if is_unsat(&smt::bool_not(&encoded)) {
        return Some(true);
    }
    is_unsat(&encoded).then_some(false)
}

fn is_closed_static_expr(expr: &IRExpr, locals: &HashSet<String>) -> bool {
    match expr {
        IRExpr::Lit { .. } => true,
        IRExpr::Var { name, ty, .. } => {
            locals.contains(name) || matches!(ty, crate::ir::types::IRType::Enum { .. })
        }
        IRExpr::Ctor { args, .. } => args
            .iter()
            .all(|(_, arg)| is_closed_static_expr(arg, locals)),
        IRExpr::Field { expr, .. } => is_closed_static_expr(expr, locals),
        IRExpr::BinOp { left, right, .. } => {
            is_closed_static_expr(left, locals) && is_closed_static_expr(right, locals)
        }
        IRExpr::UnOp { operand, .. } | IRExpr::Card { expr: operand, .. } => {
            is_closed_static_expr(operand, locals)
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements
            .iter()
            .all(|element| is_closed_static_expr(element, locals)),
        IRExpr::MapLit { entries, .. } => entries.iter().all(|(key, value)| {
            is_closed_static_expr(key, locals) && is_closed_static_expr(value, locals)
        }),
        IRExpr::SetComp {
            var,
            domain,
            source,
            filter,
            projection,
            ..
        } => {
            if matches!(domain, crate::ir::types::IRType::Entity { .. }) {
                return false;
            }
            if let Some(source) = source {
                if !is_closed_static_expr(source, locals) {
                    return false;
                }
            } else if !matches!(
                domain,
                crate::ir::types::IRType::Bool | crate::ir::types::IRType::Enum { .. }
            ) {
                return false;
            }
            let mut nested = locals.clone();
            nested.insert(var.clone());
            is_closed_static_expr(filter, &nested)
                && projection
                    .as_ref()
                    .is_none_or(|projection| is_closed_static_expr(projection, &nested))
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut nested = locals.clone();
            for binding in bindings {
                if !is_closed_static_expr(&binding.expr, &nested) {
                    return false;
                }
                nested.insert(binding.name.clone());
            }
            is_closed_static_expr(body, &nested)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            is_closed_static_expr(cond, locals)
                && is_closed_static_expr(then_body, locals)
                && else_body
                    .as_ref()
                    .is_none_or(|else_body| is_closed_static_expr(else_body, locals))
        }
        IRExpr::Forall {
            var, domain, body, ..
        }
        | IRExpr::Exists {
            var, domain, body, ..
        } => {
            if matches!(domain, crate::ir::types::IRType::Entity { .. }) {
                return false;
            }
            if !matches!(
                domain,
                crate::ir::types::IRType::Bool | crate::ir::types::IRType::Enum { .. }
            ) {
                return false;
            }
            let mut nested = locals.clone();
            nested.insert(var.clone());
            is_closed_static_expr(body, &nested)
        }
        _ => false,
    }
}

fn is_unsat(expr: &Bool) -> bool {
    let solver = AbideSolver::new();
    solver.assert(expr);
    solver.check() == SatResult::Unsat
}

fn literal_bool(expr: &IRExpr) -> Option<bool> {
    match expr {
        IRExpr::Lit {
            value: crate::ir::types::LitVal::Bool { value },
            ..
        } => Some(*value),
        _ => None,
    }
}

fn bool_lit(value: bool) -> IRExpr {
    IRExpr::Lit {
        ty: crate::ir::types::IRType::Bool,
        value: crate::ir::types::LitVal::Bool { value },
        span: None,
    }
}

/// `verify`-block obligation: the system spec plus the compiled
/// temporal asserts. `safety` projects out the always-prefix shape
/// suitable for ordinary safety encoding; assertions with stronger
/// temporal shape (e.g. liveness) are kept in `compiled_asserts` for
/// the liveness backend.
#[derive(Clone)]
pub struct TransitionVerifySpec<'a> {
    system: TransitionSystemSpec<'a>,
    compiled_asserts: Vec<CompiledTemporalFormula>,
    safety: TransitionSafetySpec<'a>,
}

impl<'a> TransitionVerifySpec<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let system = TransitionSystemSpec::for_verify(ir, vctx, verify_block, defs)?;
        let compiled_asserts: Vec<CompiledTemporalFormula> = verify_block
            .asserts
            .iter()
            .map(|assert_expr| {
                let expanded = super::expand_through_defs(assert_expr, defs);
                let temporal_scope = match expanded {
                    IRExpr::Always { .. } => expanded,
                    other => IRExpr::Always {
                        body: Box::new(other),
                        span: None,
                    },
                };
                CompiledTemporalFormula::from_expanded(temporal_scope)
            })
            .collect();
        let step_properties = compiled_asserts
            .iter()
            .map(|compiled| match compiled.expanded().clone() {
                IRExpr::Always { body, .. } => *body,
                other => other,
            })
            .map(|property| simplify_static_bool_fragments(property, vctx, defs))
            .collect();
        Some(Self {
            system: system.clone(),
            compiled_asserts,
            safety: TransitionSafetySpec {
                system,
                step_properties,
            },
        })
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn safety(&self) -> &TransitionSafetySpec<'a> {
        &self.safety
    }

    pub fn compiled_asserts(&self) -> &[CompiledTemporalFormula] {
        &self.compiled_asserts
    }

    pub fn has_liveness(&self) -> bool {
        self.compiled_asserts
            .iter()
            .any(CompiledTemporalFormula::contains_liveness)
    }
}

/// Fully assembled verify obligation ready to hand to a backend.
/// Includes the `verify` spec plus precomputed projections (fair
/// events, etc.) needed by the dispatchers in this module.
#[derive(Clone)]
pub struct TransitionVerifyObligation<'a> {
    verify: TransitionVerifySpec<'a>,
    fair_event_keys: Vec<(String, String)>,
    liveness: Option<TransitionLivenessSpec<'a>>,
}

impl<'a> TransitionVerifyObligation<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let verify = TransitionVerifySpec::for_verify(ir, vctx, verify_block, defs)?;
        let fair_event_keys = verify.system().assumptions().all_fair_event_keys();
        let liveness = TransitionLivenessSpec::from_verify_spec(verify.clone(), defs);
        Some(Self {
            verify,
            fair_event_keys,
            liveness,
        })
    }

    pub fn verify(&self) -> &TransitionVerifySpec<'a> {
        &self.verify
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        self.verify.system()
    }

    pub fn safety(&self) -> &TransitionSafetySpec<'a> {
        self.verify.safety()
    }

    pub fn fair_event_keys(&self) -> &[(String, String)] {
        &self.fair_event_keys
    }

    pub fn liveness(&self) -> Option<&TransitionLivenessSpec<'a>> {
        self.liveness.as_ref()
    }

    pub fn has_liveness(&self) -> bool {
        self.verify.has_liveness()
    }

    pub fn has_supported_liveness(&self) -> bool {
        self.liveness.is_some()
    }

    pub fn deadlock_plan(&self) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_deadlock_probe(self.system().clone())
    }

    pub fn prefix_plan(&self, steps: usize) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_prefix_probe(self.system().clone(), steps)
    }

    pub fn bmc_plan(&self) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_bmc(self.system().clone(), self.system().bound())
    }

    pub fn lasso_plan(&self) -> TransitionExecutionPlan<'a> {
        TransitionExecutionPlan::for_lasso(self.system().clone(), self.system().bound())
    }
}

/// Pre-built SMT encoding for a transition obligation: slot pool,
/// initial/domain/symmetry constraints, fire tracking, and the
/// optional lasso loopback constraint. Plans (`TransitionExecutionPlan`)
/// pick which subset to assert.
pub struct TransitionSmtEncoding<'a> {
    system: TransitionSystemSpec<'a>,
    pool: SlotPool,
    initial_constraints: Vec<Bool>,
    system_initial_constraints: Vec<Bool>,
    symmetry_constraints: Vec<Bool>,
    domain_constraints: Vec<Bool>,
    fire_tracking: FireTracking,
    lasso: Option<LassoLoop>,
    fairness_constraints: Vec<Bool>,
}

fn try_extern_assume_expr_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    exprs: &[IRExpr],
    steps: usize,
) -> Result<Vec<Bool>, String> {
    let params: HashMap<String, SmtValue> = HashMap::new();
    let store_param_types: HashMap<String, String> = HashMap::new();
    let mut constraints = Vec::new();
    for expr in exprs {
        for step in 0..=steps {
            constraints.push(try_encode_guard_expr(
                pool,
                vctx,
                expr,
                &params,
                &store_param_types,
                step,
            )?);
        }
    }
    Ok(constraints)
}

/// One scheduled run of the [`TransitionSmtEncoding`] — narrows the
/// encoding to the specific shape needed by one tier (deadlock probe,
/// finite prefix, BMC, lasso liveness).
#[derive(Clone)]
pub struct TransitionExecutionPlan<'a> {
    system: TransitionSystemSpec<'a>,
    steps: usize,
    include_system_initial_constraints: bool,
    include_symmetry_constraints: bool,
    include_lasso_and_fairness: bool,
}

impl<'a> TransitionExecutionPlan<'a> {
    fn new(
        system: TransitionSystemSpec<'a>,
        steps: usize,
        include_system_initial_constraints: bool,
        include_symmetry_constraints: bool,
        include_lasso_and_fairness: bool,
    ) -> Self {
        Self {
            system,
            steps,
            include_system_initial_constraints,
            include_symmetry_constraints,
            include_lasso_and_fairness,
        }
    }

    pub fn for_deadlock_probe(system: TransitionSystemSpec<'a>) -> Self {
        Self::new(system, 1, false, false, false)
    }

    pub fn for_prefix_probe(system: TransitionSystemSpec<'a>, steps: usize) -> Self {
        Self::new(system, steps, true, false, false)
    }

    pub fn for_bmc(system: TransitionSystemSpec<'a>, steps: usize) -> Self {
        Self::new(system, steps, true, true, false)
    }

    pub fn for_lasso(system: TransitionSystemSpec<'a>, steps: usize) -> Self {
        Self::new(system, steps, true, true, true)
    }

    pub fn for_inductive_step(system: TransitionSystemSpec<'a>) -> Self {
        Self::new(system, 1, false, false, false)
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn steps(&self) -> usize {
        self.steps
    }

    pub fn include_system_initial_constraints(&self) -> bool {
        self.include_system_initial_constraints
    }

    pub fn include_symmetry_constraints(&self) -> bool {
        self.include_symmetry_constraints
    }

    pub fn include_lasso_and_fairness(&self) -> bool {
        self.include_lasso_and_fairness
    }
}

impl<'a> TransitionSmtEncoding<'a> {
    pub fn from_plan(plan: TransitionExecutionPlan<'a>) -> Result<Self, String> {
        let system = plan.system;
        let steps = plan.steps;
        let assumption_set = system.assumptions().as_ir_assumption_set();
        let pool = create_slot_pool_with_systems(
            system.relevant_entities(),
            system.slots_per_entity(),
            steps,
            system.relevant_systems(),
        );
        let initial_bindings =
            allocate_initial_activations(system.store_ranges(), system.activations())?;
        let initial_active_slots = initial_active_slots_with_store_ranges(
            &initial_bindings.active_slots,
            system.store_ranges(),
        );
        let mut initial_constraints = initial_state_constraints_with_store_ranges(
            &pool,
            &initial_bindings.active_slots,
            system.store_ranges(),
        );
        initial_constraints.extend(try_entity_field_initial_constraints(
            &pool,
            system.vctx,
            system.relevant_entities(),
            &initial_active_slots,
        )?);
        initial_constraints.extend(store_active_cardinality_constraints(
            &pool,
            system.store_ranges(),
        ));
        if !system.initial_constraints().is_empty() {
            let defs = defenv::DefEnv::from_ir(system.ir);
            let ctx = PropertyCtx::new()
                .with_store_ranges(system.store_ranges().clone())
                .with_given_bindings(&initial_bindings.bindings);
            for expr in system.initial_constraints() {
                initial_constraints.push(encode_prop_expr_with_ctx(
                    &pool,
                    system.vctx,
                    &defs,
                    &ctx,
                    expr,
                    0,
                )?);
            }
        }
        let system_initial_constraints = if plan.include_system_initial_constraints {
            let mut out = Vec::new();
            for sys in system.relevant_systems() {
                out.extend(try_system_field_initial_constraints(
                    &pool,
                    system.vctx,
                    sys,
                )?);
            }
            out
        } else {
            Vec::new()
        };
        let symmetry_constraints = if plan.include_symmetry_constraints {
            symmetry_breaking_constraints(&pool)
        } else {
            Vec::new()
        };
        let mut domain_constraints =
            domain_constraints(&pool, system.vctx, system.relevant_entities());
        domain_constraints.extend(try_extern_assume_expr_constraints(
            &pool,
            system.vctx,
            system.assumptions().extern_assume_exprs(),
            steps,
        )?);
        let fire_tracking = try_transition_constraints_with_fire(
            &pool,
            system.vctx,
            system.relevant_entities(),
            system.relevant_systems(),
            steps,
            &assumption_set,
        )?;
        let (lasso, fairness_constraints) = if plan.include_lasso_and_fairness {
            let lasso =
                lasso_loopback(&pool, system.relevant_entities(), system.relevant_systems());
            let fairness_constraints = try_fairness_constraints(
                &pool,
                system.vctx,
                system.relevant_entities(),
                system.relevant_systems(),
                &fire_tracking,
                &lasso,
                &assumption_set,
            )?;
            (Some(lasso), fairness_constraints)
        } else {
            (None, Vec::new())
        };

        Ok(Self {
            system,
            pool,
            initial_constraints,
            system_initial_constraints,
            symmetry_constraints,
            domain_constraints,
            fire_tracking,
            lasso,
            fairness_constraints,
        })
    }

    pub fn for_deadlock_probe(system: TransitionSystemSpec<'a>) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_deadlock_probe(system))
    }

    pub fn for_prefix_probe(
        system: TransitionSystemSpec<'a>,
        steps: usize,
    ) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_prefix_probe(system, steps))
    }

    pub fn for_bmc(system: TransitionSystemSpec<'a>, steps: usize) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_bmc(system, steps))
    }

    pub fn for_lasso(system: TransitionSystemSpec<'a>, steps: usize) -> Result<Self, String> {
        Self::from_plan(TransitionExecutionPlan::for_lasso(system, steps))
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        &self.system
    }

    pub fn pool(&self) -> &SlotPool {
        &self.pool
    }

    pub fn initial_constraints(&self) -> &[Bool] {
        &self.initial_constraints
    }

    pub fn system_initial_constraints(&self) -> &[Bool] {
        &self.system_initial_constraints
    }

    pub fn symmetry_constraints(&self) -> &[Bool] {
        &self.symmetry_constraints
    }

    pub fn domain_constraints(&self) -> &[Bool] {
        &self.domain_constraints
    }

    pub fn fire_tracking(&self) -> &FireTracking {
        &self.fire_tracking
    }

    pub fn lasso(&self) -> Option<&LassoLoop> {
        self.lasso.as_ref()
    }

    pub fn fairness_constraints(&self) -> &[Bool] {
        &self.fairness_constraints
    }
}

#[derive(Clone)]
pub struct TransitionLivenessMonitorRecipe {
    assert_index: usize,
    trigger: Option<IRExpr>,
    response: IRExpr,
    quant_var: Option<String>,
    quant_entity: Option<String>,
    slot_count: usize,
    is_oneshot: bool,
}

impl TransitionLivenessMonitorRecipe {
    fn from_pattern(
        assert_index: usize,
        pattern: &LivenessPattern,
        system: &TransitionSystemSpec<'_>,
    ) -> Self {
        let (trigger, response, quant_var, quant_entity) = match pattern {
            LivenessPattern::Response { trigger, response } => {
                (Some(trigger.clone()), response.clone(), None, None)
            }
            LivenessPattern::Recurrence { response }
            | LivenessPattern::Eventuality { response } => (None, response.clone(), None, None),
            LivenessPattern::Persistence { condition } => (None, condition.clone(), None, None),
            LivenessPattern::QuantifiedResponse {
                var,
                entity,
                trigger,
                response,
            } => (
                Some(trigger.clone()),
                response.clone(),
                Some(var.clone()),
                Some(entity.clone()),
            ),
            LivenessPattern::QuantifiedRecurrence {
                var,
                entity,
                response,
            }
            | LivenessPattern::QuantifiedEventuality {
                var,
                entity,
                response,
            } => (
                None,
                response.clone(),
                Some(var.clone()),
                Some(entity.clone()),
            ),
            LivenessPattern::QuantifiedPersistence {
                var,
                entity,
                condition,
            } => (
                None,
                condition.clone(),
                Some(var.clone()),
                Some(entity.clone()),
            ),
        };
        let slot_count = quant_entity
            .as_ref()
            .and_then(|entity| system.slots_per_entity().get(entity).copied())
            .unwrap_or(1);

        Self {
            assert_index,
            trigger,
            response,
            quant_var,
            quant_entity,
            slot_count,
            is_oneshot: pattern.is_oneshot(),
        }
    }

    pub fn assert_index(&self) -> usize {
        self.assert_index
    }

    pub fn trigger<'a>(&'a self, true_expr: &'a IRExpr) -> &'a IRExpr {
        self.trigger.as_ref().unwrap_or(true_expr)
    }

    pub fn response(&self) -> &IRExpr {
        &self.response
    }

    pub fn quantified_binding(&self) -> (Option<&str>, Option<&str>) {
        (self.quant_var.as_deref(), self.quant_entity.as_deref())
    }

    pub fn slot_count(&self) -> usize {
        self.slot_count
    }

    pub fn is_quantified(&self) -> bool {
        self.quant_entity.is_some()
    }

    pub fn is_oneshot(&self) -> bool {
        self.is_oneshot
    }
}

#[derive(Clone)]
pub struct TransitionLivenessSpec<'a> {
    verify: TransitionVerifySpec<'a>,
    patterns: Vec<(usize, LivenessPattern)>,
    safety_obligations: Vec<IRExpr>,
    recipes: Vec<TransitionLivenessMonitorRecipe>,
}

impl<'a> TransitionLivenessSpec<'a> {
    pub fn for_verify(
        ir: &'a IRProgram,
        vctx: &'a VerifyContext,
        verify_block: &IRVerify,
        defs: &defenv::DefEnv,
    ) -> Option<Self> {
        let verify = TransitionVerifySpec::for_verify(ir, vctx, verify_block, defs)?;
        Self::from_verify_spec(verify, defs)
    }

    fn from_verify_spec(verify: TransitionVerifySpec<'a>, _defs: &defenv::DefEnv) -> Option<Self> {
        let mut patterns = Vec::new();
        let mut safety_obligations = Vec::new();
        let mut has_unrecognized_liveness = false;
        for (i, compiled) in verify.compiled_asserts().iter().enumerate() {
            if compiled.contains_liveness() {
                if let Some(extraction) = compiled.extraction().cloned() {
                    patterns.push((i, extraction.pattern));
                    safety_obligations.extend(extraction.safety_conjuncts);
                } else {
                    has_unrecognized_liveness = true;
                }
            } else {
                safety_obligations.push(compiled.expanded().clone());
            }
        }
        if patterns.is_empty() || has_unrecognized_liveness {
            return None;
        }
        let recipes = patterns
            .iter()
            .map(|(assert_index, pattern)| {
                TransitionLivenessMonitorRecipe::from_pattern(
                    *assert_index,
                    pattern,
                    verify.system(),
                )
            })
            .collect();
        Some(Self {
            verify,
            patterns,
            safety_obligations,
            recipes,
        })
    }

    pub fn verify(&self) -> &TransitionVerifySpec<'a> {
        &self.verify
    }

    pub fn system(&self) -> &TransitionSystemSpec<'a> {
        self.verify.system()
    }

    pub fn patterns(&self) -> &[(usize, LivenessPattern)] {
        &self.patterns
    }

    pub fn pattern(&self, index: usize) -> Option<&LivenessPattern> {
        self.patterns.get(index).map(|(_, pattern)| pattern)
    }

    pub fn safety_obligations(&self) -> &[IRExpr] {
        &self.safety_obligations
    }

    pub fn has_quantified_patterns(&self) -> bool {
        self.recipes
            .iter()
            .any(TransitionLivenessMonitorRecipe::is_quantified)
    }

    pub fn recipes(&self) -> &[TransitionLivenessMonitorRecipe] {
        &self.recipes
    }

    pub fn recipe(&self, index: usize) -> Option<&TransitionLivenessMonitorRecipe> {
        self.recipes.get(index)
    }

    pub fn pattern_slot_count(&self, pattern_index: usize) -> Option<usize> {
        Some(self.recipe(pattern_index)?.slot_count())
    }

    pub fn obligation(
        &self,
        recipe_index: usize,
        target_slot: Option<usize>,
        timeout_ms: u64,
    ) -> TransitionObligation<'a> {
        TransitionObligation::SystemLiveness {
            liveness: self.clone(),
            recipe_index,
            target_slot,
            timeout_ms,
        }
    }
}

pub use super::ic3::{Ic3Result as TransitionResult, Ic3TraceStep as TransitionTraceStep};

/// A transition-system obligation, independent of the current backend.
pub enum TransitionObligation<'a> {
    SingleEntitySafety {
        entity: &'a IREntity,
        vctx: &'a VerifyContext,
        property: &'a IRExpr,
        timeout_ms: u64,
    },
    MultiSlotSafety {
        entity: &'a IREntity,
        vctx: &'a VerifyContext,
        property: &'a IRExpr,
        n_slots: usize,
        timeout_ms: u64,
    },
    SystemSafety {
        safety: TransitionSafetySpec<'a>,
        property_index: usize,
        timeout_ms: u64,
    },
    SystemLiveness {
        liveness: TransitionLivenessSpec<'a>,
        recipe_index: usize,
        target_slot: Option<usize>,
        timeout_ms: u64,
    },
}

/// Transition-system backends consume backend-neutral obligations and return the
/// shared transition result shape.
pub trait TransitionBackend {
    fn solve(obligation: TransitionObligation<'_>) -> TransitionResult;
}

/// Current transition backend: the existing IC3/CHC path.
pub struct Ic3TransitionBackend;

impl TransitionBackend for Ic3TransitionBackend {
    fn solve(obligation: TransitionObligation<'_>) -> TransitionResult {
        match obligation {
            TransitionObligation::SingleEntitySafety {
                entity,
                vctx,
                property,
                timeout_ms,
            } => ic3::try_ic3_single_entity_with_semantics(
                entity,
                vctx,
                property,
                ic3::Ic3TransitionSemantics::default(),
                timeout_ms,
            ),
            TransitionObligation::MultiSlotSafety {
                entity,
                vctx,
                property,
                n_slots,
                timeout_ms,
            } => ic3::try_ic3_multi_slot_with_semantics(
                entity,
                vctx,
                property,
                n_slots,
                ic3::Ic3TransitionSemantics::default(),
                timeout_ms,
            ),
            TransitionObligation::SystemSafety {
                safety,
                property_index,
                timeout_ms,
            } => {
                let system = safety.system();
                let Some(property) = safety.step_property(property_index) else {
                    return TransitionResult::Unknown(format!(
                        "invalid transition safety property index {property_index}"
                    ));
                };
                let semantics = if system.assumptions().stutter() {
                    ic3::Ic3TransitionSemantics::stutter_enabled()
                } else {
                    ic3::Ic3TransitionSemantics::stutter_disabled()
                };
                ic3::try_ic3_system_with_semantics(
                    system.ir,
                    system.vctx,
                    system.system_names(),
                    property,
                    system.slots_per_entity(),
                    semantics,
                    timeout_ms,
                )
            }
            TransitionObligation::SystemLiveness {
                liveness,
                recipe_index,
                target_slot,
                timeout_ms,
            } => {
                let system = liveness.system();
                let Some(recipe) = liveness.recipe(recipe_index) else {
                    return TransitionResult::Unknown(format!(
                        "invalid transition liveness recipe index {recipe_index}"
                    ));
                };
                let true_lit = IRExpr::Lit {
                    ty: crate::ir::types::IRType::Bool,
                    value: crate::ir::types::LitVal::Bool { value: true },
                    span: None,
                };
                let trigger = recipe.trigger(&true_lit);
                let response = recipe.response();
                let (ent_var, ent_name) = recipe.quantified_binding();
                let fair_event_keys = system.assumptions().all_fair_event_keys();
                ic3::try_ic3_liveness(ic3::Ic3LivenessInput {
                    ir: system.ir,
                    vctx: system.vctx,
                    system_names: system.system_names(),
                    monitor: ic3::LivenessMonitorInput {
                        trigger,
                        response,
                        entity_var: ent_var,
                        entity_name_for_binding: ent_name,
                        fair_events: &fair_event_keys,
                        is_oneshot: recipe.is_oneshot(),
                        target_slot,
                    },
                    slots_per_entity: system.slots_per_entity(),
                    timeout_ms,
                })
            }
        }
    }
}

/// Solve a transition obligation using the current active transition backend.
pub fn solve_transition_obligation(obligation: TransitionObligation<'_>) -> TransitionResult {
    Ic3TransitionBackend::solve(obligation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRAssumptionSet, IRCommandRef, IRField, IRProgram, IRStoreDecl, IRSystem, IRTransition,
        IRType, IRVariant, IRVerify, IRVerifySystem, LitVal,
    };
    use crate::verify::smt::{self, AbideSolver, SatResult};

    #[test]
    fn transition_obligation_single_entity_preserves_current_ic3_behavior() {
        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![IRField {
                name: "value".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "inc".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity.clone()],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };

        let direct = ic3::try_ic3_single_entity(&entity, &vctx, &property, 5_000);
        let via_transition =
            solve_transition_obligation(TransitionObligation::SingleEntitySafety {
                entity: &entity,
                vctx: &vctx,
                property: &property,
                timeout_ms: 5_000,
            });

        assert!(matches!(direct, TransitionResult::Proved));
        assert!(matches!(via_transition, TransitionResult::Proved));
    }

    #[test]
    fn transition_obligation_single_entity_respects_chc_selection_over_smt_selection() {
        let previous_solver = crate::verify::solver::active_solver_family();
        let previous_chc = crate::verify::chc::active_chc_family();
        crate::verify::solver::set_active_solver_family(crate::verify::solver::SolverFamily::Cvc5)
            .expect("cvc5 SMT backend should be selectable for routing test");
        crate::verify::chc::set_active_chc_family(crate::verify::solver::SolverFamily::Z3)
            .expect("z3 CHC backend should be selectable for routing test");

        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![IRField {
                name: "value".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "inc".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity.clone()],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let property = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };

        let result = solve_transition_obligation(TransitionObligation::SingleEntitySafety {
            entity: &entity,
            vctx: &vctx,
            property: &property,
            timeout_ms: 5_000,
        });

        crate::verify::solver::set_active_solver_family(previous_solver)
            .expect("restoring SMT backend should succeed");
        crate::verify::chc::set_active_chc_family(previous_chc)
            .expect("restoring CHC backend should succeed");

        assert!(
            matches!(result, TransitionResult::Proved),
            "single-entity transition obligations must use the selected CHC backend, got: {result:?}"
        );
    }

    #[test]
    fn transition_assumptions_merge_fair_event_keys_without_duplication() {
        let assumptions = TransitionAssumptions::from_ir(&IRAssumptionSet {
            stutter: false,
            stutter_provenance: IRStutterProvenance::ExplicitNoStutter,
            weak_fair: vec![
                IRCommandRef {
                    system: "Sys".to_owned(),
                    command: "step".to_owned(),
                },
                IRCommandRef {
                    system: "Sys".to_owned(),
                    command: "other".to_owned(),
                },
            ],
            strong_fair: vec![IRCommandRef {
                system: "Sys".to_owned(),
                command: "step".to_owned(),
            }],
            per_tuple: vec![IRCommandRef {
                system: "Sys".to_owned(),
                command: "other".to_owned(),
            }],
        });

        assert!(!assumptions.stutter());
        assert_eq!(
            assumptions.all_fair_event_keys(),
            vec![
                ("Sys".to_owned(), "step".to_owned()),
                ("Sys".to_owned(), "other".to_owned()),
            ]
        );
        assert_eq!(
            assumptions.per_tuple_fair_event_keys(),
            &[("Sys".to_owned(), "other".to_owned())]
        );
        let roundtrip = assumptions.as_ir_assumption_set();
        assert!(!roundtrip.stutter);
        assert_eq!(roundtrip.weak_fair.len(), 2);
        assert_eq!(roundtrip.strong_fair.len(), 1);
        assert_eq!(roundtrip.per_tuple.len(), 1);
    }

    #[test]
    fn transition_encoding_seeds_declared_store_lower_bound_at_initial_state() {
        let account = IREntity {
            name: "Account".to_owned(),
            fields: vec![IRField {
                name: "balance".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let bank = IRSystem {
            name: "Bank".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Account".to_owned()],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            let_bindings: vec![],
            preds: vec![],
            procs: vec![],
        };
        let verify = IRVerify {
            name: "store_initial".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Bank".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![IRStoreDecl {
                name: "accounts".to_owned(),
                entity_type: "Account".to_owned(),
                lo: 1,
                hi: 1,
            }],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![],
            initial_constraints: vec![],
            asserts: vec![IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![account],
            systems: vec![bank],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let obligation = TransitionVerifyObligation::for_verify(&ir, &vctx, &verify, &defs)
            .expect("transition obligation");
        let encoding = TransitionSmtEncoding::from_plan(obligation.bmc_plan()).expect("encoding");
        let solver = AbideSolver::new();
        for constraint in encoding.initial_constraints() {
            solver.assert(constraint);
        }

        assert_eq!(solver.check(), SatResult::Sat);
        let active = encoding
            .pool()
            .active_at("Account", 0, 0)
            .expect("account active flag")
            .as_bool()
            .expect("active flag should be bool");
        solver.assert(smt::bool_not(active));
        assert_eq!(solver.check(), SatResult::Unsat);
        let balance = encoding
            .pool()
            .field_at("Account", 0, "balance", 0)
            .expect("account balance field")
            .as_int()
            .expect("balance should be int");
        solver.assert(smt::bool_not(&smt::int_eq(balance, &smt::int_lit(0))));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn transition_system_spec_for_verify_applies_quantifier_scope_widening() {
        let order_status = crate::ir::types::IRTypeEntry {
            name: "OrderStatus".to_owned(),
            ty: crate::ir::types::IRType::Enum {
                name: "OrderStatus".to_owned(),
                variants: vec![IRVariant::simple("Pending")],
            },
        };
        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "noop".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let system = IRSystem {
            name: "Orders".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let verify = IRVerify {
            name: "quantified".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![],
            initial_constraints: vec![],
            asserts: vec![IRExpr::Always {
                body: Box::new(IRExpr::Forall {
                    var: "o".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![order_status],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let spec =
            TransitionSystemSpec::for_verify(&ir, &vctx, &verify, &defs).expect("expected spec");

        assert_eq!(spec.system_names(), &["Orders".to_owned()]);
        assert_eq!(spec.slots_per_entity().get("Order"), Some(&2));
    }

    #[test]
    fn transition_encoding_asserts_verify_initial_constraints_at_step_zero() {
        let entity = IREntity {
            name: "Counter".to_owned(),
            fields: vec![IRField {
                name: "value".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let system = IRSystem {
            name: "Counters".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Counter".to_owned()],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let initial_constraint = IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "c".to_owned(),
                        ty: IRType::Entity {
                            name: "Counter".to_owned(),
                        },
                        span: None,
                    }),
                    field: "value".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 5 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };
        let verify = IRVerify {
            name: "initial_constraints".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Counters".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![crate::ir::types::IRStoreDecl {
                name: "counters".to_owned(),
                entity_type: "Counter".to_owned(),
                lo: 1,
                hi: 1,
            }],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![crate::ir::types::IRActivation {
                instances: vec!["c0".to_owned()],
                store_name: "counters".to_owned(),
            }],
            initial_constraints: vec![initial_constraint],
            asserts: vec![IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let obligation = TransitionVerifyObligation::for_verify(&ir, &vctx, &verify, &defs)
            .expect("transition obligation");
        let encoding = TransitionSmtEncoding::from_plan(obligation.bmc_plan()).expect("encoding");
        let solver = AbideSolver::new();
        for constraint in encoding.initial_constraints() {
            solver.assert(constraint);
        }
        let value = encoding
            .pool()
            .field_at("Counter", 0, "value", 0)
            .expect("counter value field")
            .as_int()
            .expect("counter value should be int");
        solver.assert(smt::bool_not(&smt::int_eq(value, &smt::int_lit(5))));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn transition_safety_spec_normalizes_always_wrapped_asserts() {
        let verify = IRVerify {
            name: "safety".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![],
            initial_constraints: vec![],
            asserts: vec![IRExpr::Always {
                body: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![IRSystem {
                name: "Orders".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec![],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let safety =
            TransitionSafetySpec::for_verify(&ir, &vctx, &verify, &defs).expect("expected safety");

        assert_eq!(safety.step_properties().len(), 1);
        assert!(matches!(
            safety.step_properties()[0],
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                ..
            }
        ));
    }

    #[test]
    fn transition_verify_obligation_compiles_quantified_liveness_monitor_recipes() {
        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "noop".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let verify = IRVerify {
            name: "liveness".to_owned(),
            depth: Some(1),
            systems: vec![IRVerifySystem {
                name: "Orders".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: vec![],
            initial_constraints: vec![],
            asserts: vec![IRExpr::Always {
                body: Box::new(IRExpr::Forall {
                    var: "o".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(IRExpr::Eventually {
                        body: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }],
            span: None,
            file: None,
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![IRSystem {
                name: "Orders".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec!["Order".to_owned()],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            verifies: vec![verify.clone()],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);

        let obligation = TransitionVerifyObligation::for_verify(&ir, &vctx, &verify, &defs)
            .expect("expected verify obligation");
        let liveness = obligation.liveness().expect("expected supported liveness");
        let recipe = liveness.recipe(0).expect("expected liveness recipe");
        let true_lit = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };

        assert!(recipe.is_quantified());
        assert!(!recipe.is_oneshot());
        assert_eq!(recipe.slot_count(), 2);
        assert_eq!(recipe.assert_index(), 0);
        assert_eq!(recipe.quantified_binding(), (Some("o"), Some("Order")));
        assert!(matches!(
            recipe.trigger(&true_lit),
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                ..
            }
        ));
        assert!(matches!(
            recipe.response(),
            IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                ..
            }
        ));
        assert!(matches!(
            liveness.obligation(0, Some(1), 123),
            TransitionObligation::SystemLiveness {
                recipe_index: 0,
                target_slot: Some(1),
                timeout_ms: 123,
                ..
            }
        ));
    }

    #[test]
    fn transition_execution_plan_distinguishes_bmc_and_lasso_modes() {
        let system_ir = IRSystem {
            name: "Orders".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            actions: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![system_ir.clone()],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let vctx = VerifyContext::from_ir(&ir);
        let system = TransitionSystemSpec::from_selected(
            &ir,
            &vctx,
            TransitionSelectedParts {
                selected_system_names: vec!["Orders".to_owned()],
                relevant_entities: vec![],
                relevant_systems: vec![system_ir],
                slots_per_entity: HashMap::new(),
                bound: 3,
                store_ranges: HashMap::new(),
                activations: vec![],
                initial_constraints: vec![],
            },
            &IRAssumptionSet::default_for_verify(),
        )
        .expect("expected selected system");

        let bmc = TransitionExecutionPlan::for_bmc(system.clone(), 3);
        let lasso = TransitionExecutionPlan::for_lasso(system.clone(), 3);
        let inductive = TransitionExecutionPlan::for_inductive_step(system);

        assert_eq!(bmc.steps(), 3);
        assert!(bmc.include_system_initial_constraints());
        assert!(bmc.include_symmetry_constraints());
        assert!(!bmc.include_lasso_and_fairness());

        assert_eq!(lasso.steps(), 3);
        assert!(lasso.include_system_initial_constraints());
        assert!(lasso.include_symmetry_constraints());
        assert!(lasso.include_lasso_and_fairness());

        assert_eq!(inductive.steps(), 1);
        assert!(!inductive.include_system_initial_constraints());
        assert!(!inductive.include_symmetry_constraints());
        assert!(!inductive.include_lasso_and_fairness());
    }
}
