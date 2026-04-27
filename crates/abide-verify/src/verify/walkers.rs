//! Expression analysis predicates and counterexample extraction.

use abide_witness::{op, rel};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

use crate::ir::types::{IRAction, IREntity, IRExpr, IRSystem, IRType};

use super::context::VerifyContext;
use super::harness::{self, FireTracking, SlotPool};
use super::smt::{self, AbideSolver, Dynamic, Model, SmtValue};
use super::{DeadlockEventDiag, FairnessEventAnalysis, FairnessKind, FairnessStatus, TraceStep};

// ── Expression analysis predicates ──────────────────────────────────

fn is_extern_boundary_system(system: &IRSystem) -> bool {
    system
        .preds
        .iter()
        .any(|pred| pred.name == "__abide_extern__marker")
}

fn render_observation_witness_value(value: &op::WitnessValue) -> String {
    match value {
        op::WitnessValue::Unknown => "?".to_owned(),
        op::WitnessValue::Int(v) => v.to_string(),
        op::WitnessValue::Bool(v) => v.to_string(),
        op::WitnessValue::Real(v)
        | op::WitnessValue::Float(v)
        | op::WitnessValue::String(v)
        | op::WitnessValue::Identity(v) => v.clone(),
        op::WitnessValue::EnumVariant { enum_name, variant } => format!("@{enum_name}::{variant}"),
        op::WitnessValue::SlotRef(slot) => format!("{}[{}]", slot.entity(), slot.slot()),
        op::WitnessValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(render_observation_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!("{name}: {}", render_observation_witness_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Set(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(render_observation_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Seq(values) => format!(
            "[{}]",
            values
                .iter()
                .map(render_observation_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, value)| {
                    format!(
                        "{} -> {}",
                        render_observation_witness_value(key),
                        render_observation_witness_value(value)
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Opaque { display, .. } => display.clone(),
    }
}

/// Check if an expression contains imperative constructs (While, `VarDecl`, mutable assignment).
pub(super) fn contains_imperative(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::While { .. }
        | IRExpr::VarDecl { .. }
        | IRExpr::Assert { .. }
        | IRExpr::Assume { .. } => true,
        // Assignment: BinOp(OpEq, Var(_), _) is an imperative mutation
        IRExpr::BinOp { op, left, .. }
            if op == "OpEq" && matches!(left.as_ref(), IRExpr::Var { .. }) =>
        {
            true
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(contains_imperative),
        IRExpr::IfElse {
            then_body,
            else_body,
            ..
        } => {
            contains_imperative(then_body)
                || else_body.as_ref().is_some_and(|e| contains_imperative(e))
        }
        _ => false,
    }
}

/// Check if a function body contains any `assert` or `assume` statements.
/// Used to determine if a function without `ensures` should still be verified.
///
/// Walks the entire expression tree — assert/assume may appear nested inside
/// any expression form (e.g., `x + (assert false)`), not just at statement level.
pub(super) fn body_contains_assert(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Assert { .. } | IRExpr::Assume { .. } => true,
        IRExpr::Block { exprs, .. } => exprs.iter().any(body_contains_assert),
        IRExpr::Lam { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. } => body_contains_assert(body),
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|pred| body_contains_assert(pred)),
        IRExpr::VarDecl { init, rest, .. } => {
            body_contains_assert(init) || body_contains_assert(rest)
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            body_contains_assert(cond)
                || invariants.iter().any(body_contains_assert)
                || body_contains_assert(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            body_contains_assert(cond)
                || body_contains_assert(then_body)
                || else_body.as_ref().is_some_and(|e| body_contains_assert(e))
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            body_contains_assert(left) || body_contains_assert(right)
        }
        IRExpr::UnOp { operand, .. } => body_contains_assert(operand),
        IRExpr::App { func, arg, .. } => body_contains_assert(func) || body_contains_assert(arg),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| body_contains_assert(&b.expr)) || body_contains_assert(body)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => body_contains_assert(body),
        IRExpr::Field { expr, .. } | IRExpr::Prime { expr, .. } | IRExpr::Card { expr, .. } => {
            body_contains_assert(expr)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            body_contains_assert(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(body_contains_assert)
                        || body_contains_assert(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => body_contains_assert(map) || body_contains_assert(key) || body_contains_assert(value),
        IRExpr::Index { map, key, .. } => body_contains_assert(map) || body_contains_assert(key),
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            body_contains_assert(filter)
                || projection.as_ref().is_some_and(|p| body_contains_assert(p))
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(body_contains_assert)
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| body_contains_assert(k) || body_contains_assert(v)),
        // saw args may contain assert.
        IRExpr::Saw { args, .. } => args
            .iter()
            .any(|a| a.as_ref().is_some_and(|e| body_contains_assert(e))),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            body_contains_assert(body)
                || in_filter.as_ref().is_some_and(|f| body_contains_assert(f))
        }
        IRExpr::Lit { .. }
        | IRExpr::Var { .. }
        | IRExpr::Ctor { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => false,
    }
}

/// Check if a function body contains any `assume` statement (specifically).
/// Used to determine if a verified function should be reported as ADMITTED.
pub(super) fn body_contains_assume(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Assume { .. } => true,
        IRExpr::Assert { expr, .. } => body_contains_assume(expr),
        IRExpr::Block { exprs, .. } => exprs.iter().any(body_contains_assume),
        IRExpr::Lam { body, .. } => body_contains_assume(body),
        IRExpr::VarDecl { init, rest, .. } => {
            body_contains_assume(init) || body_contains_assume(rest)
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            body_contains_assume(cond)
                || invariants.iter().any(body_contains_assume)
                || body_contains_assume(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            body_contains_assume(cond)
                || body_contains_assume(then_body)
                || else_body.as_ref().is_some_and(|e| body_contains_assume(e))
        }
        IRExpr::BinOp { left, right, .. } => {
            body_contains_assume(left) || body_contains_assume(right)
        }
        IRExpr::UnOp { operand, .. } => body_contains_assume(operand),
        IRExpr::App { func, arg, .. } => body_contains_assume(func) || body_contains_assume(arg),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| body_contains_assume(&b.expr)) || body_contains_assume(body)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            body_contains_assume(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(body_contains_assume)
                        || body_contains_assume(&a.body)
                })
        }
        _ => false,
    }
}

/// Check if a function body contains `sorry`.
/// Used to short-circuit verification — sorry admits the entire proof obligation.
///
/// Walks the entire expression tree so nested forms like `x + sorry` are detected.
pub(super) fn body_contains_sorry(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Sorry { .. } => true,
        IRExpr::Block { exprs, .. } => exprs.iter().any(body_contains_sorry),
        IRExpr::Lam { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. } => body_contains_sorry(body),
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|pred| body_contains_sorry(pred)),
        IRExpr::VarDecl { init, rest, .. } => {
            body_contains_sorry(init) || body_contains_sorry(rest)
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            body_contains_sorry(cond)
                || invariants.iter().any(body_contains_sorry)
                || body_contains_sorry(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            body_contains_sorry(cond)
                || body_contains_sorry(then_body)
                || else_body.as_ref().is_some_and(|e| body_contains_sorry(e))
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            body_contains_sorry(left) || body_contains_sorry(right)
        }
        IRExpr::UnOp { operand, .. } => body_contains_sorry(operand),
        IRExpr::App { func, arg, .. } => body_contains_sorry(func) || body_contains_sorry(arg),
        IRExpr::Let { bindings, body, .. } => {
            bindings.iter().any(|b| body_contains_sorry(&b.expr)) || body_contains_sorry(body)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => body_contains_sorry(body),
        IRExpr::Field { expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::Card { expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. } => body_contains_sorry(expr),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            body_contains_sorry(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(body_contains_sorry)
                        || body_contains_sorry(&a.body)
                })
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => body_contains_sorry(map) || body_contains_sorry(key) || body_contains_sorry(value),
        IRExpr::Index { map, key, .. } => body_contains_sorry(map) || body_contains_sorry(key),
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            body_contains_sorry(filter)
                || projection.as_ref().is_some_and(|p| body_contains_sorry(p))
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().any(body_contains_sorry)
        }
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| body_contains_sorry(k) || body_contains_sorry(v)),
        // saw args may contain sorry.
        IRExpr::Saw { args, .. } => args
            .iter()
            .any(|a| a.as_ref().is_some_and(|e| body_contains_sorry(e))),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            body_contains_sorry(body) || in_filter.as_ref().is_some_and(|f| body_contains_sorry(f))
        }
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Ctor { .. } | IRExpr::Todo { .. } => {
            false
        }
    }
}

// ── Model extraction helpers ────────────────────────────────────────

pub(super) fn dynamic_to_smt_value(d: Dynamic) -> SmtValue {
    if let Some(i) = d.as_int() {
        SmtValue::Int(i)
    } else if let Some(b) = d.as_bool() {
        SmtValue::Bool(b)
    } else if let Some(r) = d.as_real() {
        SmtValue::Real(r)
    } else if let Some(a) = crate::verify::smt::dynamic_as_array(&d) {
        SmtValue::Array(a)
    } else {
        SmtValue::Dynamic(d)
    }
}

/// Extract a human-readable value from a Z3 model for counterexample display.
pub(super) fn extract_model_value(
    model: &Model,
    val: &SmtValue,
    variants: &super::context::VariantMap,
    ty: &crate::ir::types::IRType,
) -> String {
    match val {
        SmtValue::Int(i) => {
            if let Some(model_val) = model.eval(i, true) {
                let s = model_val.to_string();
                // Check if this is an enum — try to decode the int to a variant name
                if let crate::ir::types::IRType::Enum { .. } = ty {
                    if let Ok(id) = s.parse::<i64>() {
                        if let Some((type_name, variant_name)) = variants.name_of(id) {
                            return format!("@{type_name}::{variant_name}");
                        }
                    }
                }
                s
            } else {
                "?".to_owned()
            }
        }
        SmtValue::Bool(b) => model
            .eval(b, true)
            .map_or("?".to_owned(), |v| v.to_string()),
        SmtValue::Real(r) => model
            .eval(r, true)
            .map_or("?".to_owned(), |v| v.to_string()),
        _ => "?".to_owned(),
    }
}

/// Elapsed time in milliseconds, saturating to `u64::MAX`.
#[allow(clippy::cast_possible_truncation)]
pub(super) fn elapsed_ms(start: &Instant) -> u64 {
    start.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

// ── Definition reference collection ─────────────────────────────────

pub(super) fn collect_def_refs_in_exprs(exprs: &[IRExpr], refs: &mut HashSet<String>) {
    let bound = HashSet::new();
    for expr in exprs {
        collect_def_refs_inner(expr, &bound, refs);
    }
}

pub(super) fn collect_def_refs_inner(
    expr: &IRExpr,
    bound: &HashSet<String>,
    refs: &mut HashSet<String>,
) {
    match expr {
        IRExpr::Var { name, .. } => {
            if !bound.contains(name) {
                refs.insert(name.clone());
            }
        }
        IRExpr::App { func, arg, .. } => {
            if let IRExpr::Var { name, .. } = func.as_ref() {
                if !bound.contains(name) {
                    refs.insert(name.clone());
                }
            }
            collect_def_refs_inner(func, bound, refs);
            collect_def_refs_inner(arg, bound, refs);
        }
        IRExpr::Forall { var, body, .. }
        | IRExpr::Exists { var, body, .. }
        | IRExpr::One { var, body, .. }
        | IRExpr::Lone { var, body, .. } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_def_refs_inner(body, &inner_bound, refs);
        }
        IRExpr::Lam { param, body, .. } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(param.clone());
            collect_def_refs_inner(body, &inner_bound, refs);
        }
        IRExpr::SetComp {
            var,
            filter,
            projection,
            ..
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_def_refs_inner(filter, &inner_bound, refs);
            if let Some(proj) = projection {
                collect_def_refs_inner(proj, &inner_bound, refs);
            }
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            collect_def_refs_inner(left, bound, refs);
            collect_def_refs_inner(right, bound, refs);
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            collect_def_refs_inner(map, bound, refs);
            collect_def_refs_inner(key, bound, refs);
            collect_def_refs_inner(value, bound, refs);
        }
        IRExpr::Index { map, key, .. } => {
            collect_def_refs_inner(map, bound, refs);
            collect_def_refs_inner(key, bound, refs);
        }
        IRExpr::MapLit { entries, .. } => {
            for (k, v) in entries {
                collect_def_refs_inner(k, bound, refs);
                collect_def_refs_inner(v, bound, refs);
            }
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            for e in elements {
                collect_def_refs_inner(e, bound, refs);
            }
        }
        IRExpr::UnOp { operand, .. }
        | IRExpr::Field { expr: operand, .. }
        | IRExpr::Prime { expr: operand, .. }
        | IRExpr::Always { body: operand, .. }
        | IRExpr::Eventually { body: operand, .. }
        | IRExpr::Historically { body: operand, .. }
        | IRExpr::Once { body: operand, .. }
        | IRExpr::Previously { body: operand, .. }
        | IRExpr::Card { expr: operand, .. } => {
            collect_def_refs_inner(operand, bound, refs);
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut inner_bound = bound.clone();
            for b in bindings {
                // Binding RHS is evaluated in the outer scope
                collect_def_refs_inner(&b.expr, &inner_bound, refs);
                inner_bound.insert(b.name.clone());
            }
            collect_def_refs_inner(body, &inner_bound, refs);
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_def_refs_inner(scrutinee, bound, refs);
            for arm in arms {
                let mut arm_bound = bound.clone();
                super::collect_pattern_binders(&arm.pattern, &mut arm_bound);
                if let Some(ref guard) = arm.guard {
                    collect_def_refs_inner(guard, &arm_bound, refs);
                }
                collect_def_refs_inner(&arm.body, &arm_bound, refs);
            }
        }
        _ => {}
    }
}

// ── IC3 trace conversion ────────────────────────────────────────────

fn parse_ic3_entity_slot(entity_label: &str) -> op::EntitySlotRef {
    if let Some((entity, slot_suffix)) = entity_label.split_once('[') {
        if let Some(slot_str) = slot_suffix.strip_suffix(']') {
            if let Ok(slot) = slot_str.parse::<usize>() {
                return op::EntitySlotRef::new(entity, slot);
            }
        }
    }
    op::EntitySlotRef::new(entity_label, 0)
}

fn decode_ic3_value(
    raw: &str,
    ty: &IRType,
    variants: &super::context::VariantMap,
) -> op::WitnessValue {
    match ty {
        IRType::Bool => match raw {
            "true" => op::WitnessValue::Bool(true),
            "false" => op::WitnessValue::Bool(false),
            _ => op::WitnessValue::Opaque {
                display: raw.to_owned(),
                ty: Some("Bool".to_owned()),
            },
        },
        IRType::Int | IRType::Refinement { .. } => raw
            .parse::<i64>()
            .map(op::WitnessValue::Int)
            .unwrap_or_else(|_| op::WitnessValue::Opaque {
                display: raw.to_owned(),
                ty: Some(render_ir_type(ty)),
            }),
        IRType::Identity => op::WitnessValue::Identity(raw.to_owned()),
        IRType::Real => op::WitnessValue::Real(raw.to_owned()),
        IRType::Float => op::WitnessValue::Float(raw.to_owned()),
        IRType::Enum { name, .. } => raw
            .parse::<i64>()
            .ok()
            .and_then(|id| variants.name_of(id))
            .filter(|(enum_name, _)| enum_name == name)
            .map(|(enum_name, variant)| op::WitnessValue::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            })
            .unwrap_or_else(|| op::WitnessValue::Opaque {
                display: raw.to_owned(),
                ty: Some(name.clone()),
            }),
        _ => op::WitnessValue::Opaque {
            display: raw.to_owned(),
            ty: Some(render_ir_type(ty)),
        },
    }
}

fn ic3_trace_step_to_state(
    step: &super::ic3::Ic3TraceStep,
    entities: &[crate::ir::types::IREntity],
    variants: &super::context::VariantMap,
) -> Result<op::State, String> {
    let entity_field_types: HashMap<(String, String), IRType> = entities
        .iter()
        .flat_map(|entity| {
            entity
                .fields
                .iter()
                .map(move |field| ((entity.name.clone(), field.name.clone()), field.ty.clone()))
        })
        .collect();

    let mut slots: HashMap<op::EntitySlotRef, op::EntityStateBuilder> = HashMap::new();
    for (entity_label, field_name, raw_value) in &step.assignments {
        let slot = parse_ic3_entity_slot(entity_label);
        let ty = entity_field_types
            .get(&(slot.entity().to_owned(), field_name.clone()))
            .ok_or_else(|| {
                format!(
                    "IC3 trace references unknown field type for {}.{}",
                    slot.entity(),
                    field_name
                )
            })?;
        let value = decode_ic3_value(raw_value, ty, variants);
        let builder = slots
            .entry(slot)
            .or_insert_with(|| op::EntityState::builder(true));
        *builder = std::mem::replace(builder, op::EntityState::builder(true))
            .field(field_name.clone(), value);
    }

    let mut state = op::State::builder();
    let mut slot_entries: Vec<_> = slots.into_iter().collect();
    slot_entries.sort_by(|left, right| left.0.cmp(&right.0));
    for (slot, builder) in slot_entries {
        state = state.entity_slot(slot, builder.build());
    }
    Ok(state.build())
}

fn parse_ic3_event_label(
    label: &str,
    systems: &[crate::ir::types::IRSystem],
) -> Option<(String, String)> {
    if label.contains(" or ") {
        return None;
    }
    if let Some((system, command)) = label.split_once("::") {
        return Some((system.to_owned(), command.to_owned()));
    }
    if systems.len() == 1 {
        return Some((systems[0].name.clone(), label.to_owned()));
    }
    None
}

pub(super) fn ic3_trace_to_operational_witness(
    ic3_trace: &[super::ic3::Ic3TraceStep],
    entities: &[crate::ir::types::IREntity],
    systems: &[crate::ir::types::IRSystem],
    variants: &super::context::VariantMap,
) -> Result<op::OperationalWitness, String> {
    if ic3_trace.is_empty() {
        return Err("IC3 trace is empty".to_owned());
    }

    let states: Vec<op::State> = ic3_trace
        .iter()
        .map(|step| ic3_trace_step_to_state(step, entities, variants))
        .collect::<Result<_, _>>()?;

    let mut transitions = Vec::new();
    for index in 0..states.len().saturating_sub(1) {
        let mut builder = op::Transition::builder();
        if let Some(label) = identify_event_from_field_changes(
            &ic3_trace[index].assignments,
            &ic3_trace[index + 1].assignments,
            entities,
            systems,
        ) {
            if let Some((system, command)) = parse_ic3_event_label(&label, systems) {
                let step_id = op::AtomicStepId::new(format!("ic3-step-{index}"))
                    .map_err(|err| format!("IC3 step id construction failed: {err}"))?;
                let atomic_step = op::AtomicStep::builder(step_id, system, command)
                    .step_name(format!("ic3#{index}"))
                    .build()
                    .map_err(|err| format!("IC3 atomic step construction failed: {err}"))?;
                builder = builder.atomic_step(atomic_step);
            } else {
                let observation = op::TransitionObservation::new(
                    "backend_event_label",
                    op::WitnessValue::String(label),
                )
                .map_err(|err| format!("IC3 backend observation construction failed: {err}"))?;
                builder = builder.observation(observation);
            }
        }
        transitions.push(
            builder
                .build()
                .map_err(|err| format!("IC3 transition construction failed: {err}"))?,
        );
    }

    let mut behavior = op::Behavior::builder();
    for (index, state) in states.into_iter().enumerate() {
        behavior = behavior.state(state);
        if let Some(transition) = transitions.get(index).cloned() {
            behavior = behavior.transition(transition);
        }
    }

    let behavior = behavior
        .build()
        .map_err(|err| format!("IC3 behavior construction failed: {err}"))?;
    op::OperationalWitness::counterexample(behavior)
        .map_err(|err| format!("IC3 operational witness validation failed: {err}"))
}

/// Best-effort event identification for IC3 traces by comparing field changes
/// between consecutive steps against event action update signatures.
///
/// Matches based on which specific fields changed (not just entity name).
/// Collects all matching events — if ambiguous, reports "event A or event B".
pub(super) fn identify_event_from_field_changes(
    before: &[(String, String, String)],
    after: &[(String, String, String)],
    entities: &[crate::ir::types::IREntity],
    systems: &[crate::ir::types::IRSystem],
) -> Option<String> {
    // Find which (entity, field) pairs changed
    let mut changed_fields: HashSet<(String, String)> = HashSet::new();
    for (entity_a, field_a, val_a) in after {
        let base_entity = entity_a.split('[').next().unwrap_or(entity_a).to_owned();
        let prev = before
            .iter()
            .find(|(e, f, _)| e == entity_a && f == field_a);
        match prev {
            Some((_, _, val_b)) if val_a != val_b => {
                changed_fields.insert((base_entity, field_a.clone()));
            }
            None => {
                changed_fields.insert((base_entity, field_a.clone()));
            }
            _ => {}
        }
    }

    if changed_fields.is_empty() {
        return None; // stutter
    }

    // Check if new entities appeared
    let new_entities: HashSet<String> = after
        .iter()
        .filter(|(e, _, _)| !before.iter().any(|(eb, _, _)| eb == e))
        .map(|(e, _, _)| e.split('[').next().unwrap_or(e).to_owned())
        .collect();

    // Collect fields that each event's actions modify
    let mut matches = Vec::new();
    for system in systems {
        for event in &system.steps {
            let modified = collect_event_modified_fields(&event.body, entities);
            let creates = collect_event_created_entities(&event.body);

            // Match: event modifies exactly the fields that changed,
            // or creates the entities that appeared
            let fields_match = !modified.is_empty()
                && modified
                    .iter()
                    .all(|(e, f)| changed_fields.contains(&(e.clone(), f.clone())));
            let creates_match =
                !creates.is_empty() && creates.iter().any(|e| new_entities.contains(e));

            if fields_match || creates_match {
                let name = if systems.len() == 1 {
                    event.name.clone()
                } else {
                    format!("{}::{}", system.name, event.name)
                };
                matches.push(name);
            }
        }
    }

    match matches.len() {
        0 => None,
        1 => Some(matches.into_iter().next().unwrap()),
        _ => Some(matches.join(" or ")),
    }
}

/// Collect (entity, field) pairs modified by an event's actions.
///
/// Resolves transition/action names to the actual fields they update
/// by looking up entity IR transitions.
pub(super) fn collect_event_modified_fields(
    actions: &[crate::ir::types::IRAction],
    entities: &[crate::ir::types::IREntity],
) -> HashSet<(String, String)> {
    use crate::ir::types::IRAction;
    let mut fields = HashSet::new();
    for action in actions {
        match action {
            IRAction::Choose { entity, ops, .. } | IRAction::ForAll { entity, ops, .. } => {
                for op in ops {
                    if let IRAction::Apply { transition, .. } = op {
                        // Resolve transition name to actual updated fields
                        if let Some(ent_ir) = entities.iter().find(|e| &e.name == entity) {
                            if let Some(trans) =
                                ent_ir.transitions.iter().find(|t| &t.name == transition)
                            {
                                for upd in &trans.updates {
                                    fields.insert((entity.clone(), upd.field.clone()));
                                }
                            }
                        }
                    }
                }
                let nested = collect_event_modified_fields(ops, entities);
                fields.extend(nested);
            }
            _ => {}
        }
    }
    fields
}

/// Collect entity names created by an event's actions.
pub(super) fn collect_event_created_entities(
    actions: &[crate::ir::types::IRAction],
) -> Vec<String> {
    use crate::ir::types::IRAction;
    let mut entities = Vec::new();
    for action in actions {
        match action {
            IRAction::Create { entity, .. } => entities.push(entity.clone()),
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                entities.extend(collect_event_created_entities(ops));
            }
            _ => {}
        }
    }
    entities
}

// ── Entity quantifier analysis ──────────────────────────────────────

/// Detect if show expressions have quantifier nesting depth > 1 for any entity type.
/// E.g., `all a: Account | all b: Account | P(a, b)` has depth 2 for Account.
/// Used to annotate PROVED output with scope info for inter-entity properties.
pub(super) fn has_multi_entity_quantifier(show_exprs: &[&IRExpr]) -> bool {
    for expr in show_exprs {
        let mut entity_vars: HashMap<String, usize> = HashMap::new();
        count_entity_quantifiers(expr, &mut entity_vars);
        if entity_vars.values().any(|&count| count > 1) {
            return true;
        }
    }
    false
}

pub(super) fn count_entity_quantifiers(expr: &IRExpr, counts: &mut HashMap<String, usize>) {
    match expr {
        IRExpr::Forall {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        }
        | IRExpr::Exists {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        }
        | IRExpr::One {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        }
        | IRExpr::Lone {
            domain: crate::ir::types::IRType::Entity { name },
            body,
            ..
        } => {
            *counts.entry(name.clone()).or_insert(0) += 1;
            count_entity_quantifiers(body, counts);
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::App {
            func: left,
            arg: right,
            ..
        } => {
            count_entity_quantifiers(left, counts);
            count_entity_quantifiers(right, counts);
        }
        IRExpr::UnOp { operand, .. }
        | IRExpr::Field { expr: operand, .. }
        | IRExpr::Prime { expr: operand, .. }
        | IRExpr::Card { expr: operand, .. }
        | IRExpr::Always { body: operand, .. }
        | IRExpr::Eventually { body: operand, .. } => {
            count_entity_quantifiers(operand, counts);
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => {
            count_entity_quantifiers(body, counts);
        }
        // SetComp introduces an entity binder — count it like Forall
        IRExpr::SetComp {
            domain: crate::ir::types::IRType::Entity { name },
            filter,
            projection,
            ..
        } => {
            *counts.entry(name.clone()).or_insert(0) += 1;
            count_entity_quantifiers(filter, counts);
            if let Some(proj) = projection {
                count_entity_quantifiers(proj, counts);
            }
        }
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            count_entity_quantifiers(filter, counts);
            if let Some(proj) = projection {
                count_entity_quantifiers(proj, counts);
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            count_entity_quantifiers(map, counts);
            count_entity_quantifiers(key, counts);
            count_entity_quantifiers(value, counts);
        }
        IRExpr::Index { map, key, .. } => {
            count_entity_quantifiers(map, counts);
            count_entity_quantifiers(key, counts);
        }
        _ => {}
    }
}

// ── Event body analysis ─────────────────────────────────────────────

/// Scan an event body (and `CrossCall` targets) for Create actions.
/// Returns the entity types created, in order of first appearance.
pub(super) fn scan_event_creates(
    actions: &[IRAction],
    all_systems: &[crate::ir::types::IRSystem],
) -> Vec<String> {
    let mut creates = Vec::new();
    scan_event_creates_inner(actions, all_systems, &mut creates, 0);
    creates
}

fn scan_event_creates_inner(
    actions: &[IRAction],
    all_systems: &[crate::ir::types::IRSystem],
    creates: &mut Vec<String>,
    depth: usize,
) {
    if depth > 10 {
        return; // prevent infinite recursion on cyclic CrossCalls
    }
    for action in actions {
        match action {
            IRAction::Create { entity, .. } => {
                if !creates.contains(entity) {
                    creates.push(entity.clone());
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                scan_event_creates_inner(ops, all_systems, creates, depth);
            }
            IRAction::CrossCall {
                system, command, ..
            } => {
                if let Some(sys) = all_systems.iter().find(|s| s.name == *system) {
                    for step in sys.steps.iter().filter(|s| s.name == *command) {
                        scan_event_creates_inner(&step.body, all_systems, creates, depth + 1);
                    }
                }
            }
            _ => {}
        }
    }
}

pub(super) fn collect_event_body_entities(
    actions: &[IRAction],
    systems: &[IRSystem],
    entities: &mut HashSet<String>,
    visited: &mut HashSet<(String, String)>,
) {
    for action in actions {
        match action {
            IRAction::Choose { entity, ops, .. } | IRAction::ForAll { entity, ops, .. } => {
                entities.insert(entity.clone());
                collect_event_body_entities(ops, systems, entities, visited);
            }
            IRAction::Create { entity, .. } => {
                entities.insert(entity.clone());
            }
            IRAction::Apply { target, .. } => {
                entities.insert(target.clone());
            }
            IRAction::CrossCall {
                system, command, ..
            } => {
                let key = (system.clone(), command.clone());
                if visited.insert(key) {
                    if let Some(sys) = systems.iter().find(|s| s.name == *system) {
                        for step in sys.steps.iter().filter(|s| s.name == *command) {
                            collect_event_body_entities(&step.body, systems, entities, visited);
                        }
                    }
                }
            }
            IRAction::LetCrossCall {
                system, command, ..
            } => {
                let key = (system.clone(), command.clone());
                if visited.insert(key) {
                    if let Some(sys) = systems.iter().find(|s| s.name == *system) {
                        for step in sys.steps.iter().filter(|s| s.name == *command) {
                            collect_event_body_entities(&step.body, systems, entities, visited);
                        }
                    }
                }
            }
            IRAction::Match { arms, .. } => {
                for arm in arms {
                    collect_event_body_entities(&arm.body, systems, entities, visited);
                }
            }
            IRAction::ExprStmt { .. } => {}
        }
    }
}

// ── Field reference collection ──────────────────────────────────────

pub(super) fn collect_field_refs_in_expr(
    expr: &IRExpr,
    var_name: &str,
    fields: &mut HashSet<String>,
) {
    match expr {
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                if name == var_name {
                    fields.insert(field.clone());
                }
            }
            collect_field_refs_in_expr(inner, var_name, fields);
        }
        IRExpr::BinOp { left, right, .. } | IRExpr::Until { left, right, .. } => {
            collect_field_refs_in_expr(left, var_name, fields);
            collect_field_refs_in_expr(right, var_name, fields);
        }
        IRExpr::UnOp { operand, .. } => collect_field_refs_in_expr(operand, var_name, fields),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => {
            collect_field_refs_in_expr(body, var_name, fields);
        }
        _ => {}
    }
}

// ── Scene expression validation ─────────────────────────────────────

/// Return the first expression kind that scene checking cannot encode safely.
///
/// Scene checks currently rely on `encode_prop_expr` / `encode_prop_value` for
/// given constraints, event arguments, and then assertions. Some expression
/// forms still panic there; reject those forms up front with `SceneFail`.
pub(super) fn find_unsupported_scene_expr(expr: &IRExpr) -> Option<&'static str> {
    match expr {
        IRExpr::Lam { .. } => Some("Lam"),
        IRExpr::Let { bindings, body, .. } => bindings
            .iter()
            .find_map(|binding| find_unsupported_scene_expr(&binding.expr))
            .or_else(|| find_unsupported_scene_expr(body)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => find_unsupported_scene_expr(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(find_unsupported_scene_expr)
                    .or_else(|| find_unsupported_scene_expr(&arm.body))
            })
        }),
        IRExpr::SetComp {
            domain: IRType::Entity { .. },
            filter,
            projection,
            ..
        } => {
            // Entity-domain comprehension is supported; check sub-expressions
            find_unsupported_scene_expr(filter).or_else(|| {
                projection
                    .as_ref()
                    .and_then(|p| find_unsupported_scene_expr(p))
            })
        }
        IRExpr::SetComp { .. } => Some("SetComp with non-entity domain"),
        IRExpr::Sorry { .. } => Some("Sorry"),
        IRExpr::Todo { .. } => Some("Todo"),
        IRExpr::Card { expr, .. } => match expr.as_ref() {
            // Compile-time literal cardinality — always supported
            IRExpr::SetLit { .. } | IRExpr::SeqLit { .. } | IRExpr::MapLit { .. } => None,
            // Entity-domain set comprehension — bounded sum over slots
            IRExpr::SetComp {
                domain: IRType::Entity { .. },
                filter,
                projection,
                ..
            } => find_unsupported_scene_expr(filter).or_else(|| {
                projection
                    .as_ref()
                    .and_then(|p| find_unsupported_scene_expr(p))
            }),
            // Anything else: unsupported (infinite domain, field expression, etc.)
            _ => Some("cardinality (#) of non-literal, non-comprehension expression"),
        },
        IRExpr::Field { expr, .. }
        | IRExpr::UnOp { operand: expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::Always { body: expr, .. }
        | IRExpr::Eventually { body: expr, .. }
        | IRExpr::Historically { body: expr, .. }
        | IRExpr::Once { body: expr, .. }
        | IRExpr::Previously { body: expr, .. } => find_unsupported_scene_expr(expr),
        // saw is a past-time operator; recurse into args.
        IRExpr::Saw { args, .. } => args
            .iter()
            .filter_map(|a| a.as_ref())
            .find_map(|e| find_unsupported_scene_expr(e)),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            find_unsupported_scene_expr(left).or_else(|| find_unsupported_scene_expr(right))
        }
        IRExpr::App { func, arg, .. } => {
            // After def expansion, remaining App(Var(name),...) means an
            // unresolvable function call that can't be encoded in Z3.
            if matches!(func.as_ref(), IRExpr::Var { .. }) {
                return Some(crate::messages::PRECHECK_UNRESOLVED_FN);
            }
            find_unsupported_scene_expr(func).or_else(|| find_unsupported_scene_expr(arg))
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => find_unsupported_scene_expr(body),
        IRExpr::Choose { predicate, .. } => {
            predicate.as_deref().and_then(find_unsupported_scene_expr)
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => find_unsupported_scene_expr(map)
            .or_else(|| find_unsupported_scene_expr(key))
            .or_else(|| find_unsupported_scene_expr(value)),
        IRExpr::Index { map, key, .. } => {
            find_unsupported_scene_expr(map).or_else(|| find_unsupported_scene_expr(key))
        }
        IRExpr::MapLit { entries, .. } => entries.iter().find_map(|(k, v)| {
            find_unsupported_scene_expr(k).or_else(|| find_unsupported_scene_expr(v))
        }),
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            elements.iter().find_map(find_unsupported_scene_expr)
        }
        IRExpr::Lit { .. } | IRExpr::Var { .. } | IRExpr::Ctor { .. } => None,
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            let r = find_unsupported_scene_expr(body);
            if r.is_some() {
                return r;
            }
            if let Some(f) = in_filter {
                return find_unsupported_scene_expr(f);
            }
            None
        }
        IRExpr::Block { .. } => Some("Block"),
        IRExpr::VarDecl { .. } => Some("VarDecl"),
        IRExpr::While { .. } => Some("While"),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            find_unsupported_scene_expr(expr)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => find_unsupported_scene_expr(cond)
            .or_else(|| find_unsupported_scene_expr(then_body))
            .or_else(|| {
                else_body
                    .as_ref()
                    .and_then(|e| find_unsupported_scene_expr(e))
            }),
    }
}

// ── Counterexample extraction ───────────────────────────────────────

fn render_ir_type(ty: &IRType) -> String {
    match ty {
        IRType::Int => "Int".to_owned(),
        IRType::Bool => "Bool".to_owned(),
        IRType::String => "String".to_owned(),
        IRType::Identity => "Identity".to_owned(),
        IRType::Real => "Real".to_owned(),
        IRType::Float => "Float".to_owned(),
        IRType::Enum { name, .. } => name.clone(),
        IRType::Record { name, .. } => name.clone(),
        IRType::Fn { .. } => "Fn".to_owned(),
        IRType::Entity { name } => format!("Entity<{name}>"),
        IRType::Set { element } => format!("Set<{}>", render_ir_type(element)),
        IRType::Seq { element } => format!("Seq<{}>", render_ir_type(element)),
        IRType::Map { key, value } => {
            format!("Map<{}, {}>", render_ir_type(key), render_ir_type(value))
        }
        IRType::Tuple { elements } => format!(
            "({})",
            elements
                .iter()
                .map(render_ir_type)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        IRType::Refinement { base, .. } => render_ir_type(base),
    }
}

fn extract_witness_value(
    model: &Model,
    val: &SmtValue,
    variants: &super::context::VariantMap,
    ty: &IRType,
) -> Result<op::WitnessValue, String> {
    match ty {
        IRType::Bool => match val {
            SmtValue::Bool(b) => model
                .eval(b, true)
                .and_then(|v| v.as_bool())
                .map(op::WitnessValue::Bool)
                .ok_or_else(|| "failed to evaluate Bool witness value".to_owned()),
            _ => Err("expected Bool SMT value for Bool witness extraction".to_owned()),
        },
        IRType::Int | IRType::Refinement { .. } => match val {
            SmtValue::Int(i) => model
                .eval(i, true)
                .and_then(|v| v.as_i64())
                .map(op::WitnessValue::Int)
                .ok_or_else(|| "failed to evaluate Int witness value".to_owned()),
            _ => Err("expected Int SMT value for Int witness extraction".to_owned()),
        },
        IRType::Identity => match val {
            SmtValue::Int(i) => model
                .eval(i, true)
                .map(|v| op::WitnessValue::Identity(format!("{v}")))
                .ok_or_else(|| "failed to evaluate Int-backed identity witness value".to_owned()),
            SmtValue::Dynamic(d) => model
                .eval(d, true)
                .map(|v| op::WitnessValue::Identity(format!("{v}")))
                .ok_or_else(|| "failed to evaluate dynamic identity witness value".to_owned()),
            _ => Err("expected Int or Dynamic SMT value for identity extraction".to_owned()),
        },
        IRType::Real => match val {
            SmtValue::Real(r) => model
                .eval(r, true)
                .map(|v| op::WitnessValue::Real(format!("{v}")))
                .ok_or_else(|| "failed to evaluate Real witness value".to_owned()),
            _ => Err("expected Real SMT value for Real witness extraction".to_owned()),
        },
        IRType::Float => match val {
            SmtValue::Real(r) => model
                .eval(r, true)
                .map(|v| op::WitnessValue::Float(format!("{v}")))
                .ok_or_else(|| "failed to evaluate Float witness value".to_owned()),
            _ => Err("expected Real SMT value for Float witness extraction".to_owned()),
        },
        IRType::Enum { name, .. } => match val {
            SmtValue::Int(i) => {
                if let Some(id) = model.eval(i, true).and_then(|v| v.as_i64()) {
                    if let Some((enum_name, variant)) = variants.name_of(id) {
                        return Ok(op::WitnessValue::EnumVariant {
                            enum_name: enum_name.clone(),
                            variant: variant.clone(),
                        });
                    }
                    Ok(op::WitnessValue::Opaque {
                        display: id.to_string(),
                        ty: Some(name.clone()),
                    })
                } else {
                    Err("failed to evaluate enum witness value".to_owned())
                }
            }
            SmtValue::Dynamic(d) => model
                .eval(d, true)
                .map(|v| op::WitnessValue::Opaque {
                    display: format!("{v}"),
                    ty: Some(name.clone()),
                })
                .ok_or_else(|| "failed to evaluate dynamic enum witness value".to_owned()),
            _ => Err("expected Int or Dynamic SMT value for enum extraction".to_owned()),
        },
        IRType::String
        | IRType::Record { .. }
        | IRType::Fn { .. }
        | IRType::Entity { .. }
        | IRType::Set { .. }
        | IRType::Seq { .. }
        | IRType::Map { .. }
        | IRType::Tuple { .. } => {
            let ty_name = render_ir_type(ty);
            match val {
                SmtValue::Int(i) => model
                    .eval(i, true)
                    .map(|v| op::WitnessValue::Opaque {
                        display: format!("{v}"),
                        ty: Some(ty_name),
                    })
                    .ok_or_else(|| "failed to evaluate Int-backed opaque witness value".to_owned()),
                SmtValue::Bool(b) => model
                    .eval(b, true)
                    .map(|v| op::WitnessValue::Opaque {
                        display: format!("{v}"),
                        ty: Some(ty_name),
                    })
                    .ok_or_else(|| {
                        "failed to evaluate Bool-backed opaque witness value".to_owned()
                    }),
                SmtValue::Real(r) => model
                    .eval(r, true)
                    .map(|v| op::WitnessValue::Opaque {
                        display: format!("{v}"),
                        ty: Some(ty_name),
                    })
                    .ok_or_else(|| {
                        "failed to evaluate Real-backed opaque witness value".to_owned()
                    }),
                SmtValue::Dynamic(d) => model
                    .eval(d, true)
                    .map(|v| op::WitnessValue::Opaque {
                        display: format!("{v}"),
                        ty: Some(ty_name),
                    })
                    .ok_or_else(|| {
                        "failed to evaluate Dynamic-backed opaque witness value".to_owned()
                    }),
                SmtValue::Array(a) => model
                    .eval(a, true)
                    .map(|v| op::WitnessValue::Opaque {
                        display: format!("{v}"),
                        ty: Some(ty_name),
                    })
                    .ok_or_else(|| {
                        "failed to evaluate Array-backed opaque witness value".to_owned()
                    }),
                SmtValue::Func(_) => Ok(op::WitnessValue::Opaque {
                    display: "?".to_owned(),
                    ty: Some(ty_name),
                }),
            }
        }
    }
}

fn extract_state_from_model(
    model: &Model,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    step: usize,
) -> Result<op::State, String> {
    let mut state = op::State::builder();

    for entity in entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            let active = match pool.active_at(&entity.name, slot, step) {
                Some(SmtValue::Bool(act)) => model
                    .eval(act, true)
                    .and_then(|v| v.as_bool())
                    .ok_or_else(|| {
                        format!(
                            "failed to evaluate active flag for {}[{slot}] at step {step}",
                            entity.name
                        )
                    })?,
                Some(_) => {
                    return Err(format!(
                        "active flag for {}[{slot}] at step {step} was not Bool",
                        entity.name
                    ));
                }
                None => {
                    return Err(format!(
                        "missing active flag for {}[{slot}] at step {step}",
                        entity.name
                    ));
                }
            };

            let mut entity_state = op::EntityState::builder(active);
            for field in &entity.fields {
                let val = pool
                    .field_at(&entity.name, slot, &field.name, step)
                    .ok_or_else(|| {
                        format!(
                            "missing field {} for {}[{slot}] at step {step}",
                            field.name, entity.name
                        )
                    })?;
                entity_state = entity_state.field(
                    field.name.clone(),
                    extract_witness_value(model, val, &vctx.variants, &field.ty).map_err(
                        |err| {
                            format!(
                                "failed to extract {}.{} for slot {slot} at step {step}: {err}",
                                entity.name, field.name
                            )
                        },
                    )?,
                );
            }

            state = state.entity_slot(
                op::EntitySlotRef::new(entity.name.clone(), slot),
                entity_state.build(),
            );
        }
    }

    for system in systems {
        for field in &system.fields {
            let val = pool
                .system_field_at(&system.name, &field.name, step)
                .ok_or_else(|| {
                    format!(
                        "missing system field {}.{} at step {step}",
                        system.name, field.name
                    )
                })?;
            state = state.system_field(
                system.name.clone(),
                field.name.clone(),
                extract_witness_value(model, val, &vctx.variants, &field.ty).map_err(|err| {
                    format!(
                        "failed to extract system field {}.{} at step {step}: {err}",
                        system.name, field.name
                    )
                })?,
            );
        }
    }

    Ok(state.build())
}

fn relational_state_from_operational_state(
    state: &op::State,
) -> Result<rel::RelationalState, String> {
    let mut builder = rel::RelationalState::builder();
    let mut field_tuples: HashMap<rel::RelationId, Vec<rel::TupleValue>> = HashMap::new();

    for (slot_ref, entity_state) in state.entity_slots() {
        if entity_state.active() {
            builder = builder
                .extent_member(slot_ref.entity().to_owned(), slot_ref.clone())
                .map_err(|err| format!("generated relational extent member is invalid: {err}"))?;
        }

        for (field_name, value) in entity_state.fields() {
            let relation = rel::RelationId::field(slot_ref.entity().to_owned(), field_name.clone())
                .map_err(|err| format!("generated entity field relation id is invalid: {err}"))?;
            field_tuples
                .entry(relation)
                .or_default()
                .push(rel::TupleValue::new(vec![
                    op::WitnessValue::SlotRef(slot_ref.clone()),
                    value.clone(),
                ]));
        }
    }

    for (system_name, fields) in state.system_fields() {
        for (field_name, value) in fields {
            let relation = rel::RelationId::field(system_name.clone(), field_name.clone())
                .map_err(|err| format!("generated system field relation id is invalid: {err}"))?;
            field_tuples
                .entry(relation)
                .or_default()
                .push(rel::TupleValue::new(vec![
                    op::WitnessValue::Identity(system_name.clone()),
                    value.clone(),
                ]));
        }
    }

    for (relation_id, tuples) in field_tuples {
        let mut relation = rel::RelationInstance::builder(2);
        for tuple in tuples {
            relation = relation
                .tuple(tuple)
                .map_err(|err| format!("generated relational field tuple is invalid: {err}"))?;
        }
        builder = builder
            .relation_instance(
                relation_id,
                relation.build().map_err(|err| {
                    format!("generated relational field relation is invalid: {err}")
                })?,
            )
            .map_err(|err| format!("generated relational field relation id is invalid: {err}"))?;
    }

    builder
        .build()
        .map_err(|err| format!("relational state projection failed validation: {err}"))
}

fn extract_relational_states(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
) -> Result<Vec<rel::RelationalState>, String> {
    let model = solver
        .get_model()
        .ok_or_else(|| "solver did not provide a model for relational extraction".to_owned())?;

    let mut states = Vec::with_capacity(bound + 1);
    for step in 0..=bound {
        let operational = extract_state_from_model(&model, pool, vctx, entities, systems, step)?;
        states.push(relational_state_from_operational_state(&operational)?);
    }
    Ok(states)
}

fn step_param_symbol(param_name: &str, step: usize, ty: &IRType) -> SmtValue {
    match ty {
        IRType::Bool => smt::bool_var(&format!("param_{param_name}_{step}")),
        IRType::Real | IRType::Float => smt::real_var(&format!("param_{param_name}_{step}")),
        _ => smt::int_var(&format!("param_{param_name}_{step}")),
    }
}

fn extract_command_params(
    model: &Model,
    vctx: &VerifyContext,
    system: &str,
    command: &str,
    step: usize,
) -> Result<Vec<op::Binding>, String> {
    let Some(params) = vctx
        .command_params
        .get(&(system.to_owned(), command.to_owned()))
    else {
        return Ok(Vec::new());
    };

    params
        .iter()
        .map(|param| {
            let value = extract_witness_value(
                model,
                &step_param_symbol(&param.name, step, &param.ty),
                &vctx.variants,
                &param.ty,
            )
            .map_err(|err| {
                format!(
                    "failed to extract command parameter {system}::{command}({}) at step {step}: {err}",
                    param.name
                )
            })?;
            op::Binding::new(param.name.clone(), value)
                .map(|binding| binding.with_ty_hint(render_ir_type(&param.ty)))
                .map_err(|err| {
                    format!(
                        "generated command parameter binding {} for {system}::{command} is invalid: {err}",
                        param.name
                    )
                })
        })
        .collect()
}

fn extract_transition_from_fire(
    model: &Model,
    fire_tracking: &FireTracking,
    vctx: &VerifyContext,
    systems: &[IRSystem],
    step: usize,
) -> Result<op::Transition, String> {
    let mut transition = op::Transition::builder();

    for system in systems {
        let mut command_ordinals: HashMap<&str, usize> = HashMap::new();
        for (clause_idx, step_decl) in system.steps.iter().enumerate() {
            let command_name = step_decl.name.as_str();
            let key = (system.name.clone(), command_name.to_owned(), clause_idx);
            let fire_bool = fire_tracking
                .clause_fire_vars
                .get(&key)
                .and_then(|step_fires| step_fires.get(step))
                .ok_or_else(|| {
                    format!(
                        "missing fire-tracking variable for {}::{command_name} clause {} at step {step}",
                        system.name,
                        clause_idx + 1
                    )
                })?;
            let fired = model
                .eval(fire_bool, true)
                .and_then(|value| value.as_bool())
                .ok_or_else(|| {
                    format!(
                        "failed to evaluate fire-tracking variable for {}::{command_name} clause {} at step {step}",
                        system.name,
                        clause_idx + 1
                    )
                })?;

            if !fired {
                continue;
            }

            let ordinal = command_ordinals
                .entry(command_name)
                .and_modify(|value| *value += 1)
                .or_insert(1);

            let step_id = op::AtomicStepId::new(format!(
                "{step}:{}::{command_name}#{}",
                system.name,
                clause_idx + 1
            ))
            .map_err(|err| format!("generated atomic step id is invalid: {err}"))?;
            let mut atomic_step =
                op::AtomicStep::builder(step_id, system.name.clone(), command_name.to_owned());
            atomic_step = atomic_step.step_name(format!("{command_name}#{ordinal}"));
            let param_bindings =
                extract_command_params(model, vctx, &system.name, command_name, step)?;
            for binding in param_bindings.iter().cloned() {
                atomic_step = atomic_step.param(binding);
            }
            let saw_observation = if is_extern_boundary_system(system) {
                let args = param_bindings
                    .iter()
                    .map(|binding| render_observation_witness_value(binding.value()))
                    .collect::<Vec<_>>()
                    .join(", ");
                Some(
                    op::TransitionObservation::new(
                        "saw",
                        op::WitnessValue::String(format!(
                            "{}::{}({args})",
                            system.name, command_name
                        )),
                    )
                    .map_err(|err| format!("generated saw observation is invalid: {err}"))?,
                )
            } else {
                None
            };
            transition = transition.atomic_step(
                atomic_step
                    .build()
                    .map_err(|err| format!("operational atomic step extraction failed: {err}"))?,
            );
            if let Some(saw_observation) = saw_observation {
                transition = transition.observation(saw_observation);
            }
        }
    }

    let is_stutter = match fire_tracking.stutter_vars.get(step) {
        Some(stutter_bool) => model
            .eval(stutter_bool, true)
            .and_then(|value| value.as_bool())
            .ok_or_else(|| {
                format!("failed to evaluate stutter-tracking variable at step {step}")
            })?,
        None => false,
    };
    if is_stutter {
        transition = transition.observation(
            op::TransitionObservation::new("stutter", op::WitnessValue::Bool(true))
                .map_err(|err| format!("generated stutter observation is invalid: {err}"))?,
        );
    }

    transition
        .build()
        .map_err(|err| format!("operational transition extraction failed: {err}"))
}

fn extract_behavior_with_fire(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire_tracking: &FireTracking,
    bound: usize,
) -> Result<op::Behavior, String> {
    let model = solver
        .get_model()
        .ok_or_else(|| "solver did not provide a model for operational extraction".to_owned())?;

    let mut behavior = op::Behavior::builder();

    for step in 0..=bound {
        behavior = behavior.state(extract_state_from_model(
            &model, pool, vctx, entities, systems, step,
        )?);

        if step < bound {
            let transition =
                extract_transition_from_fire(&model, fire_tracking, vctx, systems, step)?;
            behavior = behavior.transition(transition);
        }
    }

    behavior
        .build()
        .map_err(|err| format!("operational behavior extraction failed: {err}"))
}

pub(super) fn extract_initial_operational_deadlock(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
) -> Result<op::OperationalWitness, String> {
    let model = solver.get_model().ok_or_else(|| {
        "solver did not provide a model for initial deadlock extraction".to_owned()
    })?;

    let behavior = op::Behavior::builder()
        .state(extract_state_from_model(
            &model, pool, vctx, entities, systems, 0,
        )?)
        .build()
        .map_err(|err| format!("initial deadlock behavior extraction failed: {err}"))?;

    op::OperationalWitness::deadlock(behavior)
        .map_err(|err| format!("initial deadlock witness validation failed: {err}"))
}

pub(super) fn extract_initial_relational_deadlock(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
) -> Result<rel::RelationalWitness, String> {
    let states = extract_relational_states(solver, pool, vctx, entities, systems, 0)?;
    let state = states
        .into_iter()
        .next()
        .ok_or_else(|| "initial relational deadlock is missing its snapshot state".to_owned())?;
    rel::RelationalWitness::snapshot(state)
        .map_err(|err| format!("initial relational deadlock witness validation failed: {err}"))
}

pub(super) fn extract_operational_counterexample_with_fire(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire_tracking: &FireTracking,
    bound: usize,
) -> Result<op::OperationalWitness, String> {
    let behavior =
        extract_behavior_with_fire(solver, pool, vctx, entities, systems, fire_tracking, bound)?;
    op::OperationalWitness::counterexample(behavior)
        .map_err(|err| format!("operational counterexample witness validation failed: {err}"))
}

pub(super) fn extract_relational_counterexample(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
) -> Result<rel::RelationalWitness, String> {
    let states = extract_relational_states(solver, pool, vctx, entities, systems, bound)?;
    let temporal = rel::TemporalRelationalWitness::new(states, None).map_err(|err| {
        format!("bounded relational counterexample witness validation failed: {err}")
    })?;
    rel::RelationalWitness::temporal(temporal).map_err(|err| {
        format!("bounded relational counterexample envelope validation failed: {err}")
    })
}

pub(super) fn extract_operational_deadlock_with_fire(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire_tracking: &FireTracking,
    bound: usize,
) -> Result<op::OperationalWitness, String> {
    let behavior =
        extract_behavior_with_fire(solver, pool, vctx, entities, systems, fire_tracking, bound)?;
    op::OperationalWitness::deadlock(behavior)
        .map_err(|err| format!("operational deadlock witness validation failed: {err}"))
}

pub(super) fn extract_relational_deadlock(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
) -> Result<rel::RelationalWitness, String> {
    let states = extract_relational_states(solver, pool, vctx, entities, systems, bound)?;
    let temporal = rel::TemporalRelationalWitness::new(states, None)
        .map_err(|err| format!("bounded relational deadlock witness validation failed: {err}"))?;
    rel::RelationalWitness::temporal(temporal)
        .map_err(|err| format!("bounded relational deadlock envelope validation failed: {err}"))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn extract_operational_liveness_with_fire(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire_tracking: &FireTracking,
    bound: usize,
    loop_start: usize,
) -> Result<op::OperationalWitness, String> {
    let behavior =
        extract_behavior_with_fire(solver, pool, vctx, entities, systems, fire_tracking, bound)?;
    op::OperationalWitness::liveness(behavior, loop_start)
        .map_err(|err| format!("operational liveness witness validation failed: {err}"))
}

pub(super) fn extract_relational_liveness(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
    loop_start: usize,
) -> Result<rel::RelationalWitness, String> {
    let states = extract_relational_states(solver, pool, vctx, entities, systems, bound)?;
    let temporal = rel::TemporalRelationalWitness::new(states, Some(loop_start))
        .map_err(|err| format!("bounded relational liveness witness validation failed: {err}"))?;
    rel::RelationalWitness::temporal(temporal)
        .map_err(|err| format!("bounded relational liveness envelope validation failed: {err}"))
}

pub(super) fn render_witness_value(value: &op::WitnessValue) -> String {
    match value {
        op::WitnessValue::Unknown => "?".to_owned(),
        op::WitnessValue::Int(v) => v.to_string(),
        op::WitnessValue::Bool(v) => v.to_string(),
        op::WitnessValue::Real(v)
        | op::WitnessValue::Float(v)
        | op::WitnessValue::String(v)
        | op::WitnessValue::Identity(v) => v.clone(),
        op::WitnessValue::EnumVariant { enum_name, variant } => format!("@{enum_name}::{variant}"),
        op::WitnessValue::SlotRef(slot) => format!("{}[{}]", slot.entity(), slot.slot()),
        op::WitnessValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!("{name}: {}", render_witness_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Set(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Seq(values) => format!(
            "[{}]",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, value)| format!(
                    "{} -> {}",
                    render_witness_value(key),
                    render_witness_value(value)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Opaque { display, .. } => display.clone(),
    }
}

fn render_transition_event_label(
    transition: &op::Transition,
    system_count: usize,
) -> Option<String> {
    let labels: Vec<String> = transition
        .atomic_steps()
        .iter()
        .map(|atomic_step| {
            if system_count == 1 {
                atomic_step.command().to_owned()
            } else {
                format!("{}::{}", atomic_step.system(), atomic_step.command())
            }
        })
        .collect();

    match labels.len() {
        0 => None,
        1 => labels.into_iter().next(),
        _ => Some(labels.join(" & ")),
    }
}

pub(super) fn behavior_to_trace_steps(
    behavior: &op::Behavior,
    system_count: usize,
) -> Vec<TraceStep> {
    behavior
        .states()
        .iter()
        .enumerate()
        .map(|(step, state)| {
            let mut entity_slot_counts: HashMap<&str, usize> = HashMap::new();
            for slot_ref in state.entity_slots().keys() {
                *entity_slot_counts.entry(slot_ref.entity()).or_default() += 1;
            }

            let mut assignments = Vec::new();
            for (slot_ref, entity_state) in state.entity_slots() {
                if !entity_state.active() {
                    continue;
                }
                let entity_label = if entity_slot_counts
                    .get(slot_ref.entity())
                    .copied()
                    .unwrap_or(0)
                    > 1
                {
                    format!("{}[{}]", slot_ref.entity(), slot_ref.slot())
                } else {
                    slot_ref.entity().to_owned()
                };
                for (field, value) in entity_state.fields() {
                    assignments.push((
                        entity_label.clone(),
                        field.clone(),
                        render_witness_value(value),
                    ));
                }
            }
            for (system, fields) in state.system_fields() {
                for (field, value) in fields {
                    assignments.push((
                        format!("System::{system}"),
                        field.clone(),
                        render_witness_value(value),
                    ));
                }
            }

            TraceStep {
                step,
                event: behavior
                    .transition_after_state(step)
                    .and_then(|transition| render_transition_event_label(transition, system_count)),
                assignments,
            }
        })
        .collect()
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRActionMatchArm, IRActionMatchScrutinee, IRAggKind, IRField, IRMatchArm, IRPattern,
        IRTransition, IRUpdate, IRVariant, LetBinding, LitVal,
    };

    fn atomic_step(id: &str, system: &str, command: &str) -> op::AtomicStep {
        op::AtomicStep::builder(
            op::AtomicStepId::new(id).expect("test atomic step id"),
            system,
            command,
        )
        .build()
        .expect("test atomic step")
    }

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn int_lit(value: i64) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
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

    fn field(expr: IRExpr, name: &str, ty: IRType) -> IRExpr {
        IRExpr::Field {
            expr: Box::new(expr),
            field: name.to_owned(),
            ty,
            span: None,
        }
    }

    fn bin(op: &str, left: IRExpr, right: IRExpr, ty: IRType) -> IRExpr {
        IRExpr::BinOp {
            op: op.to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty,
            span: None,
        }
    }

    fn test_entity() -> IREntity {
        IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "OrderStatus".to_owned(),
                    variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
                },
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "confirm".to_owned(),
                refs: vec![],
                params: vec![],
                guard: bool_lit(true),
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        }
    }

    fn test_system(name: &str, steps: Vec<crate::ir::types::IRStep>) -> IRSystem {
        IRSystem {
            name: name.to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps,
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        }
    }

    fn test_step(name: &str, body: Vec<IRAction>) -> crate::ir::types::IRStep {
        crate::ir::types::IRStep {
            name: name.to_owned(),
            params: vec![],
            guard: bool_lit(true),
            body,
            return_expr: None,
        }
    }

    #[test]
    fn witness_value_renderers_cover_composite_shapes() {
        let slot = op::EntitySlotRef::new("Order", 2);
        let tuple = op::WitnessValue::Tuple(vec![
            op::WitnessValue::Unknown,
            op::WitnessValue::Bool(true),
            op::WitnessValue::Int(3),
            op::WitnessValue::Real("1/2".to_owned()),
            op::WitnessValue::Float("1.5".to_owned()),
            op::WitnessValue::String("txt".to_owned()),
            op::WitnessValue::Identity("id-1".to_owned()),
            op::WitnessValue::EnumVariant {
                enum_name: "OrderStatus".to_owned(),
                variant: "Pending".to_owned(),
            },
            op::WitnessValue::SlotRef(slot.clone()),
            op::WitnessValue::Set(vec![op::WitnessValue::Int(1), op::WitnessValue::Int(2)]),
            op::WitnessValue::Seq(vec![op::WitnessValue::Bool(false)]),
            op::WitnessValue::Map(vec![(
                op::WitnessValue::String("k".to_owned()),
                op::WitnessValue::String("v".to_owned()),
            )]),
            op::WitnessValue::Record(std::collections::BTreeMap::from([(
                "field".to_owned(),
                op::WitnessValue::Opaque {
                    display: "opaque".to_owned(),
                    ty: Some("Opaque".to_owned()),
                },
            )])),
        ]);

        let rendered = render_witness_value(&tuple);
        assert!(rendered.contains("?"));
        assert!(rendered.contains("true"));
        assert!(rendered.contains("@OrderStatus::Pending"));
        assert!(rendered.contains("Order[2]"));
        assert!(rendered.contains("{1, 2}"));
        assert!(rendered.contains("[false]"));
        assert!(rendered.contains("k -> v"));
        assert!(rendered.contains("field: opaque"));

        let observation_rendered = render_observation_witness_value(&tuple);
        assert_eq!(observation_rendered, rendered);
    }

    #[test]
    fn render_ir_type_covers_all_shapes() {
        let refinement = IRType::Refinement {
            base: Box::new(IRType::Int),
            predicate: Box::new(bool_lit(true)),
        };
        let types = vec![
            (IRType::Int, "Int"),
            (IRType::Bool, "Bool"),
            (IRType::String, "String"),
            (IRType::Identity, "Identity"),
            (IRType::Real, "Real"),
            (IRType::Float, "Float"),
            (
                IRType::Enum {
                    name: "OrderStatus".to_owned(),
                    variants: vec![IRVariant::simple("Pending")],
                },
                "OrderStatus",
            ),
            (
                IRType::Record {
                    name: "Payload".to_owned(),
                    fields: vec![],
                },
                "Payload",
            ),
            (
                IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
                "Fn",
            ),
            (
                IRType::Entity {
                    name: "Order".to_owned(),
                },
                "Entity<Order>",
            ),
            (
                IRType::Set {
                    element: Box::new(IRType::Bool),
                },
                "Set<Bool>",
            ),
            (
                IRType::Seq {
                    element: Box::new(IRType::Real),
                },
                "Seq<Real>",
            ),
            (
                IRType::Map {
                    key: Box::new(IRType::String),
                    value: Box::new(IRType::Float),
                },
                "Map<String, Float>",
            ),
            (
                IRType::Tuple {
                    elements: vec![IRType::Int, IRType::Bool],
                },
                "(Int, Bool)",
            ),
            (refinement, "Int"),
        ];

        for (ty, expected) in types {
            assert_eq!(render_ir_type(&ty), expected);
        }
    }

    #[test]
    fn expression_predicates_walk_nested_forms() {
        let assert_expr = IRExpr::Assert {
            expr: Box::new(bool_lit(true)),
            span: None,
        };
        let assume_expr = IRExpr::Assume {
            expr: Box::new(bool_lit(true)),
            span: None,
        };
        let sorry_expr = IRExpr::Sorry { span: None };
        let nested = IRExpr::Block {
            exprs: vec![
                IRExpr::While {
                    cond: Box::new(bool_lit(true)),
                    invariants: vec![assert_expr.clone()],
                    decreases: None,
                    body: Box::new(IRExpr::IfElse {
                        cond: Box::new(bool_lit(true)),
                        then_body: Box::new(assume_expr.clone()),
                        else_body: Some(Box::new(IRExpr::Let {
                            bindings: vec![LetBinding {
                                name: "x".to_owned(),
                                ty: IRType::Int,
                                expr: int_lit(1),
                            }],
                            body: Box::new(sorry_expr.clone()),
                            span: None,
                        })),
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Aggregate {
                    kind: IRAggKind::Count,
                    var: "o".to_owned(),
                    domain: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    body: Box::new(bool_lit(true)),
                    in_filter: Some(Box::new(IRExpr::Saw {
                        system_name: "Commerce".to_owned(),
                        event_name: "confirm".to_owned(),
                        args: vec![Some(Box::new(assert_expr.clone()))],
                        span: None,
                    })),
                    span: None,
                },
            ],
            span: None,
        };

        assert!(contains_imperative(&nested));
        assert!(body_contains_assert(&nested));
        assert!(body_contains_assume(&nested));
        assert!(body_contains_sorry(&nested));
        assert!(contains_imperative(&bin(
            "OpEq",
            var("x", IRType::Int),
            int_lit(1),
            IRType::Bool,
        )));
        assert!(body_contains_assert(&IRExpr::Saw {
            system_name: "Commerce".to_owned(),
            event_name: "confirm".to_owned(),
            args: vec![Some(Box::new(assert_expr.clone())), None],
            span: None,
        }));
        assert!(body_contains_assert(&IRExpr::Aggregate {
            kind: IRAggKind::Count,
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(bool_lit(true)),
            in_filter: Some(Box::new(assert_expr.clone())),
            span: None,
        }));
        assert!(body_contains_sorry(&IRExpr::MapUpdate {
            map: Box::new(var(
                "m",
                IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Bool),
                }
            )),
            key: Box::new(int_lit(1)),
            value: Box::new(sorry_expr.clone()),
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Bool),
            },
            span: None,
        }));
        assert!(body_contains_sorry(&IRExpr::MapLit {
            entries: vec![(int_lit(1), sorry_expr.clone())],
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Bool),
            },
            span: None,
        }));
        assert!(body_contains_sorry(&IRExpr::Saw {
            system_name: "Commerce".to_owned(),
            event_name: "confirm".to_owned(),
            args: vec![Some(Box::new(sorry_expr.clone()))],
            span: None,
        }));
        assert!(body_contains_sorry(&IRExpr::Aggregate {
            kind: IRAggKind::Count,
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(bool_lit(true)),
            in_filter: Some(Box::new(sorry_expr)),
            span: None,
        }));
        assert!(!contains_imperative(&IRExpr::Always {
            body: Box::new(bool_lit(true)),
            span: None,
        }));
    }

    #[test]
    fn expression_helpers_cover_remaining_recursive_branches() {
        let assert_expr = IRExpr::Assert {
            expr: Box::new(bool_lit(true)),
            span: None,
        };
        let assume_expr = IRExpr::Assume {
            expr: Box::new(bool_lit(true)),
            span: None,
        };
        let sorry_expr = IRExpr::Sorry { span: None };
        let map_ty = IRType::Map {
            key: Box::new(IRType::Int),
            value: Box::new(IRType::Bool),
        };

        assert!(body_contains_assert(&IRExpr::Choose {
            var: "x".to_owned(),
            domain: IRType::Int,
            predicate: Some(Box::new(assert_expr.clone())),
            ty: IRType::Int,
            span: None,
        }));
        assert!(body_contains_assert(&IRExpr::MapUpdate {
            map: Box::new(var("m", map_ty.clone())),
            key: Box::new(int_lit(1)),
            value: Box::new(assert_expr.clone()),
            ty: map_ty.clone(),
            span: None,
        }));
        assert!(body_contains_assert(&IRExpr::MapLit {
            entries: vec![(int_lit(1), assert_expr.clone())],
            ty: map_ty.clone(),
            span: None,
        }));
        assert!(body_contains_assert(&IRExpr::Since {
            left: Box::new(bool_lit(true)),
            right: Box::new(assert_expr.clone()),
            span: None,
        }));

        for wrapper in [
            IRExpr::Always {
                body: Box::new(sorry_expr.clone()),
                span: None,
            },
            IRExpr::Eventually {
                body: Box::new(sorry_expr.clone()),
                span: None,
            },
            IRExpr::Historically {
                body: Box::new(sorry_expr.clone()),
                span: None,
            },
            IRExpr::Once {
                body: Box::new(sorry_expr.clone()),
                span: None,
            },
            IRExpr::Previously {
                body: Box::new(sorry_expr.clone()),
                span: None,
            },
        ] {
            assert!(body_contains_sorry(&wrapper));
        }
        assert!(body_contains_sorry(&IRExpr::Choose {
            var: "x".to_owned(),
            domain: IRType::Int,
            predicate: Some(Box::new(sorry_expr.clone())),
            ty: IRType::Int,
            span: None,
        }));
        assert!(body_contains_sorry(&IRExpr::Since {
            left: Box::new(bool_lit(true)),
            right: Box::new(sorry_expr.clone()),
            span: None,
        }));

        let match_with_assume = IRExpr::Match {
            scrutinee: Box::new(bool_lit(false)),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PWild,
                guard: Some(bool_lit(true)),
                body: assume_expr,
            }],
            span: None,
        };
        assert!(body_contains_assume(&match_with_assume));
    }

    #[test]
    fn collect_def_refs_respects_binders_and_pattern_shadowing() {
        let expr = IRExpr::Let {
            bindings: vec![LetBinding {
                name: "local".to_owned(),
                ty: IRType::Int,
                expr: var("free_rhs", IRType::Int),
            }],
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(var("scrutinee", IRType::Int)),
                arms: vec![IRMatchArm {
                    pattern: IRPattern::POr {
                        left: Box::new(IRPattern::PVar {
                            name: "matched".to_owned(),
                        }),
                        right: Box::new(IRPattern::PVar {
                            name: "matched".to_owned(),
                        }),
                    },
                    guard: Some(bin(
                        "OpGt",
                        var("matched", IRType::Int),
                        var("free_guard", IRType::Int),
                        IRType::Bool,
                    )),
                    body: IRExpr::SetComp {
                        var: "item".to_owned(),
                        domain: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        filter: Box::new(bin(
                            "OpEq",
                            var(
                                "item",
                                IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                            ),
                            var(
                                "free_filter",
                                IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                            ),
                            IRType::Bool,
                        )),
                        projection: Some(Box::new(var("free_projection", IRType::Int))),
                        ty: IRType::Set {
                            element: Box::new(IRType::Int),
                        },
                        span: None,
                    },
                }],
                span: None,
            }),
            span: None,
        };

        let mut refs = HashSet::new();
        collect_def_refs_in_exprs(&[expr], &mut refs);

        assert!(refs.contains("free_rhs"));
        assert!(refs.contains("scrutinee"));
        assert!(refs.contains("free_guard"));
        assert!(refs.contains("free_filter"));
        assert!(refs.contains("free_projection"));
        assert!(!refs.contains("local"));
        assert!(!refs.contains("matched"));
        assert!(!refs.contains("item"));

        let mut more_refs = HashSet::new();
        collect_def_refs_in_exprs(
            &[
                IRExpr::Lam {
                    param: "bound".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(var("free_lam", IRType::Int)),
                    span: None,
                },
                IRExpr::Prime {
                    expr: Box::new(var("prime_ref", IRType::Int)),
                    span: None,
                },
                IRExpr::Historically {
                    body: Box::new(var("history_ref", IRType::Bool)),
                    span: None,
                },
                IRExpr::Once {
                    body: Box::new(var("once_ref", IRType::Bool)),
                    span: None,
                },
                IRExpr::Previously {
                    body: Box::new(var("prev_ref", IRType::Bool)),
                    span: None,
                },
                IRExpr::MapUpdate {
                    map: Box::new(var(
                        "map_ref",
                        IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Bool),
                        },
                    )),
                    key: Box::new(var("key_ref", IRType::Int)),
                    value: Box::new(var("value_ref", IRType::Bool)),
                    ty: IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Bool),
                    },
                    span: None,
                },
            ],
            &mut more_refs,
        );
        assert!(more_refs.contains("free_lam"));
        assert!(!more_refs.contains("bound"));
        assert!(more_refs.contains("prime_ref"));
        assert!(more_refs.contains("history_ref"));
        assert!(more_refs.contains("once_ref"));
        assert!(more_refs.contains("prev_ref"));
        assert!(more_refs.contains("map_ref"));
        assert!(more_refs.contains("key_ref"));
        assert!(more_refs.contains("value_ref"));
    }

    #[test]
    fn scene_precheck_reports_supported_and_unsupported_shapes() {
        let entity_card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "o".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                filter: Box::new(bool_lit(true)),
                projection: None,
                ty: IRType::Set {
                    element: Box::new(IRType::Entity {
                        name: "Order".to_owned(),
                    }),
                },
                span: None,
            }),
            span: None,
        };
        assert_eq!(find_unsupported_scene_expr(&entity_card), None);

        let unsupported_card = IRExpr::Card {
            expr: Box::new(field(
                var(
                    "o",
                    IRType::Entity {
                        name: "Order".to_owned(),
                    },
                ),
                "status",
                IRType::Int,
            )),
            span: None,
        };
        assert_eq!(
            find_unsupported_scene_expr(&unsupported_card),
            Some("cardinality (#) of non-literal, non-comprehension expression")
        );

        let unresolved_app = IRExpr::App {
            func: Box::new(var(
                "unknown_fn",
                IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Bool),
                },
            )),
            arg: Box::new(int_lit(1)),
            ty: IRType::Bool,
            span: None,
        };
        assert_eq!(
            find_unsupported_scene_expr(&unresolved_app),
            Some(crate::messages::PRECHECK_UNRESOLVED_FN)
        );

        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::SetComp {
                var: "x".to_owned(),
                domain: IRType::Int,
                filter: Box::new(bool_lit(true)),
                projection: None,
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            }),
            Some("SetComp with non-entity domain")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Sorry { span: None }),
            Some("Sorry")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Todo { span: None }),
            Some("Todo")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Block {
                exprs: vec![bool_lit(true)],
                span: None,
            }),
            Some("Block")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::VarDecl {
                name: "x".to_owned(),
                ty: IRType::Int,
                init: Box::new(int_lit(0)),
                rest: Box::new(bool_lit(true)),
                span: None,
            }),
            Some("VarDecl")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::While {
                cond: Box::new(bool_lit(true)),
                invariants: vec![],
                decreases: None,
                body: Box::new(bool_lit(true)),
                span: None,
            }),
            Some("While")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Aggregate {
                kind: IRAggKind::Sum,
                var: "x".to_owned(),
                domain: IRType::Int,
                body: Box::new(IRExpr::Sorry { span: None }),
                in_filter: None,
                span: None,
            }),
            Some("Sorry")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::IfElse {
                cond: Box::new(bool_lit(true)),
                then_body: Box::new(bool_lit(true)),
                else_body: Some(Box::new(IRExpr::Todo { span: None })),
                span: None,
            }),
            Some("Todo")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Saw {
                system_name: "Commerce".to_owned(),
                event_name: "confirm".to_owned(),
                args: vec![Some(Box::new(IRExpr::Sorry { span: None }))],
                span: None,
            }),
            Some("Sorry")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Choose {
                var: "x".to_owned(),
                domain: IRType::Int,
                predicate: Some(Box::new(IRExpr::Todo { span: None })),
                ty: IRType::Int,
                span: None,
            }),
            Some("Todo")
        );
        assert_eq!(
            find_unsupported_scene_expr(&IRExpr::Assume {
                expr: Box::new(IRExpr::Sorry { span: None }),
                span: None,
            }),
            Some("Sorry")
        );
    }

    #[test]
    fn action_collectors_follow_nested_crosscalls_and_matches() {
        let create_order = IRAction::Create {
            entity: "Order".to_owned(),
            fields: vec![],
        };
        let apply_confirm = IRAction::Apply {
            target: "Order".to_owned(),
            transition: "confirm".to_owned(),
            refs: vec![],
            args: vec![],
        };
        let callee = test_system(
            "Callee",
            vec![test_step("make", vec![create_order.clone()])],
        );
        let caller = test_system(
            "Caller",
            vec![test_step(
                "run",
                vec![
                    IRAction::Choose {
                        var: "o".to_owned(),
                        entity: "Order".to_owned(),
                        filter: Box::new(bool_lit(true)),
                        ops: vec![apply_confirm.clone()],
                    },
                    IRAction::CrossCall {
                        system: "Callee".to_owned(),
                        command: "make".to_owned(),
                        args: vec![],
                    },
                    IRAction::Match {
                        scrutinee: IRActionMatchScrutinee::Var {
                            name: "result".to_owned(),
                        },
                        arms: vec![IRActionMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: vec![IRAction::ForAll {
                                var: "each".to_owned(),
                                entity: "Order".to_owned(),
                                ops: vec![apply_confirm.clone()],
                            }],
                        }],
                    },
                ],
            )],
        );
        let systems = vec![caller.clone(), callee];
        let step_body = &caller.steps[0].body;

        assert_eq!(scan_event_creates(step_body, &systems), vec!["Order"]);
        assert_eq!(
            scan_event_creates(
                &[
                    create_order.clone(),
                    IRAction::ForAll {
                        var: "o".to_owned(),
                        entity: "Order".to_owned(),
                        ops: vec![create_order.clone()],
                    },
                ],
                &systems,
            ),
            vec!["Order"]
        );

        let mut entities = HashSet::new();
        let mut visited = HashSet::new();
        collect_event_body_entities(step_body, &systems, &mut entities, &mut visited);
        assert!(entities.contains("Order"));
        assert!(visited.contains(&("Callee".to_owned(), "make".to_owned())));
        collect_event_body_entities(
            &[
                IRAction::LetCrossCall {
                    name: "made".to_owned(),
                    system: "Callee".to_owned(),
                    command: "make".to_owned(),
                    args: vec![],
                },
                IRAction::ExprStmt {
                    expr: bool_lit(true),
                },
            ],
            &systems,
            &mut entities,
            &mut visited,
        );

        let modified = collect_event_modified_fields(step_body, &[test_entity()]);
        assert!(modified.contains(&("Order".to_owned(), "status".to_owned())));
        assert_eq!(
            collect_event_created_entities(step_body),
            Vec::<String>::new()
        );
    }

    #[test]
    fn field_and_quantifier_helpers_cover_recursive_paths() {
        let expr = IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Exists {
                var: "other".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Until {
                    left: Box::new(field(
                        var(
                            "o",
                            IRType::Entity {
                                name: "Order".to_owned(),
                            },
                        ),
                        "status",
                        IRType::Enum {
                            name: "OrderStatus".to_owned(),
                            variants: vec![IRVariant::simple("Pending")],
                        },
                    )),
                    right: Box::new(IRExpr::Eventually {
                        body: Box::new(field(
                            var(
                                "other",
                                IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                            ),
                            "status",
                            IRType::Enum {
                                name: "OrderStatus".to_owned(),
                                variants: vec![IRVariant::simple("Confirmed")],
                            },
                        )),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        };

        let mut fields = HashSet::new();
        collect_field_refs_in_expr(&expr, "o", &mut fields);
        assert_eq!(fields, HashSet::from(["status".to_owned()]));
        assert!(has_multi_entity_quantifier(&[&expr]));
    }

    #[test]
    fn behavior_to_trace_steps_renders_multi_step_transition_and_system_fields() {
        let state0 = op::State::builder()
            .entity_slot(
                op::EntitySlotRef::new("Order", 0),
                op::EntityState::builder(true)
                    .field(
                        "status",
                        op::WitnessValue::EnumVariant {
                            enum_name: "OrderStatus".to_owned(),
                            variant: "Pending".to_owned(),
                        },
                    )
                    .build(),
            )
            .system_field("Commerce", "queue_len", op::WitnessValue::Int(1))
            .build();

        let reserve = atomic_step("reserve", "Commerce", "reserve");
        let ship = atomic_step("ship", "Shipping", "ship");
        let transition = op::Transition::builder()
            .atomic_step(reserve.clone())
            .atomic_step(ship.clone())
            .relation(op::StepRelation::same_step(reserve.id(), ship.id()))
            .build()
            .expect("test transition");

        let state1 = op::State::builder()
            .entity_slot(
                op::EntitySlotRef::new("Order", 0),
                op::EntityState::builder(true)
                    .field(
                        "status",
                        op::WitnessValue::EnumVariant {
                            enum_name: "OrderStatus".to_owned(),
                            variant: "Confirmed".to_owned(),
                        },
                    )
                    .build(),
            )
            .system_field("Commerce", "queue_len", op::WitnessValue::Int(0))
            .build();

        let behavior = op::Behavior::builder()
            .state(state0)
            .transition(transition)
            .state(state1)
            .build()
            .expect("test behavior");

        let trace = behavior_to_trace_steps(&behavior, 2);

        assert_eq!(trace.len(), 2);
        assert_eq!(
            trace[0].event.as_deref(),
            Some("Commerce::reserve & Shipping::ship")
        );
        assert_eq!(trace[1].event, None);
        assert!(trace[0].assignments.contains(&(
            "Order".to_owned(),
            "status".to_owned(),
            "@OrderStatus::Pending".to_owned(),
        )));
        assert!(trace[0].assignments.contains(&(
            "System::Commerce".to_owned(),
            "queue_len".to_owned(),
            "1".to_owned(),
        )));
        assert!(trace[1].assignments.contains(&(
            "System::Commerce".to_owned(),
            "queue_len".to_owned(),
            "0".to_owned(),
        )));
    }

    #[test]
    fn behavior_to_trace_steps_renders_stutter_without_event_label() {
        let state0 = op::State::builder()
            .system_field("Commerce", "flag", op::WitnessValue::Bool(false))
            .build();
        let transition = op::Transition::builder()
            .observation(
                op::TransitionObservation::new("stutter", op::WitnessValue::Bool(true))
                    .expect("test stutter observation"),
            )
            .build()
            .expect("test stutter transition");
        let state1 = op::State::builder()
            .system_field("Commerce", "flag", op::WitnessValue::Bool(false))
            .build();
        let behavior = op::Behavior::builder()
            .state(state0)
            .transition(transition)
            .state(state1)
            .build()
            .expect("test behavior");

        let trace = behavior_to_trace_steps(&behavior, 1);

        assert_eq!(trace.len(), 2);
        assert_eq!(trace[0].event, None);
        assert_eq!(trace[1].event, None);
        assert!(trace[0].assignments.contains(&(
            "System::Commerce".to_owned(),
            "flag".to_owned(),
            "false".to_owned(),
        )));
    }
}

// ── Fairness analysis extraction ────────────────────────────────────

/// Extract per-event fairness analysis from a lasso counterexample model.
///
/// For each fair event (from `assumption_set.weak_fair` and `strong_fair`),
/// evaluates fire indicators and enabledness in the model to determine:
/// - `EnabledAndFired`: event was enabled and fired in the loop
/// - `EnabledButStarved`: event was enabled but never fired — starved
/// - `NeverEnabled`: event was never enabled at any loop step
#[allow(clippy::too_many_arguments)]
pub(super) fn extract_fairness_analysis(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire_tracking: &FireTracking,
    loop_start: usize,
    bound: usize,
    assumption_set: &crate::ir::types::IRAssumptionSet,
) -> Vec<FairnessEventAnalysis> {
    let Some(model) = solver.get_model() else {
        return Vec::new();
    };

    let mut results = Vec::new();

    // Process weak fair events
    for wf in &assumption_set.weak_fair {
        if let Some(analysis) = analyze_event_fairness(
            &model,
            pool,
            vctx,
            entities,
            systems,
            fire_tracking,
            &wf.system,
            &wf.command,
            FairnessKind::Weak,
            loop_start,
            bound,
        ) {
            results.push(analysis);
        }
    }

    // Process strong fair events
    for sf in &assumption_set.strong_fair {
        if let Some(analysis) = analyze_event_fairness(
            &model,
            pool,
            vctx,
            entities,
            systems,
            fire_tracking,
            &sf.system,
            &sf.command,
            FairnessKind::Strong,
            loop_start,
            bound,
        ) {
            results.push(analysis);
        }
    }

    results
}

/// Analyze a single event's fairness status in the lasso loop.
#[allow(clippy::too_many_arguments)]
fn analyze_event_fairness(
    model: &Model,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire_tracking: &FireTracking,
    sys_name: &str,
    evt_name: &str,
    kind: FairnessKind,
    loop_start: usize,
    bound: usize,
) -> Option<FairnessEventAnalysis> {
    let key = (sys_name.to_owned(), evt_name.to_owned());
    let fire_vec = fire_tracking.fire_vars.get(&key)?;

    // Check if the event fired at any step in the loop
    let mut fired = false;
    for step in loop_start..bound {
        if let Some(fire_bool) = fire_vec.get(step) {
            if let Some(val) = model.eval(fire_bool, true) {
                if val.as_bool() == Some(true) {
                    fired = true;
                    break;
                }
            }
        }
    }

    // Check enabledness at each loop step. A command may have multiple
    // step clauses — the command is enabled if ANY clause is enabled.
    let target_sys = systems.iter().find(|s| s.name == sys_name);
    let matching_steps: Vec<&crate::ir::types::IRStep> = target_sys
        .map(|s| s.steps.iter().filter(|st| st.name == evt_name).collect())
        .unwrap_or_default();

    let mut enabled_at_every_step = !matching_steps.is_empty();
    let mut enabled_somewhere = false;
    for step in loop_start..bound {
        let mut enabled_at_this_step = false;
        for event in &matching_steps {
            let Ok(enabled_bool) =
                harness::try_encode_step_enabled(pool, vctx, entities, systems, event, step)
            else {
                enabled_at_every_step = false;
                continue;
            };
            if let Some(val) = model.eval(&enabled_bool, true) {
                if val.as_bool() == Some(true) {
                    enabled_at_this_step = true;
                    break;
                }
            }
        }
        if enabled_at_this_step {
            enabled_somewhere = true;
        } else {
            enabled_at_every_step = false;
        }
    }

    // WF premise: enabled at EVERY loop step.
    // SF premise: enabled at SOME loop step.
    let fairness_premise_met = match kind {
        FairnessKind::Weak => enabled_at_every_step,
        FairnessKind::Strong => enabled_somewhere,
    };

    let status = if fired {
        FairnessStatus::EnabledAndFired
    } else if fairness_premise_met {
        FairnessStatus::EnabledButStarved
    } else {
        FairnessStatus::NeverEnabled
    };

    Some(FairnessEventAnalysis {
        system: sys_name.to_owned(),
        event: evt_name.to_owned(),
        kind,
        status,
    })
}

// ── Deadlock diagnostics extraction ─────────────────────────────────

/// Extract per-event diagnostics at a deadlocked state.
///
/// For each system event, evaluates the event's enabledness predicate
/// in the model at `deadlock_step` and reports why it is disabled.
pub(super) fn extract_deadlock_diagnostics(
    solver: &AbideSolver,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    deadlock_step: usize,
) -> Vec<DeadlockEventDiag> {
    let Some(model) = solver.get_model() else {
        return vec![];
    };

    let mut diagnostics = Vec::new();

    for system in systems {
        // Group step clauses by command name. A command is enabled if
        // ANY of its clauses is enabled (multi-clause dispatch).
        let mut seen_commands: HashSet<String> = HashSet::new();
        for event in &system.steps {
            if !seen_commands.insert(event.name.clone()) {
                continue; // already diagnosed this command
            }
            // Check all clauses for this command name
            let clauses: Vec<&crate::ir::types::IRStep> = system
                .steps
                .iter()
                .filter(|s| s.name == event.name)
                .collect();

            let any_enabled = clauses.iter().any(|clause| {
                let Ok(enabled_bool) = harness::try_encode_step_enabled(
                    pool,
                    vctx,
                    entities,
                    systems,
                    clause,
                    deadlock_step,
                ) else {
                    return true;
                };
                model
                    .eval(&enabled_bool, true)
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false)
            });

            if !any_enabled {
                // Collect reasons from ALL disabled clauses.
                let reasons: Vec<String> = clauses
                    .iter()
                    .map(|clause| {
                        diagnose_disabled_event(
                            &model,
                            pool,
                            vctx,
                            entities,
                            systems,
                            clause,
                            deadlock_step,
                        )
                    })
                    .collect();
                // Group by reason, preserving original clause indices.
                let mut groups: Vec<(String, Vec<usize>)> = Vec::new();
                for (i, r) in reasons.iter().enumerate() {
                    if let Some(g) = groups.iter_mut().find(|(gr, _)| gr == r) {
                        g.1.push(i + 1);
                    } else {
                        groups.push((r.clone(), vec![i + 1]));
                    }
                }
                let reason = if groups.len() == 1 {
                    groups.into_iter().next().unwrap().0
                } else {
                    groups
                        .iter()
                        .map(|(r, idxs)| {
                            let labels: Vec<String> =
                                idxs.iter().map(ToString::to_string).collect();
                            format!("clause {}: {r}", labels.join(","))
                        })
                        .collect::<Vec<_>>()
                        .join("; ")
                };
                diagnostics.push(DeadlockEventDiag {
                    system: system.name.clone(),
                    event: event.name.clone(),
                    reason,
                });
            }
        }
    }

    diagnostics
}

/// Determine why a specific event is disabled at a given step.
fn diagnose_disabled_event(
    model: &Model,
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &crate::ir::types::IRStep,
    step: usize,
) -> String {
    use crate::ir::types::{IRAction, IRType, LitVal};

    // Check the event guard first
    let guard_trivial = matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    );
    if !guard_trivial {
        let params = harness::build_step_params(&event.params, step);
        let store_param_types: std::collections::HashMap<String, String> = systems
            .iter()
            .find(|s| {
                s.steps
                    .iter()
                    .any(|st| std::ptr::eq(st, event) || st.name == event.name)
            })
            .map(|s| {
                s.store_params
                    .iter()
                    .map(|p| (p.name.clone(), p.entity_type.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let Ok(guard_val) = harness::try_encode_guard_expr(
            pool,
            vctx,
            &event.guard,
            &params,
            &store_param_types,
            step,
        ) else {
            return "guard encoding failed".to_owned();
        };
        let guard_ok = model
            .eval(&guard_val, true)
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        if !guard_ok {
            return "guard is false".to_owned();
        }
    }

    // Check body action preconditions
    for action in &event.body {
        match action {
            IRAction::Choose {
                entity: ent_name, ..
            } => {
                let n_slots = pool.slots_for(ent_name);
                let mut any_active = false;
                for slot in 0..n_slots {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        let is_active = model
                            .eval(active, true)
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false);
                        if is_active {
                            any_active = true;
                            break;
                        }
                    }
                }
                if !any_active {
                    return format!("no active {ent_name} matching choose filter");
                }
                return format!("no {ent_name} satisfies choose filter");
            }
            IRAction::Create {
                entity: ent_name, ..
            } => {
                let n_slots = pool.slots_for(ent_name);
                let mut any_inactive = false;
                for slot in 0..n_slots {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        let is_active = model
                            .eval(active, true)
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false);
                        if !is_active {
                            any_inactive = true;
                            break;
                        }
                    }
                }
                if !any_inactive {
                    return format!("no inactive slot for {ent_name} (pool full)");
                }
            }
            IRAction::Apply {
                target, transition, ..
            } => {
                // Check if target entity has the transition guard satisfied
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    event.params.iter().find_map(|p| {
                        if p.name == *target {
                            if let IRType::Entity { name } = &p.ty {
                                return entities.iter().find(|e| e.name == *name);
                            }
                        }
                        None
                    })
                });
                if let Some(ent) = resolved_entity {
                    if let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) {
                        let trans_guard_trivial = matches!(
                            &trans.guard,
                            IRExpr::Lit {
                                value: LitVal::Bool { value: true },
                                ..
                            }
                        );
                        if !trans_guard_trivial {
                            // Evaluate the guard in the model for each active slot.
                            let params = harness::build_step_params(&event.params, step);
                            let n_slots = pool.slots_for(&ent.name);
                            let empty_ept: HashMap<String, String> = HashMap::new();
                            let mut any_guard_true = false;
                            for slot in 0..n_slots {
                                if let Some(SmtValue::Bool(active)) =
                                    pool.active_at(&ent.name, slot, step)
                                {
                                    let is_active = model
                                        .eval(active, true)
                                        .and_then(|v| v.as_bool())
                                        .unwrap_or(false);
                                    if !is_active {
                                        continue;
                                    }
                                    let ctx = harness::SlotEncodeCtx {
                                        pool,
                                        vctx,
                                        entity: &ent.name,
                                        slot,
                                        params: params.clone(),
                                        bindings: HashMap::new(),
                                        system_name: "",
                                        entity_param_types: &empty_ept,
                                        store_param_types: &empty_ept,
                                    };
                                    let Ok(guard_val) =
                                        harness::try_encode_slot_expr(&ctx, &trans.guard, step)
                                    else {
                                        continue;
                                    };
                                    let guard_bool = guard_val
                                        .to_bool()
                                        .unwrap_or_else(|_| super::smt::bool_const(true));
                                    if model
                                        .eval(&guard_bool, true)
                                        .and_then(|v| v.as_bool())
                                        .unwrap_or(false)
                                    {
                                        any_guard_true = true;
                                        break;
                                    }
                                }
                            }
                            if !any_guard_true {
                                return format!("{target}.{transition}() guard is false",);
                            }
                        }
                    }
                }
            }
            IRAction::CrossCall {
                system: sys_name,
                command: cmd_name,
                ..
            } => {
                // Check all matching step clauses — command is
                // enabled if ANY clause is enabled.
                let target_enabled =
                    systems
                        .iter()
                        .find(|s| s.name == *sys_name)
                        .is_some_and(|s| {
                            s.steps
                                .iter()
                                .filter(|st| st.name == *cmd_name)
                                .any(|target_step| {
                                    let Ok(enabled_bool) = harness::try_encode_step_enabled(
                                        pool,
                                        vctx,
                                        entities,
                                        systems,
                                        target_step,
                                        step,
                                    ) else {
                                        return false;
                                    };
                                    model
                                        .eval(&enabled_bool, true)
                                        .and_then(|v| v.as_bool())
                                        .unwrap_or(false)
                                })
                        });
                if !target_enabled {
                    return format!("cross-call {sys_name}::{cmd_name} is disabled");
                }
            }
            _ => {}
        }
    }

    "disabled (no specific precondition identified)".to_owned()
}
