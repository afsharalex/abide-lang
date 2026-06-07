//! Scene block verification.
//!
//! Scene blocks are existential witnesses: given initial bindings and a sequence
//! of events, the solver checks whether a satisfying trace exists. The main
//! entry point is `check_scene_block`, which builds the SMT encoding and
//! dispatches to Z3.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use abide_witness::{op, EvidenceEnvelope, WitnessEnvelope};

use super::smt::{self, AbideSolver, Bool, Int, SatResult};

use crate::ir::types::{
    IREntity, IRExpr, IRProgram, IRScene, IRSceneEvent, IRSceneGiven, IRSystem, IRSystemAction,
};

use super::context::VerifyContext;
use super::defenv;
use super::harness::{
    self, create_slot_pool_with_systems, domain_constraints, store_active_cardinality_constraints,
    try_encode_step_with_params,
};
use super::property::{encode_prop_expr_with_ctx, encode_prop_value_with_ctx, PropertyCtx};
use super::scope::{
    collect_crosscall_systems, collect_saw_systems_expr, validate_crosscall_arities,
    VerifyStoreRange,
};
use super::smt::SmtValue;
use super::walkers::{
    collect_event_body_entities, collect_field_refs_in_expr, elapsed_ms, extract_state_from_model,
    extract_witness_value, find_unsupported_scene_expr, scan_event_creates,
};
use super::{
    clamp_timeout_to_deadline, collect_var_refs_in_expr, expand_through_defs, expr_span,
    find_unsupported_in_actions,
};
use super::{VerificationResult, VerifyConfig};

// ── Scene helpers ────────────────────────────────────────────────────

struct SceneOneBindingCtx<'a> {
    pool: &'a harness::SlotPool,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    store_ranges: &'a HashMap<String, (String, usize, usize)>,
    property_store_ranges: &'a HashMap<String, VerifyStoreRange>,
    prior_bindings: &'a HashMap<String, (String, usize)>,
}

struct SceneScopePlan {
    bound: usize,
    some_budget: usize,
    scope: HashMap<String, usize>,
    relevant_entities: Vec<IREntity>,
    relevant_systems: Vec<IRSystem>,
}

struct SceneStores {
    raw: HashMap<String, (String, usize, usize)>,
    property: HashMap<String, VerifyStoreRange>,
}

struct SceneBindings {
    given: HashMap<String, (String, usize)>,
    next_slot: HashMap<String, usize>,
    store_next_slot: HashMap<String, usize>,
}

struct SceneInitCtx<'a> {
    scene: &'a IRScene,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    pool: &'a harness::SlotPool,
    solver: &'a AbideSolver,
    relevant_entities: &'a [IREntity],
    stores: &'a SceneStores,
}

struct EventCard {
    n_instances: usize,
    min_fires: usize,
    has_fire_tracking: bool,
}

struct SceneFiringPlan<'a> {
    resolved_events: Vec<ResolvedSceneEvent<'a>>,
    event_var_names: Vec<String>,
    event_cards: Vec<EventCard>,
    event_instance_ranges: Vec<std::ops::Range<usize>>,
    instances: Vec<FiringInst>,
}

struct SceneGroupPlan {
    inst_group: Vec<usize>,
    inst_group_roots: Vec<usize>,
}

struct SceneScheduleCtx<'a> {
    scene: &'a IRScene,
    solver: &'a AbideSolver,
    relevant_systems: &'a [IRSystem],
}

struct SceneTransitionCtx<'a> {
    scene: &'a IRScene,
    pool: &'a harness::SlotPool,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    solver: &'a AbideSolver,
    relevant_entities: &'a [IREntity],
    relevant_systems: &'a [IRSystem],
    store_ranges: &'a HashMap<String, VerifyStoreRange>,
    given_bindings: &'a HashMap<String, (String, usize)>,
    bound: usize,
}

type SceneCheckResult<T> = Result<T, Box<VerificationResult>>;

/// Collect event indices referenced by ^| (exclusive choice) in ordering expressions.
pub(super) fn collect_xor_event_indices(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    xor_events: &mut HashSet<usize>,
) {
    if let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    {
        if op == "OpXor" {
            for var in collect_ordering_leaf_vars(left) {
                if let Some(&idx) = var_to_idx.get(var) {
                    xor_events.insert(idx);
                }
            }
            for var in collect_ordering_leaf_vars(right) {
                if let Some(&idx) = var_to_idx.get(var) {
                    xor_events.insert(idx);
                }
            }
        }
        collect_xor_event_indices(left, var_to_idx, xor_events);
        collect_xor_event_indices(right, var_to_idx, xor_events);
    }
}

fn scene_solver_result(
    scene: &IRScene,
    result: SatResult,
    elapsed_ms: u64,
    evidence: Option<EvidenceEnvelope>,
) -> VerificationResult {
    match result {
        SatResult::Sat => VerificationResult::ScenePass {
            name: scene.name.clone(),
            time_ms: elapsed_ms,
            evidence,
            span: None,
            file: None,
        },
        SatResult::Unsat => VerificationResult::SceneFail {
            name: scene.name.clone(),
            reason: crate::messages::SCENE_UNSATISFIABLE.to_owned(),
            span: None,
            file: None,
        },
        SatResult::Unknown(reason) => VerificationResult::SceneUnknown {
            name: scene.name.clone(),
            reason: if reason.is_empty() {
                crate::messages::SCENE_UNKNOWN.to_owned()
            } else {
                format!("{}: {reason}", crate::messages::SCENE_UNKNOWN)
            },
            span: None,
            file: None,
        },
    }
}

/// Collect event-level same-step pairs from `OpSameStep` ordering expressions.
pub(super) fn collect_same_step_event_pairs(
    ordering: &[IRExpr],
    var_to_idx: &HashMap<&str, usize>,
    pairs: &mut Vec<(usize, usize)>,
) {
    for expr in ordering {
        collect_same_step_event_pairs_expr(expr, var_to_idx, pairs);
    }
}

pub(super) fn collect_same_step_event_pairs_expr(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    pairs: &mut Vec<(usize, usize)>,
) {
    if let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    {
        if op == "OpSameStep" {
            let left_vars: Vec<usize> = collect_ordering_leaf_vars(left)
                .into_iter()
                .filter_map(|v| var_to_idx.get(v).copied())
                .collect();
            let right_vars: Vec<usize> = collect_ordering_leaf_vars(right)
                .into_iter()
                .filter_map(|v| var_to_idx.get(v).copied())
                .collect();
            for &a in &left_vars {
                for &b in &right_vars {
                    pairs.push((a, b));
                }
            }
        }
        collect_same_step_event_pairs_expr(left, var_to_idx, pairs);
        collect_same_step_event_pairs_expr(right, var_to_idx, pairs);
    }
}

/// Encode scene ordering constraints with multi-instance support.
/// For multi-instance events, `a -> b` means last instance of a < first instance of b.
/// `^|` asserts XOR on fire variables.
pub(super) fn encode_scene_ordering_v2(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
    event_instance_ranges: &[std::ops::Range<usize>],
    instances: &[FiringInst],
    solver: &AbideSolver,
    scene_name: &str,
) -> Result<(), String> {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpSeq" => {
                // a -> b: last instance of a < first instance of b
                if let (Some(l_event), Some(r_event)) = (
                    last_ordering_var(left, var_to_idx),
                    first_ordering_var(right, var_to_idx),
                ) {
                    let l_range = &event_instance_ranges[l_event];
                    let r_range = &event_instance_ranges[r_event];
                    if !l_range.is_empty() && !r_range.is_empty() {
                        let last_l = &instances[l_range.end - 1].step_var;
                        let first_r = &instances[r_range.start].step_var;
                        solver.assert(smt::int_lt(last_l, first_r));
                    }
                } else {
                    let left_vars = collect_ordering_leaf_vars(left);
                    let right_vars = collect_ordering_leaf_vars(right);
                    if left_vars.is_empty() || right_vars.is_empty() {
                        return Err(format!(
                            "scene '{scene_name}': ordering expression references \
                             unknown event variable in `assume` block"
                        ));
                    }
                }
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            "OpSameStep" => {
                // Handled by same-step grouping. Recurse for nested.
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            "OpConc" | "OpUnord" => {
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            "OpXor" => {
                // ^|: exactly one of the two events fires.
                // XOR on their fires variables.
                let left_events: Vec<usize> = collect_ordering_leaf_vars(left)
                    .into_iter()
                    .filter_map(|v| var_to_idx.get(v).copied())
                    .collect();
                let right_events: Vec<usize> = collect_ordering_leaf_vars(right)
                    .into_iter()
                    .filter_map(|v| var_to_idx.get(v).copied())
                    .collect();
                for &a in &left_events {
                    for &b in &right_events {
                        let a_range = &event_instance_ranges[a];
                        let b_range = &event_instance_ranges[b];
                        if a_range.is_empty() {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(a, var_to_idx),
                                0,
                            ));
                        }
                        if b_range.is_empty() {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(b, var_to_idx),
                                0,
                            ));
                        }
                        // ^| requires single-instance events (exactly 1 firing slot).
                        // Multi-instance ({some}, {N>1}) would allow extra firings
                        // that bypass the XOR constraint.
                        if a_range.len() > 1 {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(a, var_to_idx),
                                a_range.len(),
                            ));
                        }
                        if b_range.len() > 1 {
                            return Err(crate::messages::scene_xor_multi_instance(
                                scene_name,
                                &event_var_names_from_idx(b, var_to_idx),
                                b_range.len(),
                            ));
                        }
                        let a_fires =
                            instances[a_range.start].fires_var.as_ref().ok_or_else(|| {
                                crate::messages::scene_xor_no_fire_tracking(
                                    scene_name,
                                    &event_var_names_from_idx(a, var_to_idx),
                                )
                            })?;
                        let b_fires =
                            instances[b_range.start].fires_var.as_ref().ok_or_else(|| {
                                crate::messages::scene_xor_no_fire_tracking(
                                    scene_name,
                                    &event_var_names_from_idx(b, var_to_idx),
                                )
                            })?;
                        // XOR: (a_fires ∧ ¬b_fires) ∨ (¬a_fires ∧ b_fires)
                        let xor = smt::bool_or(&[
                            &smt::bool_and(&[a_fires, &smt::bool_not(b_fires)]),
                            &smt::bool_and(&[&smt::bool_not(a_fires), b_fires]),
                        ]);
                        solver.assert(&xor);
                    }
                }
                // Recurse for nested
                encode_scene_ordering_v2(
                    left,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
                encode_scene_ordering_v2(
                    right,
                    var_to_idx,
                    event_instance_ranges,
                    instances,
                    solver,
                    scene_name,
                )?;
            }
            _ => {}
        },
        IRExpr::Var { .. } => {}
        _ => {}
    }
    Ok(())
}

/// Reverse lookup: event index → variable name
pub(super) fn event_var_names_from_idx(idx: usize, var_to_idx: &HashMap<&str, usize>) -> String {
    var_to_idx
        .iter()
        .find(|(_, &i)| i == idx)
        .map_or_else(|| format!("event_{idx}"), |(name, _)| name.to_string())
}

/// A single firing instance in the scene trace.
pub(super) struct FiringInst {
    event_idx: usize,
    #[allow(dead_code)]
    inst_idx: usize,
    step_var: Int,
    fires_var: Option<Bool>,
}

/// Resolved scene event: validated reference to the scene event and its IR.
///
/// NOTE: Scene `when` blocks invoke commands. For multi-clause commands
/// (multiple steps with the same name but different guards), ALL matching
/// steps are stored. Parameter resolution uses the first step (all steps
/// for a command share the same params, validated by collect.rs). Scene
/// execution encodes a disjunction over all steps so the solver explores
/// every clause.
pub(super) struct ResolvedSceneEvent<'a> {
    scene_event: &'a IRSceneEvent,
    steps: Vec<&'a IRSystemAction>,
}

pub(super) struct SceneEventParamCtx<'a> {
    pool: &'a harness::SlotPool,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    given_bindings: &'a HashMap<String, (String, usize)>,
    store_ranges: &'a HashMap<String, VerifyStoreRange>,
    step: usize,
}

struct SceneEvidenceCtx<'a> {
    solver: &'a AbideSolver,
    pool: &'a harness::SlotPool,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    relevant_entities: &'a [crate::ir::types::IREntity],
    relevant_systems: &'a [crate::ir::types::IRSystem],
    resolved_events: &'a [ResolvedSceneEvent<'a>],
    instances: &'a [FiringInst],
    given_bindings: &'a HashMap<String, (String, usize)>,
    store_ranges: &'a HashMap<String, VerifyStoreRange>,
    bound: usize,
}

/// Build `override_params` for a scene event at a given step.
pub(super) fn build_scene_event_params(
    re: &ResolvedSceneEvent<'_>,
    ctx: &SceneEventParamCtx<'_>,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut override_params: HashMap<String, SmtValue> = HashMap::new();
    // Use the first step for param metadata (all steps share the same
    // params — validated by collect.rs).
    let step_ir = re.steps[0];
    for (param, arg) in step_ir.params.iter().zip(re.scene_event.args.iter()) {
        if let (
            crate::ir::types::IRType::Entity { name: param_entity },
            IRExpr::Var { name: arg_name, .. },
        ) = (&param.ty, arg)
        {
            if let Some((arg_entity, slot)) = ctx.given_bindings.get(arg_name) {
                if arg_entity != param_entity {
                    return Err(format!(
                        "entity type mismatch in scene event arg for {}::{}: \
                         `{arg_name}` is `{arg_entity}` but parameter `{}` expects `{param_entity}`",
                        re.scene_event.system, re.scene_event.event, param.name,
                    ));
                }
                override_params.insert(param.name.clone(), smt::int_val(*slot as i64));
                continue;
            }
        }

        let arg_ctx = PropertyCtx::new().with_store_ranges(ctx.store_ranges.clone());
        let arg_ctx = ctx
            .given_bindings
            .iter()
            .fold(arg_ctx, |ctx, (var, (ent, slot))| {
                ctx.with_binding(var, ent, *slot)
            });
        if let Some(val) =
            encode_scene_direct_choose_arg(ctx.pool, ctx.vctx, ctx.defs, &arg_ctx, arg, ctx.step)
                .map_err(|msg| {
                    format!(
                        "encoding error in scene event arg for {}::{}: {msg}",
                        re.scene_event.system, re.scene_event.event
                    )
                })?
        {
            override_params.insert(param.name.clone(), val);
            continue;
        }
        let (val, constraints) =
            encode_prop_value_with_ctx(ctx.pool, ctx.vctx, ctx.defs, &arg_ctx, arg, ctx.step)
                .map_err(|msg| {
                    format!(
                        "encoding error in scene event arg for {}::{}: {msg}",
                        re.scene_event.system, re.scene_event.event
                    )
                })?;
        if !constraints.is_empty() {
            return Err(format!(
                "scene event args do not yet support choose witness constraints for {}::{}",
                re.scene_event.system, re.scene_event.event
            ));
        }
        override_params.insert(param.name.clone(), val);
    }
    Ok(override_params)
}

fn direct_choose_equality_witness<'a>(var: &str, predicate: &'a IRExpr) -> Option<&'a IRExpr> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = predicate
    else {
        return None;
    };
    if op != "OpEq" {
        return None;
    }
    if matches!(left.as_ref(), IRExpr::Var { name, .. } if name == var) {
        return Some(right);
    }
    if matches!(right.as_ref(), IRExpr::Var { name, .. } if name == var) {
        return Some(left);
    }
    None
}

fn encode_scene_direct_choose_arg(
    pool: &harness::SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    arg: &IRExpr,
    step: usize,
) -> Result<Option<SmtValue>, String> {
    let IRExpr::Choose {
        var,
        predicate: Some(predicate),
        ..
    } = arg
    else {
        return Ok(None);
    };
    let Some(witness_expr) = direct_choose_equality_witness(var, predicate) else {
        return Ok(None);
    };
    let (value, constraints) =
        encode_prop_value_with_ctx(pool, vctx, defs, ctx, witness_expr, step)?;
    if !constraints.is_empty() {
        return Err(
            "direct choose witness expression produced nested witness constraints".to_owned(),
        );
    }
    Ok(Some(value))
}

fn scene_pass_evidence(ctx: &SceneEvidenceCtx<'_>) -> Result<EvidenceEnvelope, String> {
    let model = ctx
        .solver
        .get_model()
        .ok_or_else(|| "solver did not provide a model for scene witness extraction".to_owned())?;
    let mut behavior = op::Behavior::builder();
    for step in 0..=ctx.bound {
        behavior = behavior.state(extract_state_from_model(
            &model,
            ctx.pool,
            ctx.vctx,
            ctx.relevant_entities,
            ctx.relevant_systems,
            step,
        )?);

        if step < ctx.bound {
            let mut transition = op::Transition::builder();
            let mut selected = 0usize;
            for inst in ctx.instances {
                let Some(inst_step) = model
                    .eval(&inst.step_var, true)
                    .and_then(|value| value.as_i64())
                else {
                    continue;
                };
                if inst_step != step as i64 {
                    continue;
                }
                if let Some(fires) = &inst.fires_var {
                    let Some(true) = model.eval(fires, true).and_then(|value| value.as_bool())
                    else {
                        continue;
                    };
                }
                let re = &ctx.resolved_events[inst.event_idx];
                let step_ir = re.steps[0];
                let params = build_scene_event_params(
                    re,
                    &SceneEventParamCtx {
                        pool: ctx.pool,
                        vctx: ctx.vctx,
                        defs: ctx.defs,
                        given_bindings: ctx.given_bindings,
                        store_ranges: ctx.store_ranges,
                        step,
                    },
                )?;
                let step_id = op::AtomicStepId::new(format!(
                    "{step}:{}::{}#{}",
                    re.scene_event.system,
                    re.scene_event.event,
                    inst.inst_idx + 1
                ))
                .map_err(|err| format!("generated scene atomic step id is invalid: {err}"))?;
                let mut atomic = op::AtomicStep::builder(
                    step_id,
                    re.scene_event.system.clone(),
                    re.scene_event.event.clone(),
                )
                .step_name(format!("scene:{}", re.scene_event.var));
                for param in &step_ir.params {
                    if let Some(value) = params.get(&param.name) {
                        let value = extract_witness_value(
                            &model,
                            value,
                            &ctx.vctx.variants,
                            &param.ty,
                        )
                        .map_err(|err| {
                            format!(
                                "failed to extract scene parameter {} for {}::{} at step {step}: {err}",
                                param.name, re.scene_event.system, re.scene_event.event
                            )
                        })?;
                        let binding = op::Binding::new(param.name.clone(), value)
                            .map(|binding| {
                                binding.with_ty_hint(super::walkers::render_ir_type(&param.ty))
                            })
                            .map_err(|err| {
                                format!("generated scene parameter binding is invalid: {err}")
                            })?;
                        atomic = atomic.param(binding);
                    }
                }
                transition = transition.atomic_step(
                    atomic
                        .build()
                        .map_err(|err| format!("scene atomic step extraction failed: {err}"))?,
                );
                selected += 1;
            }
            if selected == 0 {
                transition = transition.observation(
                    op::TransitionObservation::new("stutter", op::WitnessValue::Bool(true))
                        .map_err(|err| {
                            format!("generated scene stutter observation is invalid: {err}")
                        })?,
                );
            }
            behavior = behavior.transition(
                transition
                    .build()
                    .map_err(|err| format!("scene transition extraction failed: {err}"))?,
            );
        }
    }
    let behavior = behavior
        .build()
        .map_err(|err| format!("scene behavior extraction failed: {err}"))?;
    let witness = op::OperationalWitness::counterexample(behavior)
        .map_err(|err| format!("scene witness validation failed: {err}"))?;
    EvidenceEnvelope::witness(
        WitnessEnvelope::operational(witness)
            .map_err(|err| format!("scene witness envelope validation failed: {err}"))?,
    )
    .map_err(|err| format!("scene evidence validation failed: {err}"))
}

/// Collect all event variable names referenced in an ordering expression.
pub(super) fn collect_ordering_leaf_vars(expr: &IRExpr) -> Vec<&str> {
    match expr {
        IRExpr::Var { name, .. } => vec![name.as_str()],
        IRExpr::BinOp { left, right, .. } => {
            let mut vars = collect_ordering_leaf_vars(left);
            vars.extend(collect_ordering_leaf_vars(right));
            vars
        }
        _ => vec![],
    }
}

/// Get the step variable index of the last (rightmost) event in an ordering expr.
/// For `a -> b`, returns index of `b`. For a bare `Var("a")`, returns index of `a`.
pub(super) fn last_ordering_var(expr: &IRExpr, var_to_idx: &HashMap<&str, usize>) -> Option<usize> {
    match expr {
        IRExpr::Var { name, .. } => var_to_idx.get(name.as_str()).copied(),
        IRExpr::BinOp { op, right, .. } if op == "OpSeq" => last_ordering_var(right, var_to_idx),
        IRExpr::BinOp { right, .. } => last_ordering_var(right, var_to_idx),
        _ => None,
    }
}

/// Get the step variable index of the first (leftmost) event in an ordering expr.
/// For `a -> b`, returns index of `a`. For a bare `Var("a")`, returns index of `a`.
pub(super) fn first_ordering_var(
    expr: &IRExpr,
    var_to_idx: &HashMap<&str, usize>,
) -> Option<usize> {
    match expr {
        IRExpr::Var { name, .. } => var_to_idx.get(name.as_str()).copied(),
        IRExpr::BinOp { op, left, .. } if op == "OpSeq" => first_ordering_var(left, var_to_idx),
        IRExpr::BinOp { left, .. } => first_ordering_var(left, var_to_idx),
        _ => None,
    }
}

fn encode_scene_one_binding_uniqueness(
    ctx: SceneOneBindingCtx<'_>,
    given: &IRSceneGiven,
    step: usize,
) -> Result<Bool, String> {
    let pool = ctx.pool;
    let vctx = ctx.vctx;
    let defs = ctx.defs;
    let candidate_slots: Vec<usize> = if let Some(store_name) = &given.store_name {
        let Some((store_entity, start, count)) = ctx.store_ranges.get(store_name) else {
            return Err(format!(
                "unknown store '{store_name}' in given for {}",
                given.var
            ));
        };
        if store_entity != &given.entity {
            return Err(format!(
                "entity type mismatch in given uniqueness for {}: store '{}' holds '{}', not '{}'",
                given.var, store_name, store_entity, given.entity
            ));
        }
        (*start..*start + *count).collect()
    } else {
        (0..pool.slots_for(&given.entity)).collect()
    };

    let base_ctx = PropertyCtx::new()
        .with_store_ranges(ctx.property_store_ranges.clone())
        .with_given_bindings(ctx.prior_bindings);
    let zero = smt::int_lit(0);
    let one = smt::int_lit(1);
    let mut terms = Vec::new();

    for slot in candidate_slots {
        let Some(SmtValue::Bool(active)) = pool.active_at(&given.entity, slot, step) else {
            continue;
        };
        let slot_ctx = base_ctx.with_binding(&given.var, &given.entity, slot);
        let predicate =
            encode_prop_expr_with_ctx(pool, vctx, defs, &slot_ctx, &given.constraint, step)?;
        let matches = smt::bool_and(&[active, &predicate]);
        terms.push(smt::int_ite(&matches, &one, &zero));
    }

    let count = if terms.is_empty() {
        zero
    } else {
        smt::int_add(&terms.iter().collect::<Vec<_>>())
    };
    Ok(smt::int_eq(&count, &one))
}

/// 1. Build scope and pool from scene systems
/// 2. Given: activate one slot per binding, constrain fields at step 0
/// 3. When: encode each event at its step (ordering from assume)
/// 4. Then: assert all then-expressions at the final step
/// 5. SAT → `ScenePass`, UNSAT → `SceneFail`
pub(super) fn check_scene_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    scene: &IRScene,
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> VerificationResult {
    let start = Instant::now();
    let scope = match build_scene_scope(ir, scene) {
        Ok(scope) => scope,
        Err(result) => return *result,
    };
    let pool = create_slot_pool_with_systems(
        &scope.relevant_entities,
        &scope.scope,
        scope.bound,
        &scope.relevant_systems,
    );
    let solver = match scene_solver(scene, config, deadline) {
        Ok(solver) => solver,
        Err(result) => return *result,
    };
    assert_scene_domain_constraints(&pool, vctx, &scope.relevant_entities, &solver);

    let stores = scene_store_ranges(scene);
    let mut bindings = match encode_scene_initial_state(&SceneInitCtx {
        scene,
        vctx,
        defs,
        pool: &pool,
        solver: &solver,
        relevant_entities: &scope.relevant_entities,
        stores: &stores,
    }) {
        Ok(bindings) => bindings,
        Err(result) => return *result,
    };

    let plan = match build_scene_firing_plan(
        scene,
        defs,
        &scope.relevant_systems,
        &mut bindings,
        scope.some_budget,
    ) {
        Ok(plan) => plan,
        Err(result) => return *result,
    };
    debug_assert_eq!(
        plan.instances.len().max(1),
        scope.bound,
        "instance count should match pre-computed bound"
    );

    let groups = match assert_scene_schedule_constraints(
        &SceneScheduleCtx {
            scene,
            solver: &solver,
            relevant_systems: &scope.relevant_systems,
        },
        &plan,
        scope.bound,
    ) {
        Ok(groups) => groups,
        Err(result) => return *result,
    };

    let transition_ctx = SceneTransitionCtx {
        scene,
        pool: &pool,
        vctx,
        defs,
        solver: &solver,
        relevant_entities: &scope.relevant_entities,
        relevant_systems: &scope.relevant_systems,
        store_ranges: &stores.property,
        given_bindings: &bindings.given,
        bound: scope.bound,
    };
    if let Err(result) = assert_scene_step_transitions(&transition_ctx, &plan, &groups) {
        return *result;
    }

    assert_scene_result_activation(scene, &pool, &solver, &bindings.given, &plan, scope.bound);
    let then_ctx = match assert_scene_then_assertions(&transition_ctx) {
        Ok(ctx) => ctx,
        Err(result) => return *result,
    };

    match solver.check() {
        result @ SatResult::Sat => {
            let evidence = scene_pass_evidence(&SceneEvidenceCtx {
                solver: &solver,
                pool: &pool,
                vctx,
                defs,
                relevant_entities: &scope.relevant_entities,
                relevant_systems: &scope.relevant_systems,
                resolved_events: &plan.resolved_events,
                instances: &plan.instances,
                given_bindings: &bindings.given,
                store_ranges: &then_ctx.store_ranges,
                bound: scope.bound,
            })
            .ok();
            let elapsed = elapsed_ms(&start);
            scene_solver_result(scene, result, elapsed, evidence)
        }
        result @ (SatResult::Unsat | SatResult::Unknown(_)) => {
            let elapsed = elapsed_ms(&start);
            scene_solver_result(scene, result, elapsed, None)
        }
    }
}

fn scene_fail(
    scene: &IRScene,
    reason: String,
    span: Option<crate::span::Span>,
) -> Box<VerificationResult> {
    Box::new(VerificationResult::SceneFail {
        name: scene.name.clone(),
        reason,
        span,
        file: None,
    })
}

fn scene_event_bound(scene: &IRScene) -> (usize, usize) {
    let some_budget = scene.events.len().max(2);
    let total = scene.events.iter().fold(0usize, |acc, event| {
        acc + match &event.cardinality {
            crate::ir::types::Cardinality::Named(cardinality) => match cardinality.as_str() {
                "one" | "lone" => 1,
                "no" => 0,
                "some" => some_budget,
                _ => 1,
            },
            crate::ir::types::Cardinality::Exact { exactly } => *exactly as usize,
        }
    });
    (total.max(1), some_budget)
}

fn build_scene_scope(ir: &IRProgram, scene: &IRScene) -> SceneCheckResult<SceneScopePlan> {
    let (bound, some_budget) = scene_event_bound(scene);
    let mut scope = initial_scene_scope(scene);
    let mut system_names = scene_system_names(scene);
    expand_scene_system_scope(ir, scene, bound, &mut scope, &mut system_names);
    if scope.is_empty() {
        return Err(scene_fail(
            scene,
            crate::messages::SCENE_EMPTY_SCOPE.to_owned(),
            None,
        ));
    }
    let relevant_entities = ir
        .entities
        .iter()
        .filter(|entity| scope.contains_key(&entity.name))
        .cloned()
        .collect();
    let relevant_systems = ir
        .systems
        .iter()
        .filter(|system| system_names.contains(&system.name))
        .cloned()
        .collect();
    Ok(SceneScopePlan {
        bound,
        some_budget,
        scope,
        relevant_entities,
        relevant_systems,
    })
}

fn initial_scene_scope(scene: &IRScene) -> HashMap<String, usize> {
    let mut scope = HashMap::new();
    for store in &scene.stores {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let hi = store.hi.max(0) as usize;
        let existing = scope.get(&store.entity_type).copied().unwrap_or(0);
        scope.insert(store.entity_type.clone(), existing + hi);
    }
    for given in &scene.givens {
        *scope.entry(given.entity.clone()).or_insert(0) += 1;
    }
    scope
}

fn scene_system_names(scene: &IRScene) -> Vec<String> {
    let mut system_names = scene.systems.clone();
    for scene_event in &scene.events {
        if !system_names.contains(&scene_event.system) {
            system_names.push(scene_event.system.clone());
        }
    }
    for expr in scene
        .ordering
        .iter()
        .chain(scene.assertions.iter())
        .chain(scene.given_constraints.iter())
    {
        collect_saw_systems_expr(expr, &mut system_names);
    }
    system_names
}

fn expand_scene_system_scope(
    ir: &IRProgram,
    scene: &IRScene,
    bound: usize,
    scope: &mut HashMap<String, usize>,
    system_names: &mut Vec<String>,
) {
    let default_slots = bound.max(1);
    let mut systems_to_scan = system_names.clone();
    let mut scanned = HashSet::new();
    while let Some(sys_name) = systems_to_scan.pop() {
        if !scanned.insert(sys_name.clone()) {
            continue;
        }
        let Some(sys) = ir.systems.iter().find(|system| system.name == sys_name) else {
            continue;
        };
        if !system_names.contains(&sys.name) {
            system_names.push(sys.name.clone());
        }
        for event in &sys.actions {
            collect_crosscall_systems(&event.body, &mut systems_to_scan);
        }
        for binding in &sys.let_bindings {
            if !systems_to_scan.contains(&binding.system_type) {
                systems_to_scan.push(binding.system_type.clone());
            }
        }
        for ent_name in &sys.entities {
            let given_count = scene
                .givens
                .iter()
                .filter(|given| given.entity == *ent_name)
                .count();
            let needed = given_count + default_slots;
            let entry = scope.entry(ent_name.clone()).or_insert(0);
            *entry = (*entry).max(needed);
        }
    }
}

fn scene_solver(
    scene: &IRScene,
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> SceneCheckResult<AbideSolver> {
    let solver = AbideSolver::new();
    let Some(timeout_ms) = clamp_timeout_to_deadline(config.bmc_timeout_ms, deadline) else {
        return Err(Box::new(VerificationResult::Unprovable {
            name: scene.name.clone(),
            hint: super::verification_timeout_hint(config),
            span: scene.span,
            file: scene.file.clone(),
        }));
    };
    if timeout_ms > 0 {
        solver.set_timeout(timeout_ms);
    }
    Ok(solver)
}

fn assert_scene_domain_constraints(
    pool: &harness::SlotPool,
    vctx: &VerifyContext,
    relevant_entities: &[IREntity],
    solver: &AbideSolver,
) {
    for constraint in domain_constraints(pool, vctx, relevant_entities) {
        solver.assert(&constraint);
    }
}

fn scene_store_ranges(scene: &IRScene) -> SceneStores {
    let raw = raw_scene_store_ranges(scene);
    let store_lowers: HashMap<_, _> = scene
        .stores
        .iter()
        .map(|store| {
            let min_active = usize::try_from(store.lo.max(0)).unwrap_or(0);
            (store.name.as_str(), min_active)
        })
        .collect();
    let property = raw
        .iter()
        .map(|(store_name, (entity_type, start_slot, slot_count))| {
            let min_active = store_lowers
                .get(store_name.as_str())
                .copied()
                .unwrap_or(0)
                .min(*slot_count);
            (
                store_name.clone(),
                VerifyStoreRange {
                    entity_type: entity_type.clone(),
                    start_slot: *start_slot,
                    min_active,
                    slot_count: *slot_count,
                },
            )
        })
        .collect();
    SceneStores { raw, property }
}

fn raw_scene_store_ranges(scene: &IRScene) -> HashMap<String, (String, usize, usize)> {
    let mut ranges = HashMap::new();
    let mut running: HashMap<String, usize> = HashMap::new();
    for store in &scene.stores {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let count = store.hi.max(0) as usize;
        let start = running.get(&store.entity_type).copied().unwrap_or(0);
        ranges.insert(
            store.name.clone(),
            (store.entity_type.clone(), start, count),
        );
        running.insert(store.entity_type.clone(), start + count);
    }
    ranges
}

fn encode_scene_initial_state(ctx: &SceneInitCtx<'_>) -> SceneCheckResult<SceneBindings> {
    validate_scene_givens(ctx.scene, ctx.defs)?;
    let mut bindings = SceneBindings {
        given: HashMap::new(),
        next_slot: HashMap::new(),
        store_next_slot: HashMap::new(),
    };
    for given in &ctx.scene.givens {
        encode_single_scene_given(ctx, given, &mut bindings)?;
    }
    encode_scene_activations(ctx, &mut bindings)?;
    encode_scene_given_constraints(ctx, &bindings.given)?;
    constrain_scene_initial_activity(ctx, &bindings.given);
    for constraint in store_active_cardinality_constraints(ctx.pool, &ctx.stores.property) {
        ctx.solver.assert(&constraint);
    }
    Ok(bindings)
}

fn validate_scene_givens(scene: &IRScene, defs: &defenv::DefEnv) -> SceneCheckResult<()> {
    for given in &scene.givens {
        let expanded = expand_through_defs(&given.constraint, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return Err(scene_fail(
                scene,
                format!(
                    "unsupported expression kind in scene given for {}: {kind}",
                    given.var
                ),
                None,
            ));
        }
    }
    Ok(())
}

fn encode_single_scene_given(
    ctx: &SceneInitCtx<'_>,
    given: &IRSceneGiven,
    bindings: &mut SceneBindings,
) -> SceneCheckResult<()> {
    let slot = allocate_scene_given_slot(ctx.scene, given, ctx.stores, bindings)?;
    if let Some(SmtValue::Bool(active)) = ctx.pool.active_at(&given.entity, slot, 0) {
        ctx.solver.assert(active);
    }
    assert_scene_given_constraint(ctx, given, slot)?;
    assert_scene_given_uniqueness(ctx, given, &bindings.given)?;
    apply_scene_given_defaults(ctx, given, slot)?;
    bindings
        .given
        .insert(given.var.clone(), (given.entity.clone(), slot));
    Ok(())
}

fn allocate_scene_given_slot(
    scene: &IRScene,
    given: &IRSceneGiven,
    stores: &SceneStores,
    bindings: &mut SceneBindings,
) -> SceneCheckResult<usize> {
    if let Some(store_name) = &given.store_name {
        allocate_store_scene_slot(
            scene,
            given,
            store_name,
            stores,
            &mut bindings.store_next_slot,
        )
    } else {
        let slot = bindings.next_slot.entry(given.entity.clone()).or_insert(0);
        let current = *slot;
        *slot += 1;
        Ok(current)
    }
}

fn allocate_store_scene_slot(
    scene: &IRScene,
    given: &IRSceneGiven,
    store_name: &str,
    stores: &SceneStores,
    store_next_slot: &mut HashMap<String, usize>,
) -> SceneCheckResult<usize> {
    let Some((store_entity_type, start, count)) = stores.raw.get(store_name) else {
        return Err(scene_fail(
            scene,
            format!("unknown store '{}' in given for {}", store_name, given.var),
            None,
        ));
    };
    if *store_entity_type != given.entity {
        return Err(scene_fail(
            scene,
            format!(
                "entity type mismatch: `let {} = one {} in {}` but store '{}' \
                 holds `{}`, not `{}`",
                given.var, given.entity, store_name, store_name, store_entity_type, given.entity,
            ),
            None,
        ));
    }
    let next = store_next_slot
        .entry(store_name.to_owned())
        .or_insert(*start);
    if *next >= start + count {
        return Err(scene_fail(
            scene,
            format!(
                "store '{}' is full: allocated {} of {} slots",
                store_name,
                *next - start,
                count
            ),
            None,
        ));
    }
    let slot = *next;
    *next += 1;
    Ok(slot)
}

fn assert_scene_given_constraint(
    ctx: &SceneInitCtx<'_>,
    given: &IRSceneGiven,
    slot: usize,
) -> SceneCheckResult<()> {
    let given_ctx = PropertyCtx::new()
        .with_store_ranges(ctx.stores.property.clone())
        .with_binding(&given.var, &given.entity, slot);
    match encode_prop_expr_with_ctx(
        ctx.pool,
        ctx.vctx,
        ctx.defs,
        &given_ctx,
        &given.constraint,
        0,
    ) {
        Ok(constraint) => {
            ctx.solver.assert(&constraint);
            Ok(())
        }
        Err(msg) => Err(scene_fail(
            ctx.scene,
            format!(
                "encoding error in given constraint for {}: {msg}",
                given.var
            ),
            None,
        )),
    }
}

fn assert_scene_given_uniqueness(
    ctx: &SceneInitCtx<'_>,
    given: &IRSceneGiven,
    prior_bindings: &HashMap<String, (String, usize)>,
) -> SceneCheckResult<()> {
    let uniqueness = encode_scene_one_binding_uniqueness(
        SceneOneBindingCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            defs: ctx.defs,
            store_ranges: &ctx.stores.raw,
            property_store_ranges: &ctx.stores.property,
            prior_bindings,
        },
        given,
        0,
    )
    .map_err(|msg| {
        scene_fail(
            ctx.scene,
            format!(
                "encoding error in given uniqueness for {}: {msg}",
                given.var
            ),
            None,
        )
    })?;
    ctx.solver.assert(&uniqueness);
    Ok(())
}

fn apply_scene_given_defaults(
    ctx: &SceneInitCtx<'_>,
    given: &IRSceneGiven,
    slot: usize,
) -> SceneCheckResult<()> {
    let constrained_fields = scene_given_constrained_fields(ctx.scene, ctx.defs, given);
    let Some(entity_ir) = ctx
        .relevant_entities
        .iter()
        .find(|entity| entity.name == given.entity)
    else {
        return Ok(());
    };
    for field in &entity_ir.fields {
        if constrained_fields.contains(field.name.as_str()) {
            continue;
        }
        if let Some(default_expr) = &field.default {
            assert_scene_default_field(ctx, given, slot, &field.name, default_expr)?;
        }
    }
    Ok(())
}

fn scene_given_constrained_fields(
    scene: &IRScene,
    defs: &defenv::DefEnv,
    given: &IRSceneGiven,
) -> HashSet<String> {
    let expanded_constraint = expand_through_defs(&given.constraint, defs);
    let mut constrained_fields = HashSet::new();
    collect_field_refs_in_expr(&expanded_constraint, &given.var, &mut constrained_fields);
    for given_constraint in &scene.given_constraints {
        let expanded = expand_through_defs(given_constraint, defs);
        collect_field_refs_in_expr(&expanded, &given.var, &mut constrained_fields);
    }
    constrained_fields
}

fn assert_scene_default_field(
    ctx: &SceneInitCtx<'_>,
    given: &IRSceneGiven,
    slot: usize,
    field_name: &str,
    default_expr: &IRExpr,
) -> SceneCheckResult<()> {
    let empty_ept: HashMap<String, String> = HashMap::new();
    let default_ctx = harness::SlotEncodeCtx {
        pool: ctx.pool,
        vctx: ctx.vctx,
        entity: &given.entity,
        slot,
        params: HashMap::new(),
        bindings: HashMap::new(),
        system_name: "",
        entity_param_types: &empty_ept,
        store_param_types: &empty_ept,
    };
    let val = harness::try_encode_slot_expr(&default_ctx, default_expr, 0).map_err(|reason| {
        scene_fail(
            ctx.scene,
            format!("scene default field encoding failed: {reason}"),
            None,
        )
    })?;
    if let Some(field_var) = ctx.pool.field_at(&given.entity, slot, field_name, 0) {
        assert_scene_value_eq(ctx.solver, &val, field_var);
    }
    Ok(())
}

fn assert_scene_value_eq(solver: &AbideSolver, value: &SmtValue, field_var: &SmtValue) {
    match (value, field_var) {
        (SmtValue::Int(v), SmtValue::Int(f)) => solver.assert(smt::int_eq(f, v)),
        (SmtValue::Bool(v), SmtValue::Bool(f)) => solver.assert(smt::bool_eq(f, v)),
        (SmtValue::Real(v), SmtValue::Real(f)) => solver.assert(smt::real_eq(f, v)),
        _ => {}
    }
}

fn encode_scene_activations(
    ctx: &SceneInitCtx<'_>,
    bindings: &mut SceneBindings,
) -> SceneCheckResult<()> {
    for activation in &ctx.scene.activations {
        let Some((entity_type, start, count)) = ctx.stores.raw.get(&activation.store_name) else {
            return Err(scene_fail(
                ctx.scene,
                format!("unknown store '{}'", activation.store_name),
                None,
            ));
        };
        let next = bindings
            .store_next_slot
            .entry(activation.store_name.clone())
            .or_insert(*start);
        for inst_name in &activation.instances {
            let slot =
                allocate_activation_slot(ctx.scene, &activation.store_name, *start, *count, next)?;
            if let Some(SmtValue::Bool(active)) = ctx.pool.active_at(entity_type, slot, 0) {
                ctx.solver.assert(active);
            }
            bindings
                .given
                .insert(inst_name.clone(), (entity_type.clone(), slot));
        }
    }
    Ok(())
}

fn allocate_activation_slot(
    scene: &IRScene,
    store_name: &str,
    start: usize,
    count: usize,
    next: &mut usize,
) -> SceneCheckResult<usize> {
    if *next >= start + count {
        return Err(scene_fail(
            scene,
            format!(
                "store '{}' is full: allocated {} of {} slots",
                store_name,
                *next - start,
                count
            ),
            None,
        ));
    }
    let slot = *next;
    *next += 1;
    Ok(slot)
}

fn encode_scene_given_constraints(
    ctx: &SceneInitCtx<'_>,
    given_bindings: &HashMap<String, (String, usize)>,
) -> SceneCheckResult<()> {
    for constraint in &ctx.scene.given_constraints {
        let expanded = expand_through_defs(constraint, ctx.defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return Err(scene_fail(
                ctx.scene,
                format!("unsupported expression kind in scene given constraint: {kind}"),
                expr_span(constraint),
            ));
        }
        let prop_ctx = PropertyCtx::new()
            .with_store_ranges(ctx.stores.property.clone())
            .with_given_bindings(given_bindings);
        match encode_prop_expr_with_ctx(ctx.pool, ctx.vctx, ctx.defs, &prop_ctx, constraint, 0) {
            Ok(encoded) => ctx.solver.assert(&encoded),
            Err(msg) => {
                return Err(scene_fail(
                    ctx.scene,
                    format!("encoding error in given constraint: {msg}"),
                    expr_span(constraint),
                ));
            }
        }
    }
    Ok(())
}

fn constrain_scene_initial_activity(
    ctx: &SceneInitCtx<'_>,
    given_bindings: &HashMap<String, (String, usize)>,
) {
    let activated_slots: HashSet<(String, usize)> = given_bindings
        .values()
        .map(|(entity, slot)| (entity.clone(), *slot))
        .collect();
    let store_slots: HashSet<(String, usize)> = ctx
        .stores
        .raw
        .values()
        .flat_map(|(entity, start, count)| {
            (*start..*start + *count).map(|slot| (entity.clone(), slot))
        })
        .collect();
    for entity in ctx.relevant_entities {
        for slot in 0..ctx.pool.slots_for(&entity.name) {
            if activated_slots.contains(&(entity.name.clone(), slot)) {
                continue;
            }
            if store_slots.contains(&(entity.name.clone(), slot)) {
                continue;
            }
            if let Some(SmtValue::Bool(active)) = ctx.pool.active_at(&entity.name, slot, 0) {
                ctx.solver.assert(smt::bool_not(active));
            }
        }
    }
}

fn build_scene_firing_plan<'a>(
    scene: &'a IRScene,
    defs: &defenv::DefEnv,
    relevant_systems: &'a [IRSystem],
    bindings: &mut SceneBindings,
    some_budget: usize,
) -> SceneCheckResult<SceneFiringPlan<'a>> {
    validate_scene_assertions(scene, defs)?;
    let referenced_vars = referenced_scene_event_vars(scene);
    let resolved_events = resolve_scene_events(scene, defs, relevant_systems)?;
    bind_scene_result_vars(
        scene,
        &resolved_events,
        relevant_systems,
        &referenced_vars,
        &mut bindings.next_slot,
        &mut bindings.given,
    )?;
    build_scene_firing_instances(scene, resolved_events, some_budget)
}

fn validate_scene_assertions(scene: &IRScene, defs: &defenv::DefEnv) -> SceneCheckResult<()> {
    for assertion in &scene.assertions {
        let expanded = expand_through_defs(assertion, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return Err(scene_fail(
                scene,
                format!("unsupported expression kind in scene then assertion: {kind}"),
                expr_span(assertion),
            ));
        }
    }
    Ok(())
}

fn referenced_scene_event_vars(scene: &IRScene) -> HashSet<String> {
    let mut refs = HashSet::new();
    for event in &scene.events {
        for arg in &event.args {
            collect_var_refs_in_expr(arg, &mut refs);
        }
    }
    refs
}

fn resolve_scene_events<'a>(
    scene: &'a IRScene,
    defs: &defenv::DefEnv,
    relevant_systems: &'a [IRSystem],
) -> SceneCheckResult<Vec<ResolvedSceneEvent<'a>>> {
    let mut resolved = Vec::new();
    for scene_event in &scene.events {
        let Some(system) = relevant_systems
            .iter()
            .find(|system| system.name == scene_event.system)
        else {
            return Err(scene_fail(
                scene,
                format!(
                    "system {} not found for event {}",
                    scene_event.system, scene_event.event
                ),
                None,
            ));
        };
        let steps = resolve_scene_event_steps(scene, defs, relevant_systems, scene_event, system)?;
        resolved.push(ResolvedSceneEvent { scene_event, steps });
    }
    Ok(resolved)
}

fn resolve_scene_event_steps<'a>(
    scene: &IRScene,
    defs: &defenv::DefEnv,
    relevant_systems: &'a [IRSystem],
    scene_event: &IRSceneEvent,
    system: &'a IRSystem,
) -> SceneCheckResult<Vec<&'a IRSystemAction>> {
    let matching_steps: Vec<_> = system
        .actions
        .iter()
        .filter(|step| step.name == scene_event.event)
        .collect();
    if matching_steps.is_empty() {
        return Err(scene_fail(
            scene,
            format!(
                "event {} not found in system {}",
                scene_event.event, scene_event.system
            ),
            None,
        ));
    }
    validate_scene_event_arity(scene, scene_event, matching_steps[0])?;
    validate_scene_event_args(scene, defs, scene_event)?;
    validate_scene_event_steps(scene, relevant_systems, scene_event, &matching_steps)?;
    Ok(matching_steps)
}

fn validate_scene_event_arity(
    scene: &IRScene,
    scene_event: &IRSceneEvent,
    first_step: &IRSystemAction,
) -> SceneCheckResult<()> {
    if scene_event.args.len() == first_step.params.len() {
        return Ok(());
    }
    Err(scene_fail(
        scene,
        format!(
            "arity mismatch: scene provides {} args for {}::{} but event expects {} params",
            scene_event.args.len(),
            scene_event.system,
            scene_event.event,
            first_step.params.len()
        ),
        None,
    ))
}

fn validate_scene_event_args(
    scene: &IRScene,
    defs: &defenv::DefEnv,
    scene_event: &IRSceneEvent,
) -> SceneCheckResult<()> {
    for arg in &scene_event.args {
        let expanded = expand_through_defs(arg, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return Err(scene_fail(
                scene,
                format!(
                    "unsupported expression kind in scene event arg for {}::{}: {kind}",
                    scene_event.system, scene_event.event
                ),
                None,
            ));
        }
    }
    Ok(())
}

fn validate_scene_event_steps(
    scene: &IRScene,
    relevant_systems: &[IRSystem],
    scene_event: &IRSceneEvent,
    steps: &[&IRSystemAction],
) -> SceneCheckResult<()> {
    for step in steps {
        if let Err(reason) = validate_crosscall_arities(&step.body, relevant_systems, 0) {
            return Err(scene_fail(scene, reason, None));
        }
        if let Some(kind) = find_unsupported_in_actions(&step.body) {
            return Err(scene_fail(
                scene,
                format!(
                    "unsupported action in scene event {}::{}: {kind}",
                    scene_event.system, scene_event.event
                ),
                None,
            ));
        }
    }
    Ok(())
}

fn bind_scene_result_vars(
    scene: &IRScene,
    resolved_events: &[ResolvedSceneEvent<'_>],
    relevant_systems: &[IRSystem],
    referenced_vars: &HashSet<String>,
    next_slot: &mut HashMap<String, usize>,
    given_bindings: &mut HashMap<String, (String, usize)>,
) -> SceneCheckResult<()> {
    for event in resolved_events {
        if !referenced_vars.contains(&event.scene_event.var) {
            continue;
        }
        if let Some(entity) = scene_result_entity(scene, event, relevant_systems)? {
            let slot = next_slot.entry(entity.clone()).or_insert(0);
            let allocated_slot = *slot;
            *slot += 1;
            given_bindings.insert(event.scene_event.var.clone(), (entity, allocated_slot));
        }
    }
    Ok(())
}

fn scene_result_entity(
    scene: &IRScene,
    event: &ResolvedSceneEvent<'_>,
    relevant_systems: &[IRSystem],
) -> SceneCheckResult<Option<String>> {
    let per_step_creates: Vec<Vec<String>> = event
        .steps
        .iter()
        .map(|step| scan_event_creates(&step.body, relevant_systems))
        .collect();
    let non_empty: Vec<&Vec<String>> = per_step_creates
        .iter()
        .filter(|creates| !creates.is_empty())
        .collect();
    if non_empty.is_empty() {
        return Ok(None);
    }
    if non_empty.len() != per_step_creates.len() && per_step_creates.len() > 1 {
        return Err(scene_fail(
            scene,
            format!(
                "multi-clause command {}::{} creates an entity in some steps \
                 but not others; scene result variable `{}` cannot be bound \
                 consistently (all implementing steps must create, or none)",
                event.scene_event.system, event.scene_event.event, event.scene_event.var,
            ),
            None,
        ));
    }
    validate_scene_result_entity_agreement(scene, event, &non_empty)?;
    Ok(Some(non_empty[0][0].clone()))
}

fn validate_scene_result_entity_agreement(
    scene: &IRScene,
    event: &ResolvedSceneEvent<'_>,
    creates: &[&Vec<String>],
) -> SceneCheckResult<()> {
    let first_entity = &creates[0][0];
    for other in &creates[1..] {
        if other[0] != *first_entity {
            return Err(scene_fail(
                scene,
                format!(
                    "multi-clause command {}::{} creates different entity types \
                     across steps (`{}` vs `{}`); scene result variable `{}` \
                     cannot be bound consistently",
                    event.scene_event.system,
                    event.scene_event.event,
                    first_entity,
                    other[0],
                    event.scene_event.var,
                ),
                None,
            ));
        }
    }
    Ok(())
}

fn build_scene_firing_instances<'a>(
    scene: &'a IRScene,
    resolved_events: Vec<ResolvedSceneEvent<'a>>,
    some_budget: usize,
) -> SceneCheckResult<SceneFiringPlan<'a>> {
    let event_var_names: Vec<String> = scene.events.iter().map(|event| event.var.clone()).collect();
    let var_to_idx = scene_var_to_idx(&event_var_names);
    let mut xor_events = HashSet::new();
    for ordering_expr in &scene.ordering {
        collect_xor_event_indices(ordering_expr, &var_to_idx, &mut xor_events);
    }
    let event_cards = scene_event_cards(scene, &resolved_events, &xor_events, some_budget)?;
    let (instances, event_instance_ranges) = scene_firing_instances(&event_var_names, &event_cards);
    Ok(SceneFiringPlan {
        resolved_events,
        event_var_names,
        event_cards,
        event_instance_ranges,
        instances,
    })
}

fn scene_var_to_idx(event_var_names: &[String]) -> HashMap<&str, usize> {
    event_var_names
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect()
}

fn scene_event_cards(
    scene: &IRScene,
    resolved_events: &[ResolvedSceneEvent<'_>],
    xor_events: &HashSet<usize>,
    some_budget: usize,
) -> SceneCheckResult<Vec<EventCard>> {
    resolved_events
        .iter()
        .enumerate()
        .map(|(index, event)| {
            scene_event_card(scene, event, xor_events.contains(&index), some_budget)
        })
        .collect()
}

fn scene_event_card(
    scene: &IRScene,
    event: &ResolvedSceneEvent<'_>,
    is_xor: bool,
    some_budget: usize,
) -> SceneCheckResult<EventCard> {
    use crate::ir::types::Cardinality;

    match &event.scene_event.cardinality {
        Cardinality::Named(cardinality) => {
            named_scene_event_card(scene, event, cardinality, is_xor, some_budget)
        }
        Cardinality::Exact { exactly } => exact_scene_event_card(scene, event, *exactly, is_xor),
    }
}

fn named_scene_event_card(
    scene: &IRScene,
    event: &ResolvedSceneEvent<'_>,
    cardinality: &str,
    is_xor: bool,
    some_budget: usize,
) -> SceneCheckResult<EventCard> {
    match cardinality {
        "one" if is_xor => Ok(EventCard {
            n_instances: 1,
            min_fires: 0,
            has_fire_tracking: true,
        }),
        "one" => Ok(EventCard {
            n_instances: 1,
            min_fires: 1,
            has_fire_tracking: false,
        }),
        "lone" => Ok(EventCard {
            n_instances: 1,
            min_fires: 0,
            has_fire_tracking: true,
        }),
        "no" => Ok(EventCard {
            n_instances: 0,
            min_fires: 0,
            has_fire_tracking: false,
        }),
        "some" => Ok(EventCard {
            n_instances: some_budget,
            min_fires: 1,
            has_fire_tracking: true,
        }),
        other => Err(scene_fail(
            scene,
            format!(
                "unsupported cardinality '{other}' for scene event {}::{}",
                event.scene_event.system, event.scene_event.event
            ),
            None,
        )),
    }
}

fn exact_scene_event_card(
    scene: &IRScene,
    event: &ResolvedSceneEvent<'_>,
    exactly: i64,
    is_xor: bool,
) -> SceneCheckResult<EventCard> {
    let n = exactly as usize;
    if is_xor && n > 1 {
        return Err(scene_fail(
            scene,
            format!(
                "event '{}' has cardinality {{{n}}} but appears in `^|`; \
                 exclusive choice requires {{lone}} cardinality",
                event.scene_event.var
            ),
            None,
        ));
    }
    Ok(EventCard {
        n_instances: n,
        min_fires: if is_xor && n == 1 { 0 } else { n },
        has_fire_tracking: is_xor,
    })
}

fn scene_firing_instances(
    event_var_names: &[String],
    event_cards: &[EventCard],
) -> (Vec<FiringInst>, Vec<std::ops::Range<usize>>) {
    let mut instances = Vec::new();
    let mut ranges = Vec::new();
    for (event_idx, card) in event_cards.iter().enumerate() {
        let start = instances.len();
        for inst_idx in 0..card.n_instances {
            instances.push(FiringInst {
                event_idx,
                inst_idx,
                step_var: scene_step_var(&event_var_names[event_idx], card.n_instances, inst_idx),
                fires_var: card.has_fire_tracking.then(|| {
                    smt::bool_named(&format!(
                        "scene_fires_{}_{inst_idx}",
                        event_var_names[event_idx]
                    ))
                }),
            });
        }
        ranges.push(start..instances.len());
    }
    (instances, ranges)
}

fn scene_step_var(var_name: &str, n_instances: usize, inst_idx: usize) -> Int {
    if n_instances == 1 {
        smt::int_named(&format!("scene_step_{var_name}"))
    } else {
        smt::int_named(&format!("scene_step_{var_name}_{inst_idx}"))
    }
}

fn assert_scene_schedule_constraints(
    ctx: &SceneScheduleCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    bound: usize,
) -> SceneCheckResult<SceneGroupPlan> {
    assert_scene_instance_bounds(
        ctx.solver,
        &plan.instances,
        &plan.event_instance_ranges,
        bound,
    );
    assert_scene_fire_constraints(ctx.solver, plan);
    let mut group_parent: Vec<usize> = (0..plan.instances.len()).collect();
    assert_scene_same_step_groups(ctx, plan, &mut group_parent)?;
    validate_scene_same_step_conflicts(ctx, plan, &mut group_parent)?;
    let groups = scene_group_plan(plan.instances.len(), &mut group_parent);
    assert_scene_instance_distinctness(ctx.solver, plan, &groups);
    assert_scene_ordering_constraints(ctx, plan)?;
    Ok(groups)
}

fn assert_scene_instance_bounds(
    solver: &AbideSolver,
    instances: &[FiringInst],
    ranges: &[std::ops::Range<usize>],
    bound: usize,
) {
    for inst in instances {
        solver.assert(smt::int_ge(&inst.step_var, &smt::int_lit(0)));
        solver.assert(smt::int_lt(&inst.step_var, &smt::int_lit(bound as i64)));
    }
    for range in ranges {
        if range.len() > 1 {
            for index in range.start..(range.end - 1) {
                solver.assert(smt::int_lt(
                    &instances[index].step_var,
                    &instances[index + 1].step_var,
                ));
            }
        }
    }
}

fn assert_scene_fire_constraints(solver: &AbideSolver, plan: &SceneFiringPlan<'_>) {
    for (event_idx, card) in plan.event_cards.iter().enumerate() {
        if !card.has_fire_tracking || card.min_fires == 0 {
            continue;
        }
        let range = &plan.event_instance_ranges[event_idx];
        let fire_vars: Vec<&Bool> = plan.instances[range.clone()]
            .iter()
            .filter_map(|inst| inst.fires_var.as_ref())
            .collect();
        if fire_vars.is_empty() {
            continue;
        }
        if card.min_fires == 1 {
            solver.assert(smt::bool_or(&fire_vars));
        } else {
            for fire_var in &fire_vars {
                solver.assert(*fire_var);
            }
        }
    }
}

fn scene_group_root(parent: &mut [usize], index: usize) -> usize {
    let mut root = index;
    while parent[root] != root {
        parent[root] = parent[parent[root]];
        root = parent[root];
    }
    root
}

fn assert_scene_same_step_groups(
    ctx: &SceneScheduleCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    group_parent: &mut [usize],
) -> SceneCheckResult<()> {
    let var_to_idx = scene_var_to_idx(&plan.event_var_names);
    let mut pairs = Vec::new();
    collect_same_step_event_pairs(&ctx.scene.ordering, &var_to_idx, &mut pairs);
    for (left, right) in &pairs {
        validate_scene_same_step_cardinality(ctx.scene, plan, *left, *right)?;
        let inst_left = plan.event_instance_ranges[*left].start;
        let inst_right = plan.event_instance_ranges[*right].start;
        let root_left = scene_group_root(group_parent, inst_left);
        let root_right = scene_group_root(group_parent, inst_right);
        if root_left != root_right {
            group_parent[root_right] = root_left;
        }
    }
    Ok(())
}

fn validate_scene_same_step_cardinality(
    scene: &IRScene,
    plan: &SceneFiringPlan<'_>,
    left: usize,
    right: usize,
) -> SceneCheckResult<()> {
    if plan.event_cards[left].n_instances == 1 && plan.event_cards[right].n_instances == 1 {
        return Ok(());
    }
    Err(scene_fail(
        scene,
        crate::messages::scene_same_step_multi_instance(
            &scene.name,
            &plan.event_var_names[left],
            plan.event_cards[left].n_instances,
            &plan.event_var_names[right],
            plan.event_cards[right].n_instances,
        ),
        None,
    ))
}

fn validate_scene_same_step_conflicts(
    ctx: &SceneScheduleCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    group_parent: &mut [usize],
) -> SceneCheckResult<()> {
    let groups = scene_group_plan(plan.instances.len(), group_parent);
    for root in &groups.inst_group_roots {
        let members = scene_group_members(&groups.inst_group, *root);
        if members.len() > 1 {
            validate_scene_group_entity_conflicts(ctx, plan, &members)?;
        }
    }
    Ok(())
}

fn validate_scene_group_entity_conflicts(
    ctx: &SceneScheduleCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    members: &[usize],
) -> SceneCheckResult<()> {
    let mut seen_entities = HashSet::new();
    for index in members {
        let event = &plan.resolved_events[plan.instances[*index].event_idx];
        let mut event_entities = HashSet::new();
        let mut visited_calls = HashSet::new();
        for step in &event.steps {
            collect_event_body_entities(
                &step.body,
                ctx.relevant_systems,
                &mut event_entities,
                &mut visited_calls,
            );
        }
        for entity_name in &event_entities {
            if !seen_entities.insert(entity_name.clone()) {
                return Err(scene_fail(
                    ctx.scene,
                    crate::messages::scene_same_step_entity_conflict(&ctx.scene.name, entity_name),
                    None,
                ));
            }
        }
    }
    Ok(())
}

fn scene_group_plan(instance_count: usize, group_parent: &mut [usize]) -> SceneGroupPlan {
    let inst_group: Vec<usize> = (0..instance_count)
        .map(|index| scene_group_root(group_parent, index))
        .collect();
    let mut inst_group_roots = Vec::new();
    for group in &inst_group {
        if !inst_group_roots.contains(group) {
            inst_group_roots.push(*group);
        }
    }
    SceneGroupPlan {
        inst_group,
        inst_group_roots,
    }
}

fn scene_group_members(inst_group: &[usize], root: usize) -> Vec<usize> {
    (0..inst_group.len())
        .filter(|index| inst_group[*index] == root)
        .collect()
}

fn assert_scene_instance_distinctness(
    solver: &AbideSolver,
    plan: &SceneFiringPlan<'_>,
    groups: &SceneGroupPlan,
) {
    for left in 0..plan.instances.len() {
        for right in (left + 1)..plan.instances.len() {
            let same_step = smt::int_eq(
                &plan.instances[left].step_var,
                &plan.instances[right].step_var,
            );
            if groups.inst_group[left] == groups.inst_group[right] {
                solver.assert(same_step);
            } else {
                solver.assert(smt::bool_not(&same_step));
            }
        }
    }
}

fn assert_scene_ordering_constraints(
    ctx: &SceneScheduleCtx<'_>,
    plan: &SceneFiringPlan<'_>,
) -> SceneCheckResult<()> {
    let var_to_idx = scene_var_to_idx(&plan.event_var_names);
    validate_scene_ordering_vars(ctx.scene, plan, &var_to_idx)?;
    for ordering_expr in &ctx.scene.ordering {
        if let Err(reason) = encode_scene_ordering_v2(
            ordering_expr,
            &var_to_idx,
            &plan.event_instance_ranges,
            &plan.instances,
            ctx.solver,
            &ctx.scene.name,
        ) {
            return Err(scene_fail(ctx.scene, reason, None));
        }
    }
    Ok(())
}

fn validate_scene_ordering_vars(
    scene: &IRScene,
    plan: &SceneFiringPlan<'_>,
    var_to_idx: &HashMap<&str, usize>,
) -> SceneCheckResult<()> {
    for ordering_expr in &scene.ordering {
        for var_name in collect_ordering_leaf_vars(ordering_expr) {
            if !var_to_idx.contains_key(var_name) {
                return Err(scene_fail(
                    scene,
                    crate::messages::scene_ordering_unknown_var(
                        &scene.name,
                        var_name,
                        &plan.event_var_names.join(", "),
                    ),
                    None,
                ));
            }
        }
    }
    Ok(())
}

fn assert_scene_step_transitions(
    ctx: &SceneTransitionCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    groups: &SceneGroupPlan,
) -> SceneCheckResult<()> {
    for step in 0..ctx.bound {
        let mut disjuncts = Vec::new();
        for root in &groups.inst_group_roots {
            let members = scene_group_members(&groups.inst_group, *root);
            let guard = smt::int_eq(&plan.instances[*root].step_var, &smt::int_lit(step as i64));
            let branch = if members.len() == 1 {
                scene_single_instance_branch(ctx, plan, members[0], step, &guard)?
            } else {
                scene_same_step_group_branch(ctx, plan, &members, step, guard)?
            };
            disjuncts.push(branch);
        }
        disjuncts.push(scene_stutter_branch(ctx, groups, plan, step));
        let refs: Vec<&Bool> = disjuncts.iter().collect();
        ctx.solver.assert(smt::bool_or(&refs));
    }
    Ok(())
}

fn scene_single_instance_branch(
    ctx: &SceneTransitionCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    instance_index: usize,
    step: usize,
    step_guard: &Bool,
) -> SceneCheckResult<Bool> {
    let inst = &plan.instances[instance_index];
    let event = &plan.resolved_events[inst.event_idx];
    let formula = scene_event_formula(ctx, event, step)?;
    if let Some(fires) = &inst.fires_var {
        let fires_branch = smt::bool_and(&[step_guard, fires, &formula]);
        let stutter = harness::stutter_constraint(ctx.pool, ctx.relevant_entities, step);
        let skip_branch = smt::bool_and(&[step_guard, &smt::bool_not(fires), &stutter]);
        Ok(smt::bool_or(&[&fires_branch, &skip_branch]))
    } else {
        Ok(smt::bool_and(&[step_guard, &formula]))
    }
}

fn scene_event_formula(
    ctx: &SceneTransitionCtx<'_>,
    event: &ResolvedSceneEvent<'_>,
    step: usize,
) -> SceneCheckResult<Bool> {
    let override_params = scene_event_params(ctx, event, step)?;
    let formulas = event
        .steps
        .iter()
        .map(|step_ir| {
            try_encode_step_with_params(
                ctx.pool,
                ctx.vctx,
                ctx.relevant_entities,
                ctx.relevant_systems,
                step_ir,
                step,
                override_params.clone(),
            )
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|reason| {
            scene_fail(
                ctx.scene,
                format!("transition encoding error: {reason}"),
                None,
            )
        })?;
    Ok(bool_or_values(formulas))
}

fn scene_event_params(
    ctx: &SceneTransitionCtx<'_>,
    event: &ResolvedSceneEvent<'_>,
    step: usize,
) -> SceneCheckResult<HashMap<String, SmtValue>> {
    build_scene_event_params(
        event,
        &SceneEventParamCtx {
            pool: ctx.pool,
            vctx: ctx.vctx,
            defs: ctx.defs,
            given_bindings: ctx.given_bindings,
            store_ranges: ctx.store_ranges,
            step,
        },
    )
    .map_err(|reason| scene_fail(ctx.scene, reason, None))
}

fn scene_same_step_group_branch(
    ctx: &SceneTransitionCtx<'_>,
    plan: &SceneFiringPlan<'_>,
    members: &[usize],
    step: usize,
    step_guard: Bool,
) -> SceneCheckResult<Bool> {
    let mut group_formulas = Vec::new();
    let mut combined_touched = HashSet::new();
    for index in members {
        let inst = &plan.instances[*index];
        let event = &plan.resolved_events[inst.event_idx];
        let (formula, touched) = scene_framed_event_formula(ctx, event, step)?;
        combined_touched.extend(touched);
        if let Some(fires) = &inst.fires_var {
            group_formulas.push(smt::bool_implies(fires, &formula));
        } else {
            group_formulas.push(formula);
        }
    }
    let mut parts = vec![step_guard];
    parts.extend(group_formulas);
    let combined = bool_and_values(parts);
    Ok(harness::apply_global_frame(
        ctx.pool,
        ctx.relevant_entities,
        &combined_touched,
        step,
        combined,
    ))
}

fn scene_framed_event_formula(
    ctx: &SceneTransitionCtx<'_>,
    event: &ResolvedSceneEvent<'_>,
    step: usize,
) -> SceneCheckResult<(Bool, HashSet<(String, usize)>)> {
    let override_params = scene_event_params(ctx, event, step)?;
    let mut branch_results = Vec::new();
    for step_ir in &event.steps {
        let encoded = harness::try_encode_step_inner(
            ctx.pool,
            ctx.vctx,
            ctx.relevant_entities,
            ctx.relevant_systems,
            step_ir,
            step,
            harness::StepEncodingOptions::with_override(0, override_params.clone()),
        )
        .map_err(|reason| {
            scene_fail(
                ctx.scene,
                format!("scene step encoding failed: {reason}"),
                None,
            )
        })?;
        branch_results.push(encoded);
    }
    let touched = branch_results
        .iter()
        .flat_map(|(_, branch_touched)| branch_touched.iter().cloned())
        .collect();
    let formula = scene_framed_branch_formula(ctx, step, branch_results, &touched);
    Ok((formula, touched))
}

fn scene_framed_branch_formula(
    ctx: &SceneTransitionCtx<'_>,
    step: usize,
    branch_results: Vec<(Bool, HashSet<(String, usize)>)>,
    all_touched: &HashSet<(String, usize)>,
) -> Bool {
    let branches = branch_results
        .into_iter()
        .map(|(formula, branch_touched)| {
            let extra: HashSet<(String, usize)> =
                all_touched.difference(&branch_touched).cloned().collect();
            if extra.is_empty() {
                formula
            } else {
                let frame =
                    harness::frame_specific_slots(ctx.pool, ctx.relevant_entities, &extra, step);
                let mut parts = vec![formula];
                parts.extend(frame);
                bool_and_values(parts)
            }
        })
        .collect();
    bool_or_values(branches)
}

fn scene_stutter_branch(
    ctx: &SceneTransitionCtx<'_>,
    groups: &SceneGroupPlan,
    plan: &SceneFiringPlan<'_>,
    step: usize,
) -> Bool {
    let no_instance_parts: Vec<Bool> = groups
        .inst_group_roots
        .iter()
        .map(|root| {
            smt::bool_not(&smt::int_eq(
                &plan.instances[*root].step_var,
                &smt::int_lit(step as i64),
            ))
        })
        .collect();
    let no_instance = bool_and_values(no_instance_parts);
    let stutter = harness::stutter_constraint(ctx.pool, ctx.relevant_entities, step);
    smt::bool_and(&[&no_instance, &stutter])
}

fn assert_scene_result_activation(
    scene: &IRScene,
    pool: &harness::SlotPool,
    solver: &AbideSolver,
    given_bindings: &HashMap<String, (String, usize)>,
    plan: &SceneFiringPlan<'_>,
    bound: usize,
) {
    for (event_idx, event) in plan.resolved_events.iter().enumerate() {
        let Some((result_entity, allocated_slot)) = given_bindings.get(&event.scene_event.var)
        else {
            continue;
        };
        if scene
            .givens
            .iter()
            .any(|given| given.var == event.scene_event.var)
        {
            continue;
        }
        let range = &plan.event_instance_ranges[event_idx];
        if !range.is_empty() {
            assert_scene_first_instance_activation(
                pool,
                solver,
                result_entity,
                *allocated_slot,
                &plan.instances[range.start],
                bound,
            );
        }
    }
}

fn assert_scene_first_instance_activation(
    pool: &harness::SlotPool,
    solver: &AbideSolver,
    result_entity: &str,
    allocated_slot: usize,
    first_inst: &FiringInst,
    bound: usize,
) {
    for step in 0..bound {
        let Some(SmtValue::Bool(active_next)) =
            pool.active_at(result_entity, allocated_slot, step + 1)
        else {
            continue;
        };
        let mut guard = smt::int_eq(&first_inst.step_var, &smt::int_lit(step as i64));
        if let Some(fires) = &first_inst.fires_var {
            guard = smt::bool_and(&[&guard, fires]);
        }
        solver.assert(smt::bool_implies(&guard, active_next));
    }
}

fn assert_scene_then_assertions(ctx: &SceneTransitionCtx<'_>) -> SceneCheckResult<PropertyCtx> {
    let final_step = ctx.bound;
    let then_ctx = scene_then_ctx(ctx.store_ranges, ctx.given_bindings);
    for assertion in &ctx.scene.assertions {
        let prop = encode_prop_expr_with_ctx(
            ctx.pool, ctx.vctx, ctx.defs, &then_ctx, assertion, final_step,
        )
        .map_err(|msg| {
            scene_fail(
                ctx.scene,
                format!("encoding error in then assertion: {msg}"),
                expr_span(assertion),
            )
        })?;
        ctx.solver.assert(&prop);
    }
    Ok(then_ctx)
}

fn scene_then_ctx(
    store_ranges: &HashMap<String, VerifyStoreRange>,
    given_bindings: &HashMap<String, (String, usize)>,
) -> PropertyCtx {
    let mut ctx = PropertyCtx::new().with_store_ranges(store_ranges.clone());
    for (var, (entity, slot)) in given_bindings {
        ctx = ctx.with_binding(var, entity, *slot);
    }
    ctx
}

fn bool_or_values(values: Vec<Bool>) -> Bool {
    if values.len() == 1 {
        values.into_iter().next().unwrap()
    } else {
        let refs: Vec<&Bool> = values.iter().collect();
        smt::bool_or(&refs)
    }
}

fn bool_and_values(values: Vec<Bool>) -> Bool {
    let refs: Vec<&Bool> = values.iter().collect();
    smt::bool_and(&refs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_ir() -> IRProgram {
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

    fn empty_scene() -> IRScene {
        IRScene {
            name: "empty_scene".to_owned(),
            systems: vec![],
            stores: vec![],
            givens: vec![],
            events: vec![],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }
    }

    #[test]
    fn scene_solver_result_distinguishes_sat_unsat_and_unknown() {
        let scene = empty_scene();

        let sat = scene_solver_result(&scene, SatResult::Sat, 7, None);
        assert!(matches!(
            sat,
            VerificationResult::ScenePass {
                ref name,
                time_ms: 7,
                ..
            } if name == "empty_scene"
        ));

        let unsat = scene_solver_result(&scene, SatResult::Unsat, 7, None);
        assert!(matches!(
            unsat,
            VerificationResult::SceneFail {
                ref name,
                ref reason,
                ..
            } if name == "empty_scene" && reason.contains("unsatisfiable")
        ));

        let unknown =
            scene_solver_result(&scene, SatResult::Unknown("timeout".to_owned()), 7, None);
        let unknown_json = serde_json::to_value(&unknown).expect("serialize scene unknown");
        assert_eq!(unknown_json["kind"], "scene_unknown");
        assert!(
            format!("{unknown}").contains("UNKNOWN"),
            "human display should distinguish scene unknown"
        );
        assert!(matches!(
            unknown,
            VerificationResult::SceneUnknown {
                ref name,
                ref reason,
                ..
            } if name == "empty_scene" && reason.contains("timeout")
        ));
    }

    fn scene_with_unsupported_given() -> IRScene {
        IRScene {
            name: "unsupported_given".to_owned(),
            systems: vec![],
            stores: vec![],
            givens: vec![crate::ir::types::IRSceneGiven {
                var: "task".to_owned(),
                entity: "Task".to_owned(),
                store_name: None,
                constraint: IRExpr::Sorry { span: None },
            }],
            events: vec![],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }
    }

    fn store_decl(name: &str, entity_type: &str, hi: i64) -> crate::ir::types::IRStoreDecl {
        crate::ir::types::IRStoreDecl {
            name: name.to_owned(),
            entity_type: entity_type.to_owned(),
            lo: hi,
            hi,
        }
    }

    fn given(var: &str, entity: &str, store_name: Option<&str>) -> crate::ir::types::IRSceneGiven {
        crate::ir::types::IRSceneGiven {
            var: var.to_owned(),
            entity: entity.to_owned(),
            store_name: store_name.map(str::to_owned),
            constraint: bool_lit(true),
        }
    }

    fn store_scene(
        name: &str,
        stores: Vec<crate::ir::types::IRStoreDecl>,
        givens: Vec<crate::ir::types::IRSceneGiven>,
        given_constraints: Vec<IRExpr>,
        assertions: Vec<IRExpr>,
        activations: Vec<crate::ir::types::IRActivation>,
    ) -> IRScene {
        IRScene {
            name: name.to_owned(),
            systems: vec![],
            stores,
            givens,
            events: vec![],
            ordering: vec![],
            assertions,
            given_constraints,
            activations,
            span: None,
            file: None,
        }
    }

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: crate::ir::types::IRType::Bool,
            value: crate::ir::types::LitVal::Bool { value },
            span: None,
        }
    }

    fn bool_field(var_name: &str, entity_name: &str, field: &str) -> IRExpr {
        IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: var_name.to_owned(),
                ty: crate::ir::types::IRType::Entity {
                    name: entity_name.to_owned(),
                },
                span: None,
            }),
            field: field.to_owned(),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }
    }

    fn bool_field_eq(var_name: &str, entity_name: &str, field: &str, value: bool) -> IRExpr {
        IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(bool_field(var_name, entity_name, field)),
            right: Box::new(bool_lit(value)),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }
    }

    fn var(name: &str) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }
    }

    fn bin(op: &str, left: IRExpr, right: IRExpr) -> IRExpr {
        IRExpr::BinOp {
            op: op.to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        }
    }

    fn firing(event_idx: usize, inst_idx: usize, fires_var: Option<Bool>) -> FiringInst {
        FiringInst {
            event_idx,
            inst_idx,
            step_var: smt::int_const(&format!("s_{event_idx}_{inst_idx}")),
            fires_var,
        }
    }

    #[test]
    fn scene_ordering_collectors_walk_nested_sequence_same_step_and_xor() {
        let expr = bin(
            "OpSeq",
            bin("OpSameStep", var("a"), var("b")),
            bin("OpXor", var("c"), var("d")),
        );
        assert_eq!(collect_ordering_leaf_vars(&expr), vec!["a", "b", "c", "d"]);

        let var_to_idx =
            HashMap::from([("a", 0usize), ("b", 1usize), ("c", 2usize), ("d", 3usize)]);
        assert_eq!(first_ordering_var(&expr, &var_to_idx), Some(0));
        assert_eq!(last_ordering_var(&expr, &var_to_idx), Some(3));

        let mut pairs = Vec::new();
        collect_same_step_event_pairs(std::slice::from_ref(&expr), &var_to_idx, &mut pairs);
        assert_eq!(pairs, vec![(0, 1)]);

        let mut xor_events = HashSet::new();
        collect_xor_event_indices(&expr, &var_to_idx, &mut xor_events);
        assert_eq!(xor_events, HashSet::from([2, 3]));
        assert_eq!(event_var_names_from_idx(2, &var_to_idx), "c");
        assert_eq!(event_var_names_from_idx(99, &var_to_idx), "event_99");
    }

    #[test]
    fn scene_ordering_encoder_rejects_unknown_empty_and_untracked_xor_shapes() {
        let solver = AbideSolver::new();
        let var_to_idx = HashMap::from([("a", 0usize), ("b", 1usize)]);
        let instances = vec![
            firing(0, 0, Some(smt::bool_named("a_fires"))),
            firing(1, 0, Some(smt::bool_named("b_fires"))),
        ];

        let unknown = encode_scene_ordering_v2(
            &bin("OpSeq", var("a"), bool_lit(true)),
            &var_to_idx,
            &[0..1, 1..2],
            &instances,
            &solver,
            "ordering_errors",
        );
        assert!(matches!(unknown, Err(reason) if reason.contains("unknown event variable")));

        let empty_xor = encode_scene_ordering_v2(
            &bin("OpXor", var("a"), var("b")),
            &var_to_idx,
            &[0..0, 1..2],
            &instances,
            &solver,
            "ordering_errors",
        );
        assert!(matches!(empty_xor, Err(reason) if reason.contains("ordering_errors")));

        let no_fire_instances = vec![
            firing(0, 0, None),
            firing(1, 0, Some(smt::bool_named("b_fires_2"))),
        ];
        let no_fire = encode_scene_ordering_v2(
            &bin("OpXor", var("a"), var("b")),
            &var_to_idx,
            &[0..1, 1..2],
            &no_fire_instances,
            &solver,
            "ordering_errors",
        );
        assert!(matches!(no_fire, Err(reason) if reason.contains("ordering_errors")));
    }

    #[test]
    fn scene_ordering_encoder_accepts_basic_sequence_same_step_concurrency_and_xor() {
        let solver = AbideSolver::new();
        let var_to_idx = HashMap::from([("a", 0usize), ("b", 1usize), ("c", 2usize)]);
        let instances = vec![
            firing(0, 0, Some(smt::bool_named("a_fires_ok"))),
            firing(1, 0, Some(smt::bool_named("b_fires_ok"))),
            firing(2, 0, Some(smt::bool_named("c_fires_ok"))),
        ];
        let expr = bin(
            "OpConc",
            bin("OpSeq", var("a"), var("b")),
            bin("OpXor", var("b"), var("c")),
        );
        encode_scene_ordering_v2(
            &expr,
            &var_to_idx,
            &[0..1, 1..2, 2..3],
            &instances,
            &solver,
            "ordering_ok",
        )
        .expect("supported ordering should encode");
    }

    #[test]
    fn check_scene_block_reports_empty_scope_without_solver_work() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &empty_scene(),
            &VerifyConfig::default(),
            None,
        );
        assert!(matches!(
            result,
            VerificationResult::SceneFail { name, reason, .. }
                if name == "empty_scene" && reason == crate::messages::SCENE_EMPTY_SCOPE
        ));
    }

    #[test]
    fn check_scene_block_reports_unsupported_given_before_slot_allocation() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &scene_with_unsupported_given(),
            &VerifyConfig::default(),
            None,
        );
        assert!(matches!(
            result,
            VerificationResult::SceneFail { name, reason, .. }
                if name == "unsupported_given"
                    && reason.contains("unsupported expression kind in scene given")
        ));
    }

    #[test]
    fn check_scene_block_reports_store_binding_validation_errors() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let mismatch = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "mismatch",
                vec![store_decl("tasks", "Task", 1)],
                vec![given("order", "Order", Some("tasks"))],
                vec![],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            mismatch,
            VerificationResult::SceneFail { reason, .. } if reason.contains("entity type mismatch")
        ));

        let unknown_store = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unknown_store",
                vec![store_decl("tasks", "Task", 1)],
                vec![given("task", "Task", Some("missing"))],
                vec![],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unknown_store,
            VerificationResult::SceneFail { reason, .. } if reason.contains("unknown store 'missing'")
        ));

        let full_store = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "full_store",
                vec![store_decl("tasks", "Task", 1)],
                vec![
                    given("first", "Task", Some("tasks")),
                    given("second", "Task", Some("tasks")),
                ],
                vec![],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            full_store,
            VerificationResult::SceneFail { reason, .. } if reason.contains("store 'tasks' is full")
        ));
    }

    #[test]
    fn check_scene_block_suppresses_defaults_from_raw_given_constraints() {
        let mut ir = empty_ir();
        ir.entities.push(crate::ir::types::IREntity {
            name: "Door".to_owned(),
            fields: vec![crate::ir::types::IRField {
                name: "locked".to_owned(),
                ty: crate::ir::types::IRType::Bool,
                default: Some(bool_lit(false)),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        });
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "raw_given_constraint_overrides_default",
                vec![store_decl("doors", "Door", 1)],
                vec![given("d", "Door", Some("doors"))],
                vec![bool_field_eq("d", "Door", "locked", true)],
                vec![bool_field_eq("d", "Door", "locked", true)],
                vec![],
            ),
            &VerifyConfig::default(),
            None,
        );
        assert!(
            matches!(
                result,
                VerificationResult::ScenePass { ref name, .. }
                    if name == "raw_given_constraint_overrides_default"
            ),
            "raw given constraint should suppress conflicting entity default, got: {result}"
        );
    }

    #[test]
    fn check_scene_block_enforces_unique_match_for_one_bindings() {
        let mut ir = empty_ir();
        ir.entities.push(crate::ir::types::IREntity {
            name: "Door".to_owned(),
            fields: vec![crate::ir::types::IRField {
                name: "locked".to_owned(),
                ty: crate::ir::types::IRType::Bool,
                default: Some(bool_lit(false)),
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        });
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let mut first = given("d1", "Door", Some("doors"));
        first.constraint = bool_field_eq("d1", "Door", "locked", true);
        let mut second = given("d2", "Door", Some("doors"));
        second.constraint = bool_field_eq("d2", "Door", "locked", true);

        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "duplicate_one_matches",
                vec![store_decl("doors", "Door", 2)],
                vec![first, second],
                vec![],
                vec![bool_lit(true)],
                vec![],
            ),
            &VerifyConfig::default(),
            None,
        );
        assert!(
            matches!(result, VerificationResult::SceneFail { ref name, ref reason, .. }
                if name == "duplicate_one_matches" && reason == crate::messages::SCENE_UNSATISFIABLE),
            "duplicate one bindings with the same matching predicate should be unsat, got: {result}"
        );
    }

    #[test]
    fn check_scene_block_reports_activation_and_expression_validation_errors() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let unknown_activation_store = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unknown_activation_store",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![],
                vec![],
                vec![crate::ir::types::IRActivation {
                    instances: vec!["task".to_owned()],
                    store_name: "missing".to_owned(),
                }],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unknown_activation_store,
            VerificationResult::SceneFail { reason, .. } if reason.contains("unknown store 'missing'")
        ));

        let unsupported_given_constraint = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unsupported_given_constraint",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![IRExpr::Todo { span: None }],
                vec![],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unsupported_given_constraint,
            VerificationResult::SceneFail { reason, .. }
                if reason.contains("unsupported expression kind in scene given constraint")
        ));

        let unsupported_assertion = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "unsupported_assertion",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![],
                vec![IRExpr::Sorry { span: None }],
                vec![],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unsupported_assertion,
            VerificationResult::SceneFail { reason, .. }
                if reason.contains("unsupported expression kind in scene then assertion")
        ));
    }

    #[test]
    fn build_scene_event_params_resolves_given_entity_args_to_slots() {
        let entity = crate::ir::types::IREntity {
            name: "Copy".to_owned(),
            fields: vec![],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let mut ir = empty_ir();
        ir.entities.push(entity.clone());
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = create_slot_pool_with_systems(
            std::slice::from_ref(&entity),
            &HashMap::from([("Copy".to_owned(), 1)]),
            1,
            &[],
        );
        let action = IRSystemAction {
            name: "checkout".to_owned(),
            params: vec![crate::ir::types::IRTransParam {
                name: "copy".to_owned(),
                ty: crate::ir::types::IRType::Entity {
                    name: "Copy".to_owned(),
                },
            }],
            guard: bool_lit(true),
            body: vec![],
            return_expr: None,
        };
        let scene_event = IRSceneEvent {
            var: "checkout".to_owned(),
            system: "Library".to_owned(),
            event: "checkout".to_owned(),
            args: vec![IRExpr::Var {
                name: "given_copy".to_owned(),
                ty: crate::ir::types::IRType::Entity {
                    name: "Copy".to_owned(),
                },
                span: None,
            }],
            cardinality: crate::ir::types::Cardinality::Named("one".to_owned()),
        };
        let resolved = ResolvedSceneEvent {
            scene_event: &scene_event,
            steps: vec![&action],
        };
        let params = build_scene_event_params(
            &resolved,
            &SceneEventParamCtx {
                pool: &pool,
                vctx: &vctx,
                defs: &defs,
                given_bindings: &HashMap::from([(
                    "given_copy".to_owned(),
                    ("Copy".to_owned(), 0usize),
                )]),
                store_ranges: &HashMap::new(),
                step: 0,
            },
        )
        .expect("given-bound entity scene arg should encode as slot id");

        let value = params.get("copy").expect("entity param should be bound");
        assert_eq!(
            value.as_int().expect("slot id should be Int").to_string(),
            "0"
        );
    }

    #[test]
    fn build_scene_event_params_supports_direct_choose_arg_witness() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = create_slot_pool_with_systems(&[], &HashMap::new(), 1, &[]);
        let action = IRSystemAction {
            name: "set_one".to_owned(),
            params: vec![crate::ir::types::IRTransParam {
                name: "next".to_owned(),
                ty: crate::ir::types::IRType::Int,
            }],
            guard: bool_lit(true),
            body: vec![],
            return_expr: None,
        };
        let scene_event = IRSceneEvent {
            var: "set_one".to_owned(),
            system: "App".to_owned(),
            event: "set_one".to_owned(),
            args: vec![IRExpr::Choose {
                var: "n".to_owned(),
                domain: crate::ir::types::IRType::Int,
                predicate: Some(Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "n".to_owned(),
                        ty: crate::ir::types::IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: crate::ir::types::IRType::Int,
                        value: crate::ir::types::LitVal::Int { value: 1 },
                        span: None,
                    }),
                    ty: crate::ir::types::IRType::Bool,
                    span: None,
                })),
                ty: crate::ir::types::IRType::Int,
                span: None,
            }],
            cardinality: crate::ir::types::Cardinality::Named("one".to_owned()),
        };
        let resolved = ResolvedSceneEvent {
            scene_event: &scene_event,
            steps: vec![&action],
        };
        let params = build_scene_event_params(
            &resolved,
            &SceneEventParamCtx {
                pool: &pool,
                vctx: &vctx,
                defs: &defs,
                given_bindings: &HashMap::new(),
                store_ranges: &HashMap::new(),
                step: 0,
            },
        )
        .expect("direct choose equality scene arg should encode");

        let value = params.get("next").expect("param should be bound");
        assert_eq!(
            value.as_int().expect("witness should be Int").to_string(),
            "1"
        );
    }

    #[test]
    fn check_scene_block_supports_finite_setcomp_cardinality_assertions() {
        let mut ir = empty_ir();
        ir.entities.push(crate::ir::types::IREntity {
            name: "Task".to_owned(),
            fields: vec![crate::ir::types::IRField {
                name: "id".to_owned(),
                ty: crate::ir::types::IRType::Identity,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        });
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let bool_set_ty = crate::ir::types::IRType::Set {
            element: Box::new(crate::ir::types::IRType::Bool),
        };
        let assertion = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Card {
                expr: Box::new(IRExpr::SetComp {
                    var: "b".to_owned(),
                    domain: crate::ir::types::IRType::Bool,
                    source: None,
                    filter: Box::new(IRExpr::Var {
                        name: "b".to_owned(),
                        ty: crate::ir::types::IRType::Bool,
                        span: None,
                    }),
                    projection: None,
                    ty: bool_set_ty,
                    span: None,
                }),
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: crate::ir::types::IRType::Int,
                value: crate::ir::types::LitVal::Int { value: 1 },
                span: None,
            }),
            ty: crate::ir::types::IRType::Bool,
            span: None,
        };

        let result = check_scene_block(
            &ir,
            &vctx,
            &defs,
            &store_scene(
                "finite_setcomp_cardinality",
                vec![store_decl("tasks", "Task", 1)],
                vec![],
                vec![],
                vec![assertion],
                vec![],
            ),
            &VerifyConfig::default(),
            None,
        );
        assert!(
            matches!(
                result,
                VerificationResult::ScenePass { ref name, .. } if name == "finite_setcomp_cardinality"
            ),
            "expected finite set-comprehension cardinality scene to pass, got: {result}"
        );
    }
}
