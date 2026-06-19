use super::nested::{try_encode_nested_op, NestedOpCtx};
use super::*;

#[derive(Clone)]
pub(super) struct MacroBranch {
    formula: Bool,
    touched: HashSet<(String, usize)>,
    locals: HashMap<String, SmtValue>,
    return_value: Option<SmtValue>,
}

#[derive(Clone, Copy)]
pub(super) struct StepEncodingCtx<'a> {
    pool: &'a SlotPool,
    vctx: &'a VerifyContext,
    entities: &'a [IREntity],
    all_systems: &'a [IRSystem],
    step: usize,
    depth: usize,
}

pub(crate) struct StepEncodingOptions {
    pub(crate) depth: usize,
    pub(crate) override_params: Option<HashMap<String, SmtValue>>,
}

impl StepEncodingOptions {
    pub(crate) fn root() -> Self {
        Self {
            depth: 0,
            override_params: None,
        }
    }

    pub(crate) fn with_override(depth: usize, override_params: HashMap<String, SmtValue>) -> Self {
        Self {
            depth,
            override_params: Some(override_params),
        }
    }
}

pub(super) fn contains_macro_actions(actions: &[IRAction]) -> bool {
    actions.iter().any(|action| match action {
        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => true,
        IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => contains_macro_actions(ops),
        _ => false,
    })
}

pub(crate) fn try_encode_step_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    options: StepEncodingOptions,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    let ctx = StepEncodingCtx {
        pool,
        vctx,
        entities,
        all_systems,
        step,
        depth: options.depth,
    };
    try_encode_step_inner_branching(&ctx, event, options.override_params)
}

pub(crate) fn try_encode_step_inner_legacy(
    ctx: &StepEncodingCtx<'_>,
    event: &IRSystemAction,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    validate_legacy_step_context(ctx)?;
    let scope = step_scope_metadata(ctx.all_systems, event);
    let mut state = LegacyStepState::new(event, override_params, ctx.step, &scope);
    state.conjuncts.push(event_fire_precondition_formula(
        ctx.pool,
        ctx.vctx,
        event,
        ctx.step,
        &state.step_params,
        &scope,
    )?);
    let guard = encode_legacy_event_guard(ctx, event, &scope, &state.step_params)?;
    let action_ctx = LegacyActionCtx {
        step: *ctx,
        scope: &scope,
    };
    // The command body only runs when the command fires (its guard holds), so
    // guard div/mod obligations recorded inside it (e.g. `x' = a / b`) by the
    // command guard — a divisor kept non-zero by a `requires` is not flagged.
    let guarded = guard.is_some();
    if let Some(guard) = guard {
        crate::verify::property::push_harness_div_guard(guard);
    }
    let result = (|| {
        for action in &event.body {
            encode_legacy_action(&action_ctx, &mut state, action)?;
        }
        Ok::<(), String>(())
    })();
    if guarded {
        crate::verify::property::pop_harness_div_guard();
    }
    result?;
    Ok((legacy_formula(state.conjuncts), state.touched))
}

struct LegacyStepState {
    conjuncts: Vec<Bool>,
    touched: HashSet<(String, usize)>,
    chain_id: usize,
    step_params: HashMap<String, SmtValue>,
    var_to_entity: HashMap<String, String>,
    choose_var_params: HashMap<String, SmtValue>,
}

impl LegacyStepState {
    fn new(
        event: &IRSystemAction,
        override_params: Option<HashMap<String, SmtValue>>,
        step: usize,
        scope: &StepScopeMetadata,
    ) -> Self {
        let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
        Self {
            conjuncts: Vec::new(),
            touched: HashSet::new(),
            chain_id: 0,
            step_params,
            var_to_entity: scope.entity_param_types.clone(),
            choose_var_params: HashMap::new(),
        }
    }

    fn merged_params(&self) -> HashMap<String, SmtValue> {
        let mut params = self.step_params.clone();
        params.extend(self.choose_var_params.clone());
        params
    }

    fn mark_entity_slots(&mut self, entity: &str, n_slots: usize) {
        for slot in 0..n_slots {
            self.touched.insert((entity.to_owned(), slot));
        }
    }
}

struct LegacyActionCtx<'a> {
    step: StepEncodingCtx<'a>,
    scope: &'a StepScopeMetadata,
}

type LegacyNestedEncoding = (Vec<Bool>, HashSet<(String, usize)>);

#[derive(Clone, Copy, PartialEq, Eq)]
enum LegacyBoundKind {
    Choose,
    ForAll,
}

#[derive(Clone, Copy)]
struct LegacyBoundSlot<'a> {
    kind: LegacyBoundKind,
    var: &'a str,
    entity_name: &'a str,
    entity: &'a IREntity,
    slot: usize,
    ops: &'a [IRAction],
}

#[derive(Clone, Copy)]
struct LegacyBoundApply<'a> {
    transition: &'a str,
    args: &'a [IRExpr],
    refs: &'a [String],
}

fn validate_legacy_step_context(ctx: &StepEncodingCtx<'_>) -> Result<(), String> {
    if ctx.depth > 10 {
        return Err(format!(
            "CrossCall recursion depth exceeded (depth {}) — possible cyclic cross-system calls",
            ctx.depth
        ));
    }
    if ctx.step >= ctx.pool.bound {
        return Err(format!(
            "step {} out of bounds for bound {}",
            ctx.step, ctx.pool.bound
        ));
    }
    Ok(())
}

fn encode_legacy_event_guard(
    ctx: &StepEncodingCtx<'_>,
    event: &IRSystemAction,
    scope: &StepScopeMetadata,
    step_params: &HashMap<String, SmtValue>,
) -> Result<Option<Bool>, String> {
    if matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        return Ok(None);
    }
    let guard = if scope.owning_system_name.is_empty() {
        try_encode_guard_expr(
            ctx.pool,
            ctx.vctx,
            &event.guard,
            step_params,
            &scope.store_param_types,
            ctx.step,
        )
    } else {
        try_encode_guard_expr_for_system(
            ctx.pool,
            ctx.vctx,
            &event.guard,
            ctx.step,
            SystemGuardScope {
                step_params,
                system_name: &scope.owning_system_name,
                entity_param_types: &scope.entity_param_types,
                store_param_types: &scope.store_param_types,
            },
        )
    }?;
    Ok(Some(guard))
}

fn encode_legacy_action(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    action: &IRAction,
) -> Result<(), String> {
    match action {
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } => encode_legacy_choose(ctx, state, var, entity, filter, ops),
        IRAction::Apply {
            target,
            transition,
            args,
            refs,
        } => encode_legacy_apply(ctx, state, target, transition, args, refs),
        IRAction::Create { entity, fields } => encode_legacy_create(ctx, state, entity, fields),
        IRAction::ForAll { var, entity, ops } => encode_legacy_forall(ctx, state, var, entity, ops),
        IRAction::CrossCall {
            system,
            command,
            args,
        } => encode_legacy_cross_call(ctx, state, system, command, args),
        IRAction::ExprStmt { expr } => encode_legacy_expr_stmt(ctx, state, expr),
        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
            Err("internal: macro-step actions reached legacy step encoder".to_owned())
        }
    }
}

fn encode_legacy_choose(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    var: &str,
    entity_name: &str,
    filter: &IRExpr,
    ops: &[IRAction],
) -> Result<(), String> {
    state
        .var_to_entity
        .insert(var.to_owned(), entity_name.to_owned());
    let n_slots = ctx.step.pool.slots_for(entity_name);
    let entity = ctx.step.entities.iter().find(|e| e.name == *entity_name);
    let params = state.merged_params();
    let mut slot_options = Vec::new();
    let mut nested_touched = HashSet::new();
    for slot in 0..n_slots {
        if let Some(entity) = entity {
            slot_options.push(encode_legacy_choose_slot(
                ctx,
                state,
                LegacyBoundSlot {
                    kind: LegacyBoundKind::Choose,
                    var,
                    entity_name,
                    entity,
                    slot,
                    ops,
                },
                filter,
                &params,
                &mut nested_touched,
            )?);
        }
    }
    if !slot_options.is_empty() {
        state.conjuncts.push(bool_or_all(slot_options));
        state.mark_entity_slots(entity_name, n_slots);
    }
    state.touched.extend(nested_touched);
    if let Some(entity) = entity {
        register_legacy_choose_params(state, var, entity, ctx.step.step);
    }
    Ok(())
}

fn encode_legacy_choose_slot(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    filter: &IRExpr,
    params: &HashMap<String, SmtValue>,
    nested_touched: &mut HashSet<(String, usize)>,
) -> Result<Bool, String> {
    let slot_ctx = legacy_slot_ctx(ctx, bound.entity_name, bound.slot, params.clone(), "");
    let mut parts = Vec::new();
    let active_opt = match ctx
        .step
        .pool
        .active_at(bound.entity_name, bound.slot, ctx.step.step)
    {
        Some(SmtValue::Bool(active)) => Some(active.clone()),
        _ => None,
    };
    if let Some(active) = &active_opt {
        parts.push(active.clone());
    }
    let filter_bool = try_encode_slot_expr(&slot_ctx, filter, ctx.step.step)?.to_bool()?;
    parts.push(filter_bool.clone());
    // A div/mod in this slot's body is only evaluated when the slot is active
    // and passes the filter, so guard its well-definedness obligation by both;
    // a divisor in a non-selected `choose` slot is not falsely flagged.
    let div_guard = match &active_opt {
        Some(active) => smt::bool_and(&[active, &filter_bool]),
        None => filter_bool,
    };
    crate::verify::property::push_harness_div_guard(div_guard);
    let ops_result = encode_legacy_bound_ops(
        ctx,
        state,
        bound,
        &slot_ctx,
        params,
        &mut parts,
        nested_touched,
    );
    crate::verify::property::pop_harness_div_guard();
    ops_result?;
    constrain_legacy_choose_slot_params(ctx, bound, &mut parts);
    parts.extend(frame_entity_slots_except(
        ctx.step.pool,
        bound.entity,
        bound.slot,
        ctx.step.step,
    ));
    Ok(and_all(parts))
}

fn register_legacy_choose_params(
    state: &mut LegacyStepState,
    var: &str,
    entity: &IREntity,
    step: usize,
) {
    for field in &entity.fields {
        let shared_name = format!("choose_{var}_{}_t{step}", field.name);
        let shared_var = legacy_fresh_field_value(&shared_name, &field.ty);
        state
            .choose_var_params
            .insert(format!("{var}.{}", field.name), shared_var);
    }
}

fn constrain_legacy_choose_slot_params(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    parts: &mut Vec<Bool>,
) {
    for field in &bound.entity.fields {
        let shared_name = format!("choose_{}_{}_t{}", bound.var, field.name, ctx.step.step);
        let shared_var = legacy_fresh_field_value(&shared_name, &field.ty);
        if let Some(slot_val) =
            ctx.step
                .pool
                .field_at(bound.entity_name, bound.slot, &field.name, ctx.step.step)
        {
            if let Some(eq) = smt_value_eq(&shared_var, slot_val) {
                parts.push(eq);
            }
        }
    }
}

fn encode_legacy_forall(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    var: &str,
    entity_name: &str,
    ops: &[IRAction],
) -> Result<(), String> {
    let n_slots = ctx.step.pool.slots_for(entity_name);
    let Some(entity) = ctx.step.entities.iter().find(|e| e.name == *entity_name) else {
        return Ok(());
    };
    let params = state.merged_params();
    // Entities this body may write (field update, create, or activation),
    // resolving Apply targets through the bound variables in scope. Used to
    // decide which foreign-entity slots a forall's *inactive* iteration may
    // safely frame: framing an entity the body writes would over-constrain
    // the transition (and is unsound — it could mask real behaviours).
    let mut modified: HashSet<String> = HashSet::new();
    let mut scope = vec![(var.to_owned(), entity_name.to_owned())];
    collect_modified_entities(ops, ctx.step.entities, &mut scope, &mut modified);
    let mut nested_touched = HashSet::new();
    for slot in 0..n_slots {
        let slot_formula = encode_legacy_forall_slot(
            ctx,
            state,
            LegacyBoundSlot {
                kind: LegacyBoundKind::ForAll,
                var,
                entity_name,
                entity,
                slot,
                ops,
            },
            &params,
            &modified,
            &mut nested_touched,
        )?;
        state.conjuncts.push(slot_formula);
        state.touched.insert((entity_name.to_owned(), slot));
    }
    state.touched.extend(nested_touched);
    Ok(())
}

/// Collect the set of entity names a `forall`/`choose` body may modify —
/// write a field, `create`, or activate a slot. `Apply` targets are resolved
/// through the bound variables in `scope` (innermost first), then by entity
/// name, then by unique transition owner. Unresolvable targets and any
/// cross-system call conservatively mark every candidate entity as modified,
/// so the set is a sound over-approximation: callers that frame only
/// *unmodified* entities never drop a real write.
fn collect_modified_entities(
    ops: &[IRAction],
    entities: &[IREntity],
    scope: &mut Vec<(String, String)>,
    out: &mut HashSet<String>,
) {
    for op in ops {
        match op {
            IRAction::Create { entity, .. } => {
                out.insert(entity.clone());
            }
            IRAction::Apply {
                target, transition, ..
            } => {
                let resolved = scope
                    .iter()
                    .rev()
                    .find(|(v, _)| v == target)
                    .map(|(_, e)| e.clone())
                    .or_else(|| {
                        entities
                            .iter()
                            .find(|e| e.name == *target)
                            .map(|e| e.name.clone())
                    });
                if let Some(name) = resolved {
                    out.insert(name);
                } else {
                    // Unresolved target — conservatively mark every entity
                    // that owns this transition as potentially modified.
                    for entity in entities
                        .iter()
                        .filter(|e| e.transitions.iter().any(|t| t.name == *transition))
                    {
                        out.insert(entity.name.clone());
                    }
                }
            }
            IRAction::Choose {
                var, entity, ops, ..
            }
            | IRAction::ForAll {
                var, entity, ops, ..
            } => {
                scope.push((var.clone(), entity.clone()));
                collect_modified_entities(ops, entities, scope, out);
                scope.pop();
            }
            IRAction::Match { arms, .. } => {
                for arm in arms {
                    collect_modified_entities(&arm.body, entities, scope, out);
                }
            }
            IRAction::CrossCall { .. } | IRAction::LetCrossCall { .. } => {
                // A cross-system command may mutate any entity; over-approximate.
                for entity in entities {
                    out.insert(entity.name.clone());
                }
            }
            IRAction::ExprStmt { .. } => {}
        }
    }
}

fn encode_legacy_forall_slot(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    params: &HashMap<String, SmtValue>,
    modified: &HashSet<String>,
    nested_touched: &mut HashSet<(String, usize)>,
) -> Result<Bool, String> {
    let slot_ctx = legacy_slot_ctx(ctx, bound.entity_name, bound.slot, params.clone(), "");
    let mut op_parts = Vec::new();
    // Track the slots THIS iteration's body would constrain so they can be
    // framed in the inactive branch. A `forall` ranges over every slot and
    // "fires" even when no slot is active, so unlike `choose` it cannot rely
    // on an empty disjunction to forbid an empty step. Cross-entity bodies
    // (e.g. `forall c { choose m { c.sync_from_marker(m) } }`) mark the other
    // entity's slots as touched, which suppresses the global frame for them;
    // when this counter slot is inactive its body emits no constraint, so we
    // must re-frame those touched slots here or they would be left free.
    let mut slot_touched: HashSet<(String, usize)> = HashSet::new();
    // A `forall` body's constraints (and any div/mod inside them) are only
    // asserted for active slots — the inactive branch just frames the slot. So
    // guard div obligations recorded here by this slot's active flag, or a
    // divisor in an inactive iteration could be falsely flagged.
    let div_guard = match ctx
        .step
        .pool
        .active_at(bound.entity_name, bound.slot, ctx.step.step)
    {
        Some(SmtValue::Bool(active)) => Some(active.clone()),
        _ => None,
    };
    if let Some(active) = &div_guard {
        crate::verify::property::push_harness_div_guard(active.clone());
    }
    let ops_result = encode_legacy_bound_ops(
        ctx,
        state,
        bound,
        &slot_ctx,
        params,
        &mut op_parts,
        &mut slot_touched,
    );
    if div_guard.is_some() {
        crate::verify::property::pop_harness_div_guard();
    }
    ops_result?;
    // Only re-frame *foreign* slots the body reads but never writes. The bound
    // entity's own slots are already covered by every iteration's active/
    // inactive split and the global frame; framing an entity the body writes
    // would over-constrain the transition.
    let frame_targets: HashSet<(String, usize)> = slot_touched
        .iter()
        .filter(|(ent, _)| *ent != bound.entity_name && !modified.contains(ent))
        .cloned()
        .collect();
    let Some(SmtValue::Bool(active)) =
        ctx.step
            .pool
            .active_at(bound.entity_name, bound.slot, ctx.step.step)
    else {
        nested_touched.extend(slot_touched);
        return Ok(smt::bool_const(true));
    };
    let active_branch = if op_parts.is_empty() {
        active.clone()
    } else {
        let mut parts = vec![active.clone()];
        parts.extend(op_parts);
        and_all(parts)
    };
    let mut inactive_parts = vec![legacy_inactive_slot_frame(ctx, bound, active)?];
    inactive_parts.extend(frame_specific_slots(
        ctx.step.pool,
        ctx.step.entities,
        &frame_targets,
        ctx.step.step,
    ));
    let inactive_branch = and_all(inactive_parts);
    nested_touched.extend(slot_touched);
    Ok(smt::bool_or(&[&active_branch, &inactive_branch]))
}

fn encode_legacy_bound_ops(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    base_params: &HashMap<String, SmtValue>,
    parts: &mut Vec<Bool>,
    nested_touched: &mut HashSet<(String, usize)>,
) -> Result<(), String> {
    let applies = legacy_bound_applies(bound.var, bound.ops);
    if applies.len() <= 1 {
        encode_legacy_single_bound_ops(ctx, bound, slot_ctx, base_params, parts, nested_touched)
    } else {
        encode_legacy_multi_bound_ops(ctx, state, bound, slot_ctx, &applies, parts, nested_touched)
    }
}

fn encode_legacy_single_bound_ops(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    base_params: &HashMap<String, SmtValue>,
    parts: &mut Vec<Bool>,
    nested_touched: &mut HashSet<(String, usize)>,
) -> Result<(), String> {
    for op in bound.ops {
        if let IRAction::Apply {
            target,
            transition,
            args,
            refs,
        } = op
        {
            if bound.kind == LegacyBoundKind::Choose || target == bound.var {
                encode_legacy_direct_bound_apply(
                    ctx, bound, slot_ctx, transition, args, refs, parts,
                )?;
                continue;
            }
        }
        let (nested_f, nested_t) = legacy_nested_op(ctx, bound, base_params, op)?;
        parts.extend(nested_f);
        nested_touched.extend(nested_t);
    }
    Ok(())
}

fn encode_legacy_direct_bound_apply(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    transition: &str,
    args: &[IRExpr],
    refs: &[String],
    parts: &mut Vec<Bool>,
) -> Result<(), String> {
    if let Some(trans) = bound
        .entity
        .transitions
        .iter()
        .find(|candidate| candidate.name == transition)
    {
        let action_params = try_build_apply_params(slot_ctx, trans, args, refs, ctx.step.step)?;
        parts.push(try_encode_action(
            ctx.step.pool,
            ctx.step.vctx,
            bound.entity,
            trans,
            bound.slot,
            ctx.step.step,
            &action_params,
        )?);
    }
    Ok(())
}

fn encode_legacy_multi_bound_ops(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    applies: &[LegacyBoundApply<'_>],
    parts: &mut Vec<Bool>,
    nested_touched: &mut HashSet<(String, usize)>,
) -> Result<(), String> {
    let chain = legacy_chain_state(ctx, state, bound, applies.len());
    for (index, apply) in applies.iter().enumerate() {
        encode_legacy_chain_apply(ctx, bound, slot_ctx, &chain, index, *apply, parts)?;
    }
    assert_legacy_chain_active(ctx, bound, parts);
    encode_legacy_multi_non_apply_ops(ctx, bound, &slot_ctx.params, parts, nested_touched)?;
    state.chain_id += 1;
    Ok(())
}

struct LegacyChainState {
    read_step: HashMap<String, SmtValue>,
    write_step: HashMap<String, SmtValue>,
    intermediates: Vec<HashMap<String, SmtValue>>,
}

fn legacy_chain_state(
    ctx: &LegacyActionCtx<'_>,
    state: &LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    n_applies: usize,
) -> LegacyChainState {
    LegacyChainState {
        read_step: legacy_field_values(
            ctx.step.pool,
            bound.entity_name,
            bound.entity,
            bound.slot,
            ctx.step.step,
        ),
        write_step: legacy_field_values(
            ctx.step.pool,
            bound.entity_name,
            bound.entity,
            bound.slot,
            ctx.step.step + 1,
        ),
        intermediates: (0..n_applies - 1)
            .map(|index| legacy_intermediate_values(ctx, state, bound, index))
            .collect(),
    }
}

fn encode_legacy_chain_apply(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    chain: &LegacyChainState,
    index: usize,
    apply: LegacyBoundApply<'_>,
    parts: &mut Vec<Bool>,
) -> Result<(), String> {
    let Some(trans) = bound
        .entity
        .transitions
        .iter()
        .find(|candidate| candidate.name == apply.transition)
    else {
        return Ok(());
    };
    let read_from = if index == 0 {
        &chain.read_step
    } else {
        &chain.intermediates[index - 1]
    };
    let write_to = if index == chain.intermediates.len() {
        &chain.write_step
    } else {
        &chain.intermediates[index]
    };
    let action_params =
        legacy_chain_apply_params(ctx, bound, slot_ctx, trans, index, apply, read_from)?;
    parts.push(try_encode_action_with_vars(
        bound.entity,
        trans,
        bound.slot,
        read_from,
        write_to,
        ctx.step.vctx,
        &action_params,
    )?);
    Ok(())
}

fn legacy_chain_apply_params(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    trans: &IRTransition,
    index: usize,
    apply: LegacyBoundApply<'_>,
    read_from: &HashMap<String, SmtValue>,
) -> Result<HashMap<String, SmtValue>, String> {
    if index == 0 {
        return try_build_apply_params(slot_ctx, trans, apply.args, apply.refs, ctx.step.step);
    }
    let mut params = HashMap::new();
    for (param_index, param) in trans.params.iter().enumerate() {
        if let Some(arg_expr) = apply.args.get(param_index) {
            let val = try_eval_expr_with_vars(
                arg_expr,
                bound.entity,
                read_from,
                ctx.step.vctx,
                &slot_ctx.params,
            )?;
            params.insert(param.name.clone(), val);
        }
    }
    // Wire refs (and any cross-entity qualified field bindings such as `m.y`)
    // exactly as the first apply does, so a later chained apply reading a
    // foreign ref field resolves it identically.
    wire_apply_refs(
        &mut params,
        slot_ctx,
        &trans.refs,
        apply.refs,
        ctx.step.step,
    );
    // Fallback: a ref naming one of the bound entity's own chained intermediate
    // fields resolves from the prior apply's write.
    for (ref_index, target_ref) in trans.refs.iter().enumerate() {
        if let Some(ref_name) = apply.refs.get(ref_index) {
            if !params.contains_key(&target_ref.name) {
                if let Some(val) = read_from.get(ref_name) {
                    params.insert(target_ref.name.clone(), val.clone());
                }
            }
        }
    }
    Ok(params)
}

fn encode_legacy_multi_non_apply_ops(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    base_params: &HashMap<String, SmtValue>,
    parts: &mut Vec<Bool>,
    nested_touched: &mut HashSet<(String, usize)>,
) -> Result<(), String> {
    for op in bound.ops {
        match op {
            IRAction::Apply { target, .. } if target == bound.var => {}
            IRAction::Apply { target, .. } if bound.kind == LegacyBoundKind::Choose => {
                return Err(format!(
                    "Apply target {target} does not match Choose var {} \
                     — cross-target Apply in Choose is not supported",
                    bound.var
                ));
            }
            _ => {
                let (nested_f, nested_t) = legacy_nested_op(ctx, bound, base_params, op)?;
                parts.extend(nested_f);
                nested_touched.extend(nested_t);
            }
        }
    }
    Ok(())
}

fn assert_legacy_chain_active(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    parts: &mut Vec<Bool>,
) {
    if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
        ctx.step
            .pool
            .active_at(bound.entity_name, bound.slot, ctx.step.step),
        ctx.step
            .pool
            .active_at(bound.entity_name, bound.slot, ctx.step.step + 1),
    ) {
        parts.push(curr.clone());
        parts.push(next.clone());
    }
}

fn legacy_bound_applies<'a>(bound_var: &str, ops: &'a [IRAction]) -> Vec<LegacyBoundApply<'a>> {
    ops.iter()
        // abide-audit: allow-silent-fallback -- iterator intentionally projects supported variants and drops nonmatching shapes
        .filter_map(|op| match op {
            IRAction::Apply {
                target,
                transition,
                args,
                refs,
            } if target == bound_var => Some(LegacyBoundApply {
                transition,
                args,
                refs,
            }),
            _ => None,
        })
        .collect()
}

fn legacy_nested_op(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    base_params: &HashMap<String, SmtValue>,
    op: &IRAction,
) -> Result<LegacyNestedEncoding, String> {
    try_encode_nested_op(
        NestedOpCtx {
            pool: ctx.step.pool,
            vctx: ctx.step.vctx,
            entities: ctx.step.entities,
            all_systems: ctx.step.all_systems,
            bound_var: bound.var,
            bound_ent_name: bound.entity_name,
            bound_entity_ir: bound.entity,
            bound_slot: bound.slot,
            step: ctx.step.step,
            base_params,
            depth: ctx.step.depth,
            outer_bindings: &[],
        },
        op,
    )
}

fn encode_legacy_apply(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    target: &str,
    transition: &str,
    args: &[IRExpr],
    refs: &[String],
) -> Result<(), String> {
    let entity = resolve_legacy_apply_entity(ctx, state, target, transition)?;
    let trans = entity
        .transitions
        .iter()
        .find(|candidate| candidate.name == transition)
        .ok_or_else(|| legacy_apply_transition_error(entity, transition))?;
    let n_slots = ctx.step.pool.slots_for(&entity.name);
    let target_param_eq = event_param_is_entity(target, &ctx.scope.entity_param_types)
        .then(|| state.step_params.get(target))
        .flatten();
    let mut slot_options = Vec::new();
    for slot in 0..n_slots {
        slot_options.push(encode_legacy_apply_slot(
            ctx,
            state,
            entity,
            trans,
            LegacyBoundApply {
                transition,
                args,
                refs,
            },
            target_param_eq,
            slot,
        )?);
    }
    if !slot_options.is_empty() {
        state.conjuncts.push(bool_or_all(slot_options));
    }
    state.mark_entity_slots(&entity.name, n_slots);
    Ok(())
}

fn resolve_legacy_apply_entity<'a>(
    ctx: &'a LegacyActionCtx<'_>,
    state: &LegacyStepState,
    target: &str,
    transition: &str,
) -> Result<&'a IREntity, String> {
    ctx.step
        .entities
        .iter()
        .find(|entity| entity.name == *target)
        .or_else(|| {
            state
                .var_to_entity
                .get(target)
                .and_then(|name| ctx.step.entities.iter().find(|entity| entity.name == *name))
        })
        .or_else(|| {
            let matches: Vec<_> = ctx
                .step
                .entities
                .iter()
                .filter(|entity| {
                    entity
                        .transitions
                        .iter()
                        .any(|candidate| candidate.name == *transition)
                })
                .collect();
            (matches.len() == 1).then(|| matches[0])
        })
        .ok_or_else(|| {
            format!(
                "Apply target resolution failed: target={target:?}, transition={transition:?} \
                 — could not resolve entity (var_to_entity keys: {:?}, entity names: {:?})",
                state.var_to_entity.keys().collect::<Vec<_>>(),
                ctx.step
                    .entities
                    .iter()
                    .map(|e| &e.name)
                    .collect::<Vec<_>>()
            )
        })
}

fn encode_legacy_apply_slot(
    ctx: &LegacyActionCtx<'_>,
    state: &LegacyStepState,
    entity: &IREntity,
    transition: &IRTransition,
    apply: LegacyBoundApply<'_>,
    target_param_eq: Option<&SmtValue>,
    slot: usize,
) -> Result<Bool, String> {
    let params = state.merged_params();
    let apply_ctx = legacy_slot_ctx(ctx, &entity.name, slot, params, "");
    let action_params = try_build_apply_params(
        &apply_ctx,
        transition,
        apply.args,
        apply.refs,
        ctx.step.step,
    )?;
    let mut parts = vec![try_encode_action(
        ctx.step.pool,
        ctx.step.vctx,
        entity,
        transition,
        slot,
        ctx.step.step,
        &action_params,
    )?];
    if let Some(param_val) = target_param_eq {
        parts.push(smt::smt_eq(
            param_val,
            // abide-audit: allow-silent-fallback -- bounded count or slot conversion intentionally collapses invalid capacity to zero
            &smt::int_val(i64::try_from(slot).unwrap_or(0)),
        )?);
    }
    parts.extend(frame_entity_slots_except(
        ctx.step.pool,
        entity,
        slot,
        ctx.step.step,
    ));
    Ok(and_all(parts))
}

fn legacy_apply_transition_error(entity: &IREntity, transition: &str) -> String {
    format!(
        "Apply transition not found: entity={}, transition={transition:?} \
         — available transitions: {:?}",
        entity.name,
        entity
            .transitions
            .iter()
            .map(|t| &t.name)
            .collect::<Vec<_>>()
    )
}

fn encode_legacy_create(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    entity_name: &str,
    fields: &[crate::ir::types::IRCreateField],
) -> Result<(), String> {
    let entity_ir = ctx.step.entities.iter().find(|e| e.name == *entity_name);
    let create_fields: Vec<(String, IRExpr)> = fields
        .iter()
        .map(|field| (field.name.clone(), field.value.clone()))
        .collect();
    state.conjuncts.push(try_encode_create(
        ctx.step.pool,
        ctx.step.vctx,
        entity_name,
        entity_ir,
        &create_fields,
        ctx.step.step,
        &state.step_params,
    )?);
    state.mark_entity_slots(entity_name, ctx.step.pool.slots_for(entity_name));
    Ok(())
}

fn encode_legacy_cross_call(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    target_system: &str,
    command_name: &str,
    cross_args: &[IRExpr],
) -> Result<(), String> {
    let Some(target_sys) = ctx
        .step
        .all_systems
        .iter()
        .find(|s| s.name == *target_system)
    else {
        return Ok(());
    };
    let mut branch_results = Vec::new();
    for target_step in target_sys
        .actions
        .iter()
        .filter(|s| s.name == *command_name)
    {
        branch_results.push(encode_legacy_cross_branch(
            ctx,
            state,
            target_step,
            cross_args,
        )?);
    }
    if branch_results.is_empty() {
        return Ok(());
    }
    let all_touched: HashSet<(String, usize)> = branch_results
        .iter()
        .flat_map(|(_, touched)| touched.iter().cloned())
        .collect();
    state.conjuncts.push(framed_branch_disjunction(
        ctx.step.pool,
        ctx.step.entities,
        ctx.step.step,
        branch_results,
        &all_touched,
    ));
    state.touched.extend(all_touched);
    Ok(())
}

fn encode_legacy_cross_branch(
    ctx: &LegacyActionCtx<'_>,
    state: &LegacyStepState,
    target_step: &IRSystemAction,
    cross_args: &[IRExpr],
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    if target_step.params.len() != cross_args.len() {
        return Ok((smt::bool_const(false), HashSet::new()));
    }
    let arg_ctx = legacy_slot_ctx(ctx, "", 0, state.merged_params(), "");
    let mut cross_params = HashMap::new();
    for (target_param, arg_expr) in target_step.params.iter().zip(cross_args.iter()) {
        let val = try_encode_slot_expr(&arg_ctx, arg_expr, ctx.step.step)?;
        cross_params.insert(target_param.name.clone(), val);
    }
    try_encode_step_inner(
        ctx.step.pool,
        ctx.step.vctx,
        ctx.step.entities,
        ctx.step.all_systems,
        target_step,
        ctx.step.step,
        StepEncodingOptions::with_override(ctx.step.depth + 1, cross_params),
    )
}

fn encode_legacy_expr_stmt(
    ctx: &LegacyActionCtx<'_>,
    state: &mut LegacyStepState,
    expr: &IRExpr,
) -> Result<(), String> {
    let expr_ctx = legacy_slot_ctx(
        ctx,
        "",
        0,
        state.merged_params(),
        &ctx.scope.owning_system_name,
    );
    state
        .conjuncts
        .push(try_encode_slot_expr(&expr_ctx, expr, ctx.step.step)?.to_bool()?);
    Ok(())
}

fn legacy_slot_ctx<'a>(
    ctx: &'a LegacyActionCtx<'a>,
    entity: &'a str,
    slot: usize,
    params: HashMap<String, SmtValue>,
    system_name: &'a str,
) -> SlotEncodeCtx<'a> {
    SlotEncodeCtx {
        pool: ctx.step.pool,
        vctx: ctx.step.vctx,
        entity,
        slot,
        params,
        bindings: HashMap::new(),
        system_name,
        entity_param_types: &ctx.scope.entity_param_types,
        store_param_types: &ctx.scope.store_param_types,
    }
}

fn legacy_inactive_slot_frame(
    ctx: &LegacyActionCtx<'_>,
    bound: LegacyBoundSlot<'_>,
    active: &Bool,
) -> Result<Bool, String> {
    let mut frame_parts = vec![smt::bool_not(active)];
    if let Some(SmtValue::Bool(next)) =
        ctx.step
            .pool
            .active_at(bound.entity_name, bound.slot, ctx.step.step + 1)
    {
        frame_parts.push(smt::bool_eq(next, active));
    }
    for field in &bound.entity.fields {
        if let (Some(curr), Some(next)) = (
            ctx.step
                .pool
                .field_at(bound.entity_name, bound.slot, &field.name, ctx.step.step),
            ctx.step.pool.field_at(
                bound.entity_name,
                bound.slot,
                &field.name,
                ctx.step.step + 1,
            ),
        ) {
            frame_parts.push(smt::smt_eq(curr, next)?);
        }
    }
    Ok(and_all(frame_parts))
}

fn legacy_field_values(
    pool: &SlotPool,
    entity_name: &str,
    entity: &IREntity,
    slot: usize,
    step: usize,
) -> HashMap<String, SmtValue> {
    entity
        .fields
        .iter()
        // abide-audit: allow-silent-fallback -- iterator intentionally projects supported variants and drops nonmatching shapes
        .filter_map(|field| {
            pool.field_at(entity_name, slot, &field.name, step)
                .map(|value| (field.name.clone(), value.clone()))
        })
        .collect()
}

fn legacy_intermediate_values(
    ctx: &LegacyActionCtx<'_>,
    state: &LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    index: usize,
) -> HashMap<String, SmtValue> {
    bound
        .entity
        .fields
        .iter()
        .map(|field| {
            let name = legacy_intermediate_name(ctx, state, bound, field, index);
            (
                field.name.clone(),
                legacy_fresh_field_value(&name, &field.ty),
            )
        })
        .collect()
}

fn legacy_intermediate_name(
    ctx: &LegacyActionCtx<'_>,
    state: &LegacyStepState,
    bound: LegacyBoundSlot<'_>,
    field: &crate::ir::types::IRField,
    index: usize,
) -> String {
    let label = if bound.kind == LegacyBoundKind::ForAll {
        format!("forall_ch{}", state.chain_id)
    } else {
        format!("ch{}", state.chain_id)
    };
    format!(
        "{}_s{}_{}_t{}_{}_inter{index}",
        bound.entity_name, bound.slot, field.name, ctx.step.step, label
    )
}

fn legacy_fresh_field_value(name: &str, ty: &IRType) -> SmtValue {
    match ty {
        IRType::Bool => smt::bool_var(name),
        IRType::Real | IRType::Float => smt::real_var(name),
        IRType::Map { .. } | IRType::Set { .. } => {
            smt::array_var(name, ty).expect("internal: array sort expected for Map/Set field")
        }
        IRType::Seq { element } => SmtValue::Dynamic(smt::dynamic_const(
            name,
            &smt::seq_sort(element.as_ref()).sort(),
        )),
        _ => smt::int_var(name),
    }
}

fn smt_value_eq(left: &SmtValue, right: &SmtValue) -> Option<Bool> {
    match (left, right) {
        (SmtValue::Int(l), SmtValue::Int(r)) => Some(smt::int_eq(l, r)),
        (SmtValue::Bool(l), SmtValue::Bool(r)) => Some(smt::bool_eq(l, r)),
        (SmtValue::Real(l), SmtValue::Real(r)) => Some(smt::real_eq(l, r)),
        _ => None,
    }
}

fn framed_branch_disjunction(
    pool: &SlotPool,
    entities: &[IREntity],
    step: usize,
    branch_results: Vec<(Bool, HashSet<(String, usize)>)>,
    all_touched: &HashSet<(String, usize)>,
) -> Bool {
    let disjuncts = branch_results
        .into_iter()
        .map(|(formula, branch_touched)| {
            let untouched: HashSet<(String, usize)> =
                all_touched.difference(&branch_touched).cloned().collect();
            if untouched.is_empty() {
                formula
            } else {
                let mut parts = vec![formula];
                parts.extend(frame_specific_slots(pool, entities, &untouched, step));
                and_all(parts)
            }
        })
        .collect();
    bool_or_all(disjuncts)
}

fn legacy_formula(conjuncts: Vec<Bool>) -> Bool {
    if conjuncts.is_empty() {
        smt::bool_const(true)
    } else {
        and_all(conjuncts)
    }
}

fn bool_or_all(disjuncts: Vec<Bool>) -> Bool {
    if disjuncts.is_empty() {
        smt::bool_const(false)
    } else {
        let refs: Vec<&Bool> = disjuncts.iter().collect();
        smt::bool_or(&refs)
    }
}

pub(super) fn try_encode_step_inner_branching(
    ctx: &StepEncodingCtx<'_>,
    event: &IRSystemAction,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    let branches = try_encode_step_branches_dispatch(ctx, event, override_params)?;
    let all_touched: HashSet<(String, usize)> = branches
        .iter()
        .flat_map(|b| b.touched.iter().cloned())
        .collect();
    let disjuncts: Vec<Bool> = branches
        .into_iter()
        .map(|branch| {
            let untouched_by_branch: HashSet<(String, usize)> =
                all_touched.difference(&branch.touched).cloned().collect();
            if untouched_by_branch.is_empty() {
                branch.formula
            } else {
                let frame =
                    frame_specific_slots(ctx.pool, ctx.entities, &untouched_by_branch, ctx.step);
                let mut parts = vec![branch.formula];
                parts.extend(frame);
                let refs: Vec<&Bool> = parts.iter().collect();
                smt::bool_and(&refs)
            }
        })
        .collect();
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Ok((
        if refs.is_empty() {
            smt::bool_const(false)
        } else {
            smt::bool_or(&refs)
        },
        all_touched,
    ))
}

pub(super) fn try_encode_step_branches_dispatch(
    ctx: &StepEncodingCtx<'_>,
    event: &IRSystemAction,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<Vec<MacroBranch>, String> {
    let step = ctx.step;
    let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
    let scope = step_scope_metadata(ctx.all_systems, event);

    if !contains_macro_actions(&event.body) {
        return encode_non_macro_step_branch(ctx, event, step_params, &scope);
    }

    let mut branches = vec![MacroBranch {
        formula: event_fire_precondition_formula(
            ctx.pool,
            ctx.vctx,
            event,
            ctx.step,
            &step_params,
            &scope,
        )?,
        touched: HashSet::new(),
        locals: HashMap::new(),
        return_value: None,
    }];
    let var_to_entity = scope.entity_param_types.clone();

    for action in &event.body {
        let action_ctx = MacroActionCtx {
            step: *ctx,
            step_params: &step_params,
            owning_system_name: &scope.owning_system_name,
            entity_param_types: &scope.entity_param_types,
            store_param_types: &scope.store_param_types,
            var_to_entity: &var_to_entity,
        };
        branches = try_apply_macro_action(&action_ctx, action, branches)?;
    }

    attach_macro_return_values(
        ctx,
        &scope,
        event.return_expr.as_ref(),
        &step_params,
        &mut branches,
    )?;

    Ok(branches)
}

pub(in crate::verify::harness) struct StepScopeMetadata {
    pub(in crate::verify::harness) owning_system_name: String,
    pub(in crate::verify::harness) entity_param_types: HashMap<String, String>,
    pub(in crate::verify::harness) store_param_types: HashMap<String, String>,
}

fn encode_non_macro_step_branch(
    ctx: &StepEncodingCtx<'_>,
    event: &IRSystemAction,
    step_params: HashMap<String, SmtValue>,
    scope: &StepScopeMetadata,
) -> Result<Vec<MacroBranch>, String> {
    let (formula, touched) = try_encode_step_inner_legacy(ctx, event, Some(step_params.clone()))?;
    let mut branch = MacroBranch {
        formula,
        touched,
        locals: HashMap::new(),
        return_value: None,
    };
    if let Some(ret) = &event.return_expr {
        attach_macro_return_value(ctx, scope, ret, step_params, &mut branch)?;
    }
    Ok(vec![branch])
}

pub(in crate::verify::harness) fn event_fire_precondition_formula(
    pool: &SlotPool,
    vctx: &VerifyContext,
    event: &IRSystemAction,
    step: usize,
    step_params: &HashMap<String, SmtValue>,
    scope: &StepScopeMetadata,
) -> Result<Bool, String> {
    let mut parts = step_param_domain_constraints(&event.params, step_params, vctx);
    if matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        if parts.is_empty() {
            return Ok(smt::bool_const(true));
        }
        let refs: Vec<&Bool> = parts.iter().collect();
        return Ok(smt::bool_and(&refs));
    }
    let guard = if scope.owning_system_name.is_empty() {
        try_encode_guard_expr(
            pool,
            vctx,
            &event.guard,
            step_params,
            &scope.store_param_types,
            step,
        )
    } else {
        try_encode_guard_expr_for_system(
            pool,
            vctx,
            &event.guard,
            step,
            SystemGuardScope {
                step_params,
                system_name: &scope.owning_system_name,
                entity_param_types: &scope.entity_param_types,
                store_param_types: &scope.store_param_types,
            },
        )
    }?;
    parts.push(guard);
    let refs: Vec<&Bool> = parts.iter().collect();
    Ok(smt::bool_and(&refs))
}

fn attach_macro_return_values(
    ctx: &StepEncodingCtx<'_>,
    scope: &StepScopeMetadata,
    ret: Option<&IRExpr>,
    step_params: &HashMap<String, SmtValue>,
    branches: &mut [MacroBranch],
) -> Result<(), String> {
    let Some(ret) = ret else {
        return Ok(());
    };
    for branch in branches {
        let params = merged_branch_params(step_params, &branch.locals);
        attach_macro_return_value(ctx, scope, ret, params, branch)?;
    }
    Ok(())
}

fn attach_macro_return_value(
    ctx: &StepEncodingCtx<'_>,
    scope: &StepScopeMetadata,
    ret: &IRExpr,
    params: HashMap<String, SmtValue>,
    branch: &mut MacroBranch,
) -> Result<(), String> {
    let value_ctx = macro_value_slot_ctx(ctx, scope, params);
    let (value, constraints) = try_encode_macro_value_expr(&value_ctx, ret, ctx.step)?;
    if !constraints.is_empty() {
        let mut parts = vec![branch.formula.clone()];
        parts.extend(constraints);
        let refs: Vec<&Bool> = parts.iter().collect();
        branch.formula = smt::bool_and(&refs);
    }
    branch.return_value = Some(value);
    Ok(())
}

fn macro_value_slot_ctx<'a>(
    ctx: &'a StepEncodingCtx<'a>,
    scope: &'a StepScopeMetadata,
    params: HashMap<String, SmtValue>,
) -> SlotEncodeCtx<'a> {
    SlotEncodeCtx {
        pool: ctx.pool,
        vctx: ctx.vctx,
        entity: "",
        slot: 0,
        params,
        bindings: HashMap::new(),
        system_name: &scope.owning_system_name,
        entity_param_types: &scope.entity_param_types,
        store_param_types: &scope.store_param_types,
    }
}

pub(in crate::verify::harness) fn step_scope_metadata(
    all_systems: &[IRSystem],
    event: &IRSystemAction,
) -> StepScopeMetadata {
    let owning_system = all_systems.iter().find(|s| {
        s.actions
            .iter()
            .any(|st| std::ptr::eq(st, event) || st.name == event.name)
    });
    // abide-audit: allow-silent-fallback -- empty collection/string is the documented neutral value for this path
    let owning_system_name = owning_system.map(|s| s.name.clone()).unwrap_or_default();
    let entity_param_types: HashMap<String, String> = event
        .params
        .iter()
        // abide-audit: allow-silent-fallback -- iterator intentionally projects supported variants and drops nonmatching shapes
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();
    let store_param_types: HashMap<String, String> = owning_system
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        // abide-audit: allow-silent-fallback -- empty collection/string is the documented neutral value for this path
        .unwrap_or_default();
    StepScopeMetadata {
        owning_system_name,
        entity_param_types,
        store_param_types,
    }
}

pub(super) fn merged_branch_params(
    step_params: &HashMap<String, SmtValue>,
    locals: &HashMap<String, SmtValue>,
) -> HashMap<String, SmtValue> {
    let mut params = step_params.clone();
    params.extend(locals.clone());
    params
}

pub(super) fn fresh_smt_value(prefix: &str, ty: &IRType) -> SmtValue {
    match ty {
        IRType::Bool => smt::bool_var(prefix),
        IRType::Real | IRType::Float => smt::real_var(prefix),
        IRType::Int | IRType::Identity => smt::int_var(prefix),
        _ => walkers::dynamic_to_smt_value(smt::dynamic_fresh(prefix, &smt::ir_type_to_sort(ty))),
    }
}

pub(crate) fn try_encode_macro_value_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<(SmtValue, Vec<Bool>), String> {
    match expr {
        IRExpr::Choose {
            var, predicate, ty, ..
        } => {
            let fresh = fresh_smt_value(&format!("choose_{var}_t{step}"), ty);
            let mut constraints = Vec::new();
            if let Some(pred) = predicate {
                let mut pred_params = ctx.params.clone();
                pred_params.insert(var.clone(), fresh.clone());
                pred_params.insert("$".to_owned(), fresh.clone());
                let pred_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: pred_params,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                constraints.push(try_encode_slot_expr(&pred_ctx, pred, step)?.to_bool()?);
            }
            Ok((fresh, constraints))
        }
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } if !args.is_empty() => {
            let Some(dt) = ctx.vctx.adt_sorts.get(enum_name) else {
                return Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new()));
            };
            let Some(variant) = dt
                .variants
                .iter()
                .find(|variant| smt::func_decl_name(&variant.constructor) == ctor.as_str())
            else {
                return Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new()));
            };
            let declared_names: Vec<String> =
                variant.accessors.iter().map(smt::func_decl_name).collect();
            let args_map: HashMap<&str, &IRExpr> = args
                .iter()
                .map(|(name, expr)| (name.as_str(), expr))
                .collect();
            for (field_name, _) in args {
                if !declared_names.iter().any(|name| name == field_name) {
                    return Err(format!(
                        "unknown field '{field_name}' in constructor '{ctor}' of '{enum_name}'"
                    ));
                }
            }

            let mut constraints = Vec::new();
            let mut z3_args: Vec<smt::Dynamic> = Vec::new();
            for name in &declared_names {
                let Some(field_expr) = args_map.get(name.as_str()) else {
                    return Err(format!(
                        "constructor '{ctor}' of '{enum_name}' is missing field '{name}'"
                    ));
                };
                let (value, mut field_constraints) =
                    try_encode_macro_value_expr(ctx, field_expr, step)?;
                constraints.append(&mut field_constraints);
                z3_args.push(value.to_dynamic());
            }
            let refs: Vec<&smt::Dynamic> = z3_args.iter().collect();
            let result = smt::func_decl_apply(&variant.constructor, &refs);
            Ok((walkers::dynamic_to_smt_value(result), constraints))
        }
        IRExpr::App { .. } => {
            let Some((enum_name, ctor, args)) = decompose_macro_ctor_app(expr) else {
                return Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new()));
            };
            let Some(dt) = ctx.vctx.adt_sorts.get(enum_name) else {
                return Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new()));
            };
            let Some(variant) = dt
                .variants
                .iter()
                .find(|variant| smt::func_decl_name(&variant.constructor) == ctor)
            else {
                return Err(format!("unknown constructor '{ctor}' of '{enum_name}'"));
            };
            if variant.accessors.len() != args.len() {
                return Err(format!(
                    "constructor '{ctor}' of '{enum_name}' expects {} argument(s), got {}",
                    variant.accessors.len(),
                    args.len()
                ));
            }

            let mut constraints = Vec::new();
            let mut z3_args: Vec<smt::Dynamic> = Vec::new();
            for arg in args {
                let (value, mut arg_constraints) = try_encode_macro_value_expr(ctx, arg, step)?;
                constraints.append(&mut arg_constraints);
                z3_args.push(value.to_dynamic());
            }
            let refs: Vec<&smt::Dynamic> = z3_args.iter().collect();
            let result = smt::func_decl_apply(&variant.constructor, &refs);
            Ok((walkers::dynamic_to_smt_value(result), constraints))
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut params = ctx.params.clone();
            let mut constraints = Vec::new();
            for binding in bindings {
                let bind_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: params.clone(),
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                let (value, cs) = try_encode_macro_value_expr(&bind_ctx, &binding.expr, step)?;
                constraints.extend(cs);
                params.insert(binding.name.clone(), value);
            }
            let body_ctx = SlotEncodeCtx {
                pool: ctx.pool,
                vctx: ctx.vctx,
                entity: ctx.entity,
                slot: ctx.slot,
                params,
                bindings: ctx.bindings.clone(),
                system_name: ctx.system_name,
                entity_param_types: ctx.entity_param_types,
                store_param_types: ctx.store_param_types,
            };
            let (value, mut body_constraints) = try_encode_macro_value_expr(&body_ctx, body, step)?;
            constraints.append(&mut body_constraints);
            Ok((value, constraints))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_bool = try_encode_slot_expr(ctx, cond, step)?.to_bool()?;
            let (then_val, then_constraints) = try_encode_macro_value_expr(ctx, then_body, step)?;
            let else_expr = else_body
                .as_ref()
                .ok_or_else(|| "macro-step return if/else requires an else branch".to_owned())?;
            let (else_val, else_constraints) = try_encode_macro_value_expr(ctx, else_expr, step)?;
            let result = smt::smt_ite(&cond_bool, &then_val, &else_val);
            let mut constraints = Vec::new();
            for c in then_constraints {
                constraints.push(smt::bool_implies(&cond_bool, &c));
            }
            let not_cond = smt::bool_not(&cond_bool);
            for c in else_constraints {
                constraints.push(smt::bool_implies(&not_cond, &c));
            }
            Ok((result, constraints))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let (scrut, mut constraints) = try_encode_macro_value_expr(ctx, scrutinee, step)?;
            let mut arm_conds = Vec::new();
            let mut result: Option<SmtValue> = None;
            for arm in arms.iter().rev() {
                let mut arm_env = ctx.params.clone();
                encode::bind_pattern_vars(&arm.pattern, &scrut, &mut arm_env, ctx.vctx)?;
                let arm_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: arm_env,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                let mut arm_cond =
                    encode::encode_pattern_cond(&scrut, &arm.pattern, &HashMap::new(), ctx.vctx)?;
                if let Some(guard) = &arm.guard {
                    let guard_bool = try_encode_slot_expr(&arm_ctx, guard, step)?.to_bool()?;
                    arm_cond = smt::bool_and(&[&arm_cond, &guard_bool]);
                }
                arm_conds.push(arm_cond.clone());
                let (arm_val, arm_constraints) =
                    try_encode_macro_value_expr(&arm_ctx, &arm.body, step)?;
                if let Some(current) = result.take() {
                    result = Some(smt::smt_ite(&arm_cond, &arm_val, &current));
                } else {
                    result = Some(arm_val);
                }
                for c in arm_constraints {
                    constraints.push(smt::bool_implies(&arm_cond, &c));
                }
            }
            if arm_conds.is_empty() {
                return Err("macro-step return match has no arms".to_owned());
            }
            let cond_refs: Vec<&Bool> = arm_conds.iter().collect();
            constraints.push(smt::bool_or(&cond_refs));
            Ok((result.expect("non-empty arms"), constraints))
        }
        _ => Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new())),
    }
}

fn decompose_macro_ctor_app(expr: &IRExpr) -> Option<(&str, &str, Vec<&IRExpr>)> {
    let mut args = Vec::new();
    let mut head = expr;
    while let IRExpr::App { func, arg, .. } = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    let IRExpr::Ctor {
        enum_name,
        ctor,
        args: named_args,
        ..
    } = head
    else {
        return None;
    };
    if !named_args.is_empty() {
        return None;
    }
    args.reverse();
    Some((enum_name, ctor, args))
}

pub(super) struct MacroActionCtx<'a> {
    step: StepEncodingCtx<'a>,
    step_params: &'a HashMap<String, SmtValue>,
    owning_system_name: &'a str,
    entity_param_types: &'a HashMap<String, String>,
    store_param_types: &'a HashMap<String, String>,
    var_to_entity: &'a HashMap<String, String>,
}

pub(super) fn try_apply_macro_action(
    ctx: &MacroActionCtx<'_>,
    action: &IRAction,
    branches: Vec<MacroBranch>,
) -> Result<Vec<MacroBranch>, String> {
    let step_params = ctx.step_params;

    let mut next = Vec::new();
    for branch in branches {
        let params = merged_branch_params(step_params, &branch.locals);
        match action {
            IRAction::Choose {
                var,
                entity,
                filter,
                ops,
            } => {
                apply_macro_choose(
                    ctx,
                    MacroChooseAction {
                        var,
                        entity,
                        filter,
                        ops,
                    },
                    &branch,
                    &params,
                    &mut next,
                )?;
            }
            IRAction::ForAll { .. } => {
                return Err(
                    "macro-step commands do not yet support for blocks in command bodies"
                        .to_owned(),
                );
            }
            IRAction::Create { entity, fields } => {
                apply_macro_create(ctx, entity, fields, &branch, &params, &mut next)?;
            }
            IRAction::ExprStmt { expr } => {
                apply_macro_expr_stmt(ctx, expr, &branch, params, &mut next)?;
            }
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                apply_macro_apply(
                    ctx,
                    MacroApplyAction {
                        target,
                        transition,
                        args,
                        refs: apply_refs,
                    },
                    &branch,
                    &params,
                    &mut next,
                )?;
            }
            IRAction::CrossCall {
                system,
                command,
                args,
            } => {
                apply_macro_cross_call(ctx, system, command, args, &branch, &params, &mut next)?;
            }
            IRAction::LetCrossCall {
                name,
                system,
                command,
                args,
            } => {
                apply_macro_let_cross_call(
                    ctx,
                    MacroLetCrossCall {
                        name,
                        system,
                        command,
                        args,
                    },
                    &branch,
                    &params,
                    &mut next,
                )?;
            }
            IRAction::Match { scrutinee, arms } => {
                apply_macro_match(ctx, scrutinee, arms, &branch, &params, &mut next)?;
            }
        }
    }
    Ok(next)
}

#[derive(Clone, Copy)]
struct MacroChooseAction<'a> {
    var: &'a str,
    entity: &'a str,
    filter: &'a IRExpr,
    ops: &'a [IRAction],
}

#[derive(Clone, Copy)]
struct MacroApplyAction<'a> {
    target: &'a str,
    transition: &'a str,
    args: &'a [IRExpr],
    refs: &'a [String],
}

struct MacroLetCrossCall<'a> {
    name: &'a str,
    system: &'a str,
    command: &'a str,
    args: &'a [IRExpr],
}

fn apply_macro_choose(
    ctx: &MacroActionCtx<'_>,
    choose: MacroChooseAction<'_>,
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let n_slots = ctx.step.pool.slots_for(choose.entity);
    let entity_ir = ctx.step.entities.iter().find(|e| e.name == *choose.entity);
    for slot in 0..n_slots {
        next.push(encode_macro_choose_slot(
            ctx, choose, branch, params, entity_ir, slot, n_slots,
        )?);
    }
    Ok(())
}

fn encode_macro_choose_slot(
    ctx: &MacroActionCtx<'_>,
    choose: MacroChooseAction<'_>,
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    entity_ir: Option<&IREntity>,
    slot: usize,
    n_slots: usize,
) -> Result<MacroBranch, String> {
    let pool = ctx.step.pool;
    let step = ctx.step.step;
    let slot_ctx = macro_action_slot_ctx(ctx, choose.entity, slot, params.clone());
    let mut conjuncts = vec![branch.formula.clone()];
    if let Some(SmtValue::Bool(active)) = pool.active_at(choose.entity, slot, step) {
        conjuncts.push(active.clone());
    }
    conjuncts.push(try_encode_slot_expr(&slot_ctx, choose.filter, step)?.to_bool()?);

    let mut touched = branch.touched.clone();
    let mut slot_has_action = false;
    let mut nested_touched = HashSet::new();
    if let Some(ent_ir) = entity_ir {
        encode_macro_choose_ops(
            ctx,
            choose,
            &slot_ctx,
            ent_ir,
            &mut ChooseSlotState {
                conjuncts: &mut conjuncts,
                touched: &mut touched,
                nested_touched: &mut nested_touched,
                slot_has_action: &mut slot_has_action,
            },
        )?;
        if !slot_has_action {
            conjuncts.extend(choose_slot_frame_self(pool, ent_ir, slot, step)?);
        }
        conjuncts.extend(frame_entity_slots_except(pool, ent_ir, slot, step));
    }

    touched.extend(nested_touched);
    for slot in 0..n_slots {
        touched.insert((choose.entity.to_owned(), slot));
    }
    Ok(MacroBranch {
        formula: and_all(conjuncts),
        touched,
        locals: branch.locals.clone(),
        return_value: branch.return_value.clone(),
    })
}

struct ChooseSlotState<'a> {
    conjuncts: &'a mut Vec<Bool>,
    touched: &'a mut HashSet<(String, usize)>,
    nested_touched: &'a mut HashSet<(String, usize)>,
    slot_has_action: &'a mut bool,
}

fn encode_macro_choose_ops(
    ctx: &MacroActionCtx<'_>,
    choose: MacroChooseAction<'_>,
    slot_ctx: &SlotEncodeCtx<'_>,
    entity_ir: &IREntity,
    state: &mut ChooseSlotState<'_>,
) -> Result<(), String> {
    for op in choose.ops {
        match op {
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } if target == choose.var => {
                if let Some(trans) = entity_ir
                    .transitions
                    .iter()
                    .find(|transition_ir| transition_ir.name == *transition)
                {
                    let action_params =
                        try_build_apply_params(slot_ctx, trans, args, apply_refs, ctx.step.step)?;
                    state.conjuncts.push(try_encode_action(
                        ctx.step.pool,
                        ctx.step.vctx,
                        entity_ir,
                        trans,
                        slot_ctx.slot,
                        ctx.step.step,
                        &action_params,
                    )?);
                    *state.slot_has_action = true;
                    state
                        .touched
                        .insert((choose.entity.to_owned(), slot_ctx.slot));
                }
            }
            _ => {
                let (nested_f, nested_slots) = try_encode_nested_op(
                    NestedOpCtx {
                        pool: ctx.step.pool,
                        vctx: ctx.step.vctx,
                        entities: ctx.step.entities,
                        all_systems: ctx.step.all_systems,
                        bound_var: choose.var,
                        bound_ent_name: choose.entity,
                        bound_entity_ir: entity_ir,
                        bound_slot: slot_ctx.slot,
                        step: ctx.step.step,
                        base_params: &slot_ctx.params,
                        depth: ctx.step.depth,
                        outer_bindings: &[],
                    },
                    op,
                )?;
                state.conjuncts.extend(nested_f);
                state.nested_touched.extend(nested_slots);
            }
        }
    }
    Ok(())
}

fn choose_slot_frame_self(
    pool: &SlotPool,
    entity: &IREntity,
    slot: usize,
    step: usize,
) -> Result<Vec<Bool>, String> {
    let mut conjuncts = Vec::new();
    for field in &entity.fields {
        if let (Some(curr), Some(next_val)) = (
            pool.field_at(&entity.name, slot, &field.name, step),
            pool.field_at(&entity.name, slot, &field.name, step + 1),
        ) {
            conjuncts.push(smt::smt_eq(curr, next_val)?);
        }
    }
    if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
        pool.active_at(&entity.name, slot, step),
        pool.active_at(&entity.name, slot, step + 1),
    ) {
        conjuncts.push(smt::bool_eq(act_next, act_curr));
    }
    Ok(conjuncts)
}

fn apply_macro_create(
    ctx: &MacroActionCtx<'_>,
    entity: &str,
    fields: &[crate::ir::types::IRCreateField],
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let entity_ir = ctx.step.entities.iter().find(|e| e.name == *entity);
    let create_fields: Vec<(String, IRExpr)> = fields
        .iter()
        .map(|field| (field.name.clone(), field.value.clone()))
        .collect();
    let create = try_encode_create(
        ctx.step.pool,
        ctx.step.vctx,
        entity,
        entity_ir,
        &create_fields,
        ctx.step.step,
        params,
    )?;
    let mut touched = branch.touched.clone();
    for slot in 0..ctx.step.pool.slots_for(entity) {
        touched.insert((entity.to_owned(), slot));
    }
    next.push(MacroBranch {
        formula: branch_and(branch, create),
        touched,
        locals: branch.locals.clone(),
        return_value: branch.return_value.clone(),
    });
    Ok(())
}

fn apply_macro_expr_stmt(
    ctx: &MacroActionCtx<'_>,
    expr: &IRExpr,
    branch: &MacroBranch,
    params: HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let expr_ctx = macro_action_slot_ctx(ctx, "", 0, params);
    let expr_bool = try_encode_slot_expr(&expr_ctx, expr, ctx.step.step)?.to_bool()?;
    next.push(MacroBranch {
        formula: branch_and(branch, expr_bool),
        touched: branch.touched.clone(),
        locals: branch.locals.clone(),
        return_value: branch.return_value.clone(),
    });
    Ok(())
}

fn apply_macro_apply(
    ctx: &MacroActionCtx<'_>,
    apply: MacroApplyAction<'_>,
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let ent = resolve_macro_apply_entity(ctx, apply.target, apply.transition)?;
    let trans = ent
        .transitions
        .iter()
        .find(|transition| transition.name == *apply.transition)
        .ok_or_else(|| {
            format!(
                "Apply transition not found in macro-step: entity={}, transition={}",
                ent.name, apply.transition
            )
        })?;
    let target_param_eq = event_param_is_entity(apply.target, ctx.entity_param_types)
        .then(|| params.get(apply.target))
        .flatten();
    for slot in 0..ctx.step.pool.slots_for(&ent.name) {
        next.push(encode_macro_apply_slot(
            ctx,
            MacroApplySlot {
                entity: ent,
                transition: trans,
                slot,
                target_param_eq,
            },
            apply,
            branch,
            params,
        )?);
    }
    Ok(())
}

struct MacroApplySlot<'a> {
    entity: &'a IREntity,
    transition: &'a IRTransition,
    slot: usize,
    target_param_eq: Option<&'a SmtValue>,
}

fn resolve_macro_apply_entity<'a>(
    ctx: &'a MacroActionCtx<'_>,
    target: &str,
    transition: &str,
) -> Result<&'a IREntity, String> {
    ctx.step
        .entities
        .iter()
        .find(|entity| entity.name == *target)
        .or_else(|| {
            ctx.var_to_entity
                .get(target)
                .and_then(|entity_name| ctx.step.entities.iter().find(|e| e.name == *entity_name))
        })
        .or_else(|| {
            let matches: Vec<_> = ctx
                .step
                .entities
                .iter()
                .filter(|entity| {
                    entity
                        .transitions
                        .iter()
                        .any(|transition_ir| transition_ir.name == *transition)
                })
                .collect();
            (matches.len() == 1).then(|| matches[0])
        })
        .ok_or_else(|| {
            format!(
                "Apply target resolution failed in macro-step: target={target}, transition={transition}"
            )
        })
}

fn encode_macro_apply_slot(
    ctx: &MacroActionCtx<'_>,
    slot: MacroApplySlot<'_>,
    apply: MacroApplyAction<'_>,
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
) -> Result<MacroBranch, String> {
    let apply_ctx = macro_action_slot_ctx(ctx, &slot.entity.name, slot.slot, params.clone());
    let action_params = try_build_apply_params(
        &apply_ctx,
        slot.transition,
        apply.args,
        apply.refs,
        ctx.step.step,
    )?;
    let mut parts = vec![
        branch.formula.clone(),
        try_encode_action(
            ctx.step.pool,
            ctx.step.vctx,
            slot.entity,
            slot.transition,
            slot.slot,
            ctx.step.step,
            &action_params,
        )?,
    ];
    if let Some(param_val) = slot.target_param_eq {
        parts.push(smt::smt_eq(
            param_val,
            // abide-audit: allow-silent-fallback -- bounded count or slot conversion intentionally collapses invalid capacity to zero
            &smt::int_val(i64::try_from(slot.slot).unwrap_or(0)),
        )?);
    }
    let mut touched = branch.touched.clone();
    for slot_idx in 0..ctx.step.pool.slots_for(&slot.entity.name) {
        touched.insert((slot.entity.name.clone(), slot_idx));
    }
    Ok(MacroBranch {
        formula: and_all(parts),
        touched,
        locals: branch.locals.clone(),
        return_value: branch.return_value.clone(),
    })
}

fn apply_macro_cross_call(
    ctx: &MacroActionCtx<'_>,
    system: &str,
    command: &str,
    args: &[IRExpr],
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let call_branches = try_encode_macro_call(ctx, system, command, args, params)?;
    for call_branch in call_branches {
        next.push(branch_with_macro_call(
            branch,
            &call_branch,
            branch.locals.clone(),
        ));
    }
    Ok(())
}

fn apply_macro_let_cross_call(
    ctx: &MacroActionCtx<'_>,
    call: MacroLetCrossCall<'_>,
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let call_branches = try_encode_macro_call(ctx, call.system, call.command, call.args, params)?;
    for call_branch in call_branches {
        let Some(value) = call_branch.return_value.clone() else {
            return Err(format!(
                "macro-step binding requires `{}::{}` to return a value",
                call.system, call.command
            ));
        };
        let mut locals = branch.locals.clone();
        locals.insert(call.name.to_owned(), value);
        next.push(branch_with_macro_call(branch, &call_branch, locals));
    }
    Ok(())
}

fn apply_macro_match(
    ctx: &MacroActionCtx<'_>,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    arms: &[crate::ir::types::IRActionMatchArm],
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<MacroBranch>,
) -> Result<(), String> {
    let call_branches = macro_match_scrutinee_branches(ctx, scrutinee, branch, params)?;
    for call_branch in call_branches {
        let Some(scrut) = call_branch.return_value.clone() else {
            return Err("macro-step match requires a returned command outcome".to_owned());
        };
        for arm in arms {
            next.extend(macro_match_arm_branches(
                ctx,
                arm,
                branch,
                &call_branch,
                &scrut,
                params,
            )?);
        }
    }
    Ok(())
}

fn macro_match_scrutinee_branches(
    ctx: &MacroActionCtx<'_>,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    branch: &MacroBranch,
    params: &HashMap<String, SmtValue>,
) -> Result<Vec<MacroBranch>, String> {
    match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => {
            let Some(value) = branch.locals.get(name).cloned() else {
                return Err(format!(
                    "macro-step match references unknown local `{name}`"
                ));
            };
            Ok(vec![MacroBranch {
                formula: smt::bool_const(true),
                touched: HashSet::new(),
                locals: HashMap::from([(name.clone(), value.clone())]),
                return_value: Some(value),
            }])
        }
        crate::ir::types::IRActionMatchScrutinee::CrossCall {
            system,
            command,
            args,
        } => try_encode_macro_call(ctx, system, command, args, params),
    }
}

fn macro_match_arm_branches(
    ctx: &MacroActionCtx<'_>,
    arm: &crate::ir::types::IRActionMatchArm,
    branch: &MacroBranch,
    call_branch: &MacroBranch,
    scrut: &SmtValue,
    params: &HashMap<String, SmtValue>,
) -> Result<Vec<MacroBranch>, String> {
    let arm_locals = macro_match_arm_locals(ctx, arm, branch, scrut)?;
    let arm_cond = macro_match_arm_condition(ctx, arm, scrut, params, &arm_locals)?;
    let mut arm_branches = vec![MacroBranch {
        formula: and_all(vec![
            branch.formula.clone(),
            call_branch.formula.clone(),
            arm_cond.clone(),
        ]),
        touched: {
            let mut touched = branch.touched.clone();
            touched.extend(call_branch.touched.clone());
            touched
        },
        locals: arm_locals,
        return_value: branch.return_value.clone(),
    }];
    // A div/mod in this arm's body is only evaluated when the arm is selected
    // (its pattern matches and any arm guard holds), so guard obligations
    // recorded while encoding the body by the arm condition — a divisor in a
    // non-taken match arm is not falsely flagged.
    crate::verify::property::push_harness_div_guard(arm_cond);
    let body_result = (|| {
        let mut branches = arm_branches;
        for nested in &arm.body {
            branches = try_apply_macro_action(ctx, nested, branches)?;
        }
        Ok::<Vec<MacroBranch>, String>(branches)
    })();
    crate::verify::property::pop_harness_div_guard();
    arm_branches = body_result?;
    Ok(arm_branches)
}

fn macro_match_arm_locals(
    ctx: &MacroActionCtx<'_>,
    arm: &crate::ir::types::IRActionMatchArm,
    branch: &MacroBranch,
    scrut: &SmtValue,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut arm_locals = branch.locals.clone();
    encode::bind_pattern_vars(&arm.pattern, scrut, &mut arm_locals, ctx.step.vctx)?;
    Ok(arm_locals)
}

fn macro_match_arm_condition(
    ctx: &MacroActionCtx<'_>,
    arm: &crate::ir::types::IRActionMatchArm,
    scrut: &SmtValue,
    params: &HashMap<String, SmtValue>,
    arm_locals: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    let mut arm_cond =
        encode::encode_pattern_cond(scrut, &arm.pattern, &HashMap::new(), ctx.step.vctx)?;
    if let Some(guard) = &arm.guard {
        let guard_ctx = macro_action_slot_ctx(ctx, "", 0, merged_branch_params(params, arm_locals));
        let guard_bool = try_encode_slot_expr(&guard_ctx, guard, ctx.step.step)?.to_bool()?;
        arm_cond = smt::bool_and(&[&arm_cond, &guard_bool]);
    }
    Ok(arm_cond)
}

fn macro_action_slot_ctx<'a>(
    ctx: &'a MacroActionCtx<'a>,
    entity: &'a str,
    slot: usize,
    params: HashMap<String, SmtValue>,
) -> SlotEncodeCtx<'a> {
    SlotEncodeCtx {
        pool: ctx.step.pool,
        vctx: ctx.step.vctx,
        entity,
        slot,
        params,
        bindings: HashMap::new(),
        system_name: ctx.owning_system_name,
        entity_param_types: ctx.entity_param_types,
        store_param_types: ctx.store_param_types,
    }
}

fn branch_with_macro_call(
    branch: &MacroBranch,
    call_branch: &MacroBranch,
    locals: HashMap<String, SmtValue>,
) -> MacroBranch {
    let mut touched = branch.touched.clone();
    touched.extend(call_branch.touched.clone());
    MacroBranch {
        formula: and_all(vec![branch.formula.clone(), call_branch.formula.clone()]),
        touched,
        locals,
        return_value: branch.return_value.clone(),
    }
}

fn branch_and(branch: &MacroBranch, formula: Bool) -> Bool {
    and_all(vec![branch.formula.clone(), formula])
}

fn and_all(parts: Vec<Bool>) -> Bool {
    let refs: Vec<&Bool> = parts.iter().collect();
    smt::bool_and(&refs)
}

pub(super) fn event_param_is_entity(
    target: &str,
    entity_param_types: &HashMap<String, String>,
) -> bool {
    entity_param_types.contains_key(target)
}

pub(super) fn try_encode_macro_call(
    ctx: &MacroActionCtx<'_>,
    target_system: &str,
    command_name: &str,
    cross_args: &[IRExpr],
    params: &HashMap<String, SmtValue>,
) -> Result<Vec<MacroBranch>, String> {
    let pool = ctx.step.pool;
    let vctx = ctx.step.vctx;
    let all_systems = ctx.step.all_systems;
    let step = ctx.step.step;

    let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) else {
        return Ok(vec![]);
    };
    let matching_steps: Vec<_> = target_sys
        .actions
        .iter()
        .filter(|s| s.name == *command_name)
        .collect();
    let arg_ctx = SlotEncodeCtx {
        pool,
        vctx,
        entity: "",
        slot: 0,
        params: params.clone(),
        bindings: HashMap::new(),
        system_name: ctx.owning_system_name,
        entity_param_types: ctx.entity_param_types,
        store_param_types: ctx.store_param_types,
    };
    let mut branches = Vec::new();
    for target_step in &matching_steps {
        if target_step.params.len() != cross_args.len() {
            continue;
        }
        let mut cross_params = HashMap::new();
        for (target_param, arg_expr) in target_step.params.iter().zip(cross_args.iter()) {
            let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
            cross_params.insert(target_param.name.clone(), val);
        }
        let cross_ctx = StepEncodingCtx {
            depth: ctx.step.depth + 1,
            ..ctx.step
        };
        branches.extend(try_encode_step_branches_dispatch(
            &cross_ctx,
            target_step,
            Some(cross_params),
        )?);
    }
    Ok(branches)
}
