use std::collections::{HashMap, HashSet};

use super::step::{event_fire_precondition_formula, step_scope_metadata};
use super::*;
use crate::verify::encode;

pub fn transition_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    step: usize,
    assumption_set: &IRAssumptionSet,
) -> Bool {
    try_transition_constraints(pool, vctx, entities, systems, step, assumption_set)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_transition_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    step: usize,
    assumption_set: &IRAssumptionSet,
) -> Result<Bool, String> {
    if step >= pool.bound {
        return Err(format!(
            "step {step} out of bounds for bound {}",
            pool.bound
        ));
    }

    let mut disjuncts = Vec::new();

    for system in systems {
        for event in &system.actions {
            let event_formula = try_encode_step(pool, vctx, entities, systems, event, step)?;
            let sys_frames =
                system_field_frame_conjuncts(pool, vctx, systems, system, &event.body, step);
            if sys_frames.is_empty() {
                disjuncts.push(event_formula);
            } else {
                let mut all = vec![event_formula];
                all.extend(sys_frames);
                let refs: Vec<&Bool> = all.iter().collect();
                disjuncts.push(smt::bool_and(&refs));
            }
        }
    }

    if assumption_set.stutter {
        let mut stutter_parts = vec![stutter_constraint(pool, entities, step)];
        for system in systems {
            if !system.fields.is_empty() {
                let empty_touched = HashSet::new();
                stutter_parts.extend(frame_system_fields(pool, system, &empty_touched, step));
            }
        }
        let refs: Vec<&Bool> = stutter_parts.iter().collect();
        disjuncts.push(smt::bool_and(&refs));
    }

    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Ok(smt::bool_or(&refs))
}

pub struct FireTracking {
    pub fire_vars: HashMap<(String, String), Vec<Bool>>,
    pub clause_fire_vars: HashMap<(String, String, usize), Vec<Bool>>,
    pub stutter_vars: Vec<Bool>,
    pub constraints: Vec<Bool>,
}

pub fn transition_constraints_with_fire(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
    assumption_set: &IRAssumptionSet,
) -> FireTracking {
    try_transition_constraints_with_fire(pool, vctx, entities, systems, bound, assumption_set)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_transition_constraints_with_fire(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    bound: usize,
    assumption_set: &IRAssumptionSet,
) -> Result<FireTracking, String> {
    let mut fire_vars: HashMap<(String, String), Vec<Bool>> = HashMap::new();
    let mut clause_fire_vars: HashMap<(String, String, usize), Vec<Bool>> = HashMap::new();
    let mut stutter_vars = Vec::new();
    let mut constraints = Vec::new();

    for system in systems {
        for (clause_idx, event) in system.actions.iter().enumerate() {
            let key = (system.name.clone(), event.name.clone());
            fire_vars.entry(key).or_default();
            clause_fire_vars
                .entry((system.name.clone(), event.name.clone(), clause_idx))
                .or_default();
        }
    }

    for step in 0..bound {
        let mut step_indicators: Vec<Bool> = Vec::new();
        let mut command_clauses: HashMap<(String, String), Vec<Bool>> = HashMap::new();

        for system in systems {
            for (clause_idx, event) in system.actions.iter().enumerate() {
                let key = (system.name.clone(), event.name.clone());
                let clause_fire_var = smt::bool_var(&format!(
                    "fire_{}_{}_c{}_t{step}",
                    system.name, event.name, clause_idx
                ));
                let clause_fire_bool = clause_fire_var
                    .to_bool()
                    .expect("internal: clause fire var");

                // Tie every div/mod well-definedness obligation recorded while
                // encoding this event to its clause-fire selector. The solver
                // asserts `clause_fire => event_formula`, so guarding the
                // obligation by `clause_fire` forces the whole event formula
                // (active slots, create-slot selection, choose/match branch
                // disjunctions) when the divisor is probed — a divisor in an
                // event that can never fire, or behind an unsatisfiable
                // branch, is no longer falsely flagged.
                crate::verify::property::push_harness_div_guard(clause_fire_bool.clone());
                let event_formula_result =
                    try_encode_step(pool, vctx, entities, systems, event, step);
                crate::verify::property::pop_harness_div_guard();
                let event_formula = event_formula_result?;
                let sys_frames =
                    system_field_frame_conjuncts(pool, vctx, systems, system, &event.body, step);
                let event_formula = if sys_frames.is_empty() {
                    event_formula
                } else {
                    let mut parts = vec![event_formula];
                    parts.extend(sys_frames);
                    let refs: Vec<&Bool> = parts.iter().collect();
                    smt::bool_and(&refs)
                };
                constraints.push(smt::bool_implies(&clause_fire_bool, &event_formula));

                command_clauses
                    .entry(key)
                    .or_default()
                    .push(clause_fire_bool.clone());
                clause_fire_vars
                    .get_mut(&(system.name.clone(), event.name.clone(), clause_idx))
                    .expect("clause fire key exists")
                    .push(clause_fire_bool.clone());
                step_indicators.push(clause_fire_bool);
            }
        }

        for (key, clause_bools) in command_clauses {
            let command_fire_var = smt::bool_var(&format!("fire_{}_{}_t{step}", key.0, key.1));
            let command_fire_bool = command_fire_var
                .to_bool()
                .expect("internal: command fire var");
            let clause_refs: Vec<&Bool> = clause_bools.iter().collect();
            let command_fired = smt::bool_or(&clause_refs);
            constraints.push(smt::bool_eq(&command_fire_bool, &command_fired));
            fire_vars
                .get_mut(&key)
                .expect("command fire key exists")
                .push(command_fire_bool);
        }

        if assumption_set.stutter {
            let stutter_var = smt::bool_var(&format!("stutter_t{step}"));
            let stutter_bool = stutter_var.to_bool().expect("internal: stutter var");
            let mut stutter_parts = vec![stutter_constraint(pool, entities, step)];
            for system in systems {
                if !system.fields.is_empty() {
                    let empty_touched = HashSet::new();
                    stutter_parts.extend(frame_system_fields(pool, system, &empty_touched, step));
                }
            }
            let stutter_refs: Vec<&Bool> = stutter_parts.iter().collect();
            let stutter_formula = smt::bool_and(&stutter_refs);
            constraints.push(smt::bool_implies(&stutter_bool, &stutter_formula));
            step_indicators.push(stutter_bool.clone());
            stutter_vars.push(stutter_bool);
        }

        let indicator_refs: Vec<&Bool> = step_indicators.iter().collect();
        constraints.push(smt::bool_or(&indicator_refs));
        for i in 0..step_indicators.len() {
            for j in (i + 1)..step_indicators.len() {
                constraints.push(smt::bool_not(&smt::bool_and(&[
                    &step_indicators[i],
                    &step_indicators[j],
                ])));
            }
        }
    }

    Ok(FireTracking {
        fire_vars,
        clause_fire_vars,
        stutter_vars,
        constraints,
    })
}

pub struct LassoLoop {
    pub loop_indicators: Vec<Bool>,
    pub constraints: Vec<Bool>,
}

pub fn lasso_loopback(pool: &SlotPool, entities: &[IREntity], systems: &[IRSystem]) -> LassoLoop {
    let bound = pool.bound;
    let mut loop_indicators = Vec::new();
    let mut constraints = Vec::new();

    for l in 0..bound {
        let indicator = smt::bool_var(&format!("loop_l_{l}"));
        let indicator_bool = indicator.to_bool().expect("internal: loop indicator");

        let mut equalities = Vec::new();
        for entity in entities {
            let n_slots = pool.slots_for(&entity.name);
            for slot in 0..n_slots {
                if let (Some(SmtValue::Bool(at_bound)), Some(SmtValue::Bool(at_l))) = (
                    pool.active_at(&entity.name, slot, bound),
                    pool.active_at(&entity.name, slot, l),
                ) {
                    equalities.push(smt::bool_eq(at_bound, at_l));
                }
                for field in &entity.fields {
                    if let (Some(val_bound), Some(val_l)) = (
                        pool.field_at(&entity.name, slot, &field.name, bound),
                        pool.field_at(&entity.name, slot, &field.name, l),
                    ) {
                        if let Ok(eq) = smt::smt_eq(val_bound, val_l) {
                            equalities.push(eq);
                        }
                    }
                }
            }
        }
        for system in systems {
            for field in &system.fields {
                if let (Some(val_bound), Some(val_l)) = (
                    pool.system_field_at(&system.name, &field.name, bound),
                    pool.system_field_at(&system.name, &field.name, l),
                ) {
                    if let Ok(eq) = smt::smt_eq(val_bound, val_l) {
                        equalities.push(eq);
                    }
                }
            }
        }

        if equalities.is_empty() {
            loop_indicators.push(indicator_bool);
            continue;
        }

        let eq_refs: Vec<&Bool> = equalities.iter().collect();
        let loopback_eq = smt::bool_and(&eq_refs);
        constraints.push(smt::bool_implies(&indicator_bool, &loopback_eq));
        loop_indicators.push(indicator_bool);
    }

    let ind_refs: Vec<&Bool> = loop_indicators.iter().collect();
    constraints.push(smt::bool_or(&ind_refs));
    for i in 0..loop_indicators.len() {
        for j in (i + 1)..loop_indicators.len() {
            constraints.push(smt::bool_not(&smt::bool_and(&[
                &loop_indicators[i],
                &loop_indicators[j],
            ])));
        }
    }

    LassoLoop {
        loop_indicators,
        constraints,
    }
}

pub fn encode_step_enabled(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
) -> Bool {
    try_encode_step_enabled(pool, vctx, entities, systems, event, step)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_encode_step_enabled(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
) -> Result<Bool, String> {
    try_encode_step_enabled_inner(
        pool,
        vctx,
        entities,
        systems,
        event,
        step,
        EnabledStepOptions::root(),
    )
}

#[allow(clippy::implicit_hasher)]
pub fn encode_step_enabled_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Bool {
    try_encode_step_enabled_with_params(pool, vctx, entities, systems, event, step, params)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_step_enabled_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    try_encode_step_enabled_inner(
        pool,
        vctx,
        entities,
        systems,
        event,
        step,
        EnabledStepOptions::with_override(params, 0),
    )
}

#[derive(Clone)]
struct EnabledBranch {
    formula: Bool,
    locals: HashMap<String, SmtValue>,
    return_value: Option<SmtValue>,
}

#[derive(Clone, Copy)]
struct EnabledEncodingCtx<'a> {
    pool: &'a SlotPool,
    vctx: &'a VerifyContext,
    entities: &'a [IREntity],
    systems: &'a [IRSystem],
    event: &'a IRSystemAction,
    step: usize,
    depth: usize,
}

struct EnabledStepOptions {
    override_params: Option<HashMap<String, SmtValue>>,
    depth: usize,
}

impl EnabledStepOptions {
    fn root() -> Self {
        Self {
            override_params: None,
            depth: 0,
        }
    }

    fn with_override(params: HashMap<String, SmtValue>, depth: usize) -> Self {
        Self {
            override_params: Some(params),
            depth,
        }
    }
}

struct EnabledMacroCtx<'a> {
    encoding: EnabledEncodingCtx<'a>,
    step_params: &'a HashMap<String, SmtValue>,
    owning_system_name: &'a str,
    entity_param_types: &'a HashMap<String, String>,
    store_param_types: &'a HashMap<String, String>,
}

fn enabled_body_contains_macro(actions: &[IRAction]) -> bool {
    actions.iter().any(|action| match action {
        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => true,
        IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
            enabled_body_contains_macro(ops)
        }
        _ => false,
    })
}

fn merged_enabled_params(
    params: &HashMap<String, SmtValue>,
    locals: &HashMap<String, SmtValue>,
) -> HashMap<String, SmtValue> {
    let mut merged = params.clone();
    merged.extend(locals.clone());
    merged
}

fn try_encode_enabled_nonmacro_action(
    ctx: &EnabledMacroCtx<'_>,
    action: &IRAction,
    params: HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    let encoding = ctx.encoding;
    let temp_event = IRSystemAction {
        name: encoding.event.name.clone(),
        params: encoding.event.params.clone(),
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![action.clone()],
        return_expr: None,
    };
    try_encode_step_enabled_inner(
        encoding.pool,
        encoding.vctx,
        encoding.entities,
        encoding.systems,
        &temp_event,
        encoding.step,
        EnabledStepOptions::with_override(params, encoding.depth + 1),
    )
}

fn try_encode_enabled_cross_call_branches(
    ctx: &EnabledMacroCtx<'_>,
    target_system: &str,
    command_name: &str,
    cross_args: &[IRExpr],
    params: &HashMap<String, SmtValue>,
) -> Result<Vec<EnabledBranch>, String> {
    let encoding = ctx.encoding;
    let pool = encoding.pool;
    let vctx = encoding.vctx;
    let step = encoding.step;
    let depth = encoding.depth;

    if depth >= 5 {
        return Ok(vec![]);
    }
    let Some(target_sys) = encoding
        .systems
        .iter()
        .find(|system| system.name == *target_system)
    else {
        return Ok(vec![]);
    };
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
    for target_step in target_sys
        .actions
        .iter()
        .filter(|target_step| target_step.name == *command_name)
    {
        if target_step.params.len() != cross_args.len() {
            continue;
        }
        let mut cross_params = HashMap::new();
        for (target_param, arg_expr) in target_step.params.iter().zip(cross_args.iter()) {
            let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
            cross_params.insert(target_param.name.clone(), val);
        }
        branches.extend(try_encode_enabled_branches_for_event(
            &EnabledEncodingCtx {
                event: target_step,
                depth: depth + 1,
                ..encoding
            },
            cross_params,
        )?);
    }
    Ok(branches)
}

fn try_apply_enabled_macro_action(
    ctx: &EnabledMacroCtx<'_>,
    action: &IRAction,
    branches: Vec<EnabledBranch>,
) -> Result<Vec<EnabledBranch>, String> {
    let step_params = ctx.step_params;

    let mut next = Vec::new();
    for branch in branches {
        let params = merged_enabled_params(step_params, &branch.locals);
        match action {
            IRAction::LetCrossCall {
                name,
                system,
                command,
                args,
            } => {
                apply_enabled_let_cross_call(
                    ctx,
                    EnabledLetCrossCall {
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
                apply_enabled_match(ctx, scrutinee, arms, &branch, &params, &mut next)?;
            }
            IRAction::CrossCall {
                system,
                command,
                args,
            } => {
                apply_enabled_cross_call(ctx, system, command, args, &branch, &params, &mut next)?;
            }
            IRAction::ExprStmt { expr } => {
                apply_enabled_expr_stmt(ctx, expr, &branch, params, &mut next)?;
            }
            _ => {
                apply_enabled_nonmacro_action(ctx, action, &branch, params, &mut next)?;
            }
        }
    }
    Ok(next)
}

struct EnabledLetCrossCall<'a> {
    name: &'a str,
    system: &'a str,
    command: &'a str,
    args: &'a [IRExpr],
}

fn apply_enabled_let_cross_call(
    ctx: &EnabledMacroCtx<'_>,
    call: EnabledLetCrossCall<'_>,
    branch: &EnabledBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<EnabledBranch>,
) -> Result<(), String> {
    let call_branches =
        try_encode_enabled_cross_call_branches(ctx, call.system, call.command, call.args, params)?;
    for call_branch in call_branches {
        let Some(value) = call_branch.return_value.clone() else {
            return Err(format!(
                "macro-step binding requires `{}::{}` to return a value",
                call.system, call.command
            ));
        };
        let mut locals = branch.locals.clone();
        locals.insert(call.name.to_owned(), value);
        next.push(EnabledBranch {
            formula: branch_call_formula(branch, &call_branch),
            locals,
            return_value: branch.return_value.clone(),
        });
    }
    Ok(())
}

fn apply_enabled_match(
    ctx: &EnabledMacroCtx<'_>,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    arms: &[crate::ir::types::IRActionMatchArm],
    branch: &EnabledBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<EnabledBranch>,
) -> Result<(), String> {
    let call_branches = enabled_match_scrutinee_branches(ctx, scrutinee, branch, params)?;
    for call_branch in call_branches {
        let Some(scrut) = call_branch.return_value.clone() else {
            return Err("macro-step match requires a returned command outcome".to_owned());
        };
        for arm in arms {
            next.extend(apply_enabled_match_arm(
                ctx,
                arm,
                branch,
                &call_branch,
                &scrut,
            )?);
        }
    }
    Ok(())
}

fn enabled_match_scrutinee_branches(
    ctx: &EnabledMacroCtx<'_>,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    branch: &EnabledBranch,
    params: &HashMap<String, SmtValue>,
) -> Result<Vec<EnabledBranch>, String> {
    match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => {
            let Some(value) = branch.locals.get(name).cloned() else {
                return Err(format!(
                    "macro-step match references unknown local `{name}`"
                ));
            };
            Ok(vec![EnabledBranch {
                formula: smt::bool_const(true),
                locals: HashMap::new(),
                return_value: Some(value),
            }])
        }
        crate::ir::types::IRActionMatchScrutinee::CrossCall {
            system,
            command,
            args,
        } => try_encode_enabled_cross_call_branches(ctx, system, command, args, params),
    }
}

fn apply_enabled_match_arm(
    ctx: &EnabledMacroCtx<'_>,
    arm: &crate::ir::types::IRActionMatchArm,
    branch: &EnabledBranch,
    call_branch: &EnabledBranch,
    scrut: &SmtValue,
) -> Result<Vec<EnabledBranch>, String> {
    let arm_cond = enabled_match_arm_condition(ctx, arm, branch, scrut)?;
    let mut arm_branches = vec![EnabledBranch {
        formula: smt::bool_and(&[&branch.formula, &call_branch.formula, &arm_cond]),
        locals: enabled_match_arm_locals(ctx, arm, branch, scrut)?,
        return_value: branch.return_value.clone(),
    }];
    for nested in &arm.body {
        arm_branches = try_apply_enabled_macro_action(ctx, nested, arm_branches)?;
    }
    Ok(arm_branches)
}

fn enabled_match_arm_locals(
    ctx: &EnabledMacroCtx<'_>,
    arm: &crate::ir::types::IRActionMatchArm,
    branch: &EnabledBranch,
    scrut: &SmtValue,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut arm_locals = branch.locals.clone();
    encode::bind_pattern_vars(&arm.pattern, scrut, &mut arm_locals, ctx.encoding.vctx)?;
    Ok(arm_locals)
}

fn enabled_match_arm_condition(
    ctx: &EnabledMacroCtx<'_>,
    arm: &crate::ir::types::IRActionMatchArm,
    branch: &EnabledBranch,
    scrut: &SmtValue,
) -> Result<Bool, String> {
    let mut arm_cond =
        encode::encode_pattern_cond(scrut, &arm.pattern, &HashMap::new(), ctx.encoding.vctx)?;
    if let Some(guard) = &arm.guard {
        let arm_locals = enabled_match_arm_locals(ctx, arm, branch, scrut)?;
        let guard_ctx = enabled_slot_ctx(ctx, merged_enabled_params(ctx.step_params, &arm_locals));
        arm_cond = smt::bool_and(&[
            &arm_cond,
            &try_encode_slot_expr(&guard_ctx, guard, ctx.encoding.step)?.to_bool()?,
        ]);
    }
    Ok(arm_cond)
}

fn apply_enabled_cross_call(
    ctx: &EnabledMacroCtx<'_>,
    system: &str,
    command: &str,
    args: &[IRExpr],
    branch: &EnabledBranch,
    params: &HashMap<String, SmtValue>,
    next: &mut Vec<EnabledBranch>,
) -> Result<(), String> {
    let call_branches = try_encode_enabled_cross_call_branches(ctx, system, command, args, params)?;
    for call_branch in call_branches {
        next.push(EnabledBranch {
            formula: branch_call_formula(branch, &call_branch),
            locals: branch.locals.clone(),
            return_value: branch.return_value.clone(),
        });
    }
    Ok(())
}

fn apply_enabled_expr_stmt(
    ctx: &EnabledMacroCtx<'_>,
    expr: &IRExpr,
    branch: &EnabledBranch,
    params: HashMap<String, SmtValue>,
    next: &mut Vec<EnabledBranch>,
) -> Result<(), String> {
    let slot_ctx = enabled_slot_ctx(ctx, params);
    let formula = try_encode_slot_expr(&slot_ctx, expr, ctx.encoding.step)?.to_bool()?;
    next.push(branch_with_formula(branch, &formula));
    Ok(())
}

fn apply_enabled_nonmacro_action(
    ctx: &EnabledMacroCtx<'_>,
    action: &IRAction,
    branch: &EnabledBranch,
    params: HashMap<String, SmtValue>,
    next: &mut Vec<EnabledBranch>,
) -> Result<(), String> {
    let formula = try_encode_enabled_nonmacro_action(ctx, action, params)?;
    next.push(branch_with_formula(branch, &formula));
    Ok(())
}

fn enabled_slot_ctx<'a>(
    ctx: &'a EnabledMacroCtx<'a>,
    params: HashMap<String, SmtValue>,
) -> SlotEncodeCtx<'a> {
    SlotEncodeCtx {
        pool: ctx.encoding.pool,
        vctx: ctx.encoding.vctx,
        entity: "",
        slot: 0,
        params,
        bindings: HashMap::new(),
        system_name: ctx.owning_system_name,
        entity_param_types: ctx.entity_param_types,
        store_param_types: ctx.store_param_types,
    }
}

fn branch_call_formula(branch: &EnabledBranch, call_branch: &EnabledBranch) -> Bool {
    smt::bool_and(&[&branch.formula, &call_branch.formula])
}

fn branch_with_formula(branch: &EnabledBranch, formula: &Bool) -> EnabledBranch {
    EnabledBranch {
        formula: smt::bool_and(&[&branch.formula, formula]),
        locals: branch.locals.clone(),
        return_value: branch.return_value.clone(),
    }
}

fn try_encode_enabled_branches_for_event(
    ctx: &EnabledEncodingCtx<'_>,
    step_params: HashMap<String, SmtValue>,
) -> Result<Vec<EnabledBranch>, String> {
    let pool = ctx.pool;
    let vctx = ctx.vctx;
    let systems = ctx.systems;
    let event = ctx.event;
    let step = ctx.step;

    let scope = step_scope_metadata(systems, event);
    let initial_formula =
        event_fire_precondition_formula(pool, vctx, event, step, &step_params, &scope)?;
    let mut branches = vec![EnabledBranch {
        formula: initial_formula,
        locals: HashMap::new(),
        return_value: None,
    }];
    for action in &event.body {
        let macro_ctx = EnabledMacroCtx {
            encoding: *ctx,
            step_params: &step_params,
            owning_system_name: &scope.owning_system_name,
            entity_param_types: &scope.entity_param_types,
            store_param_types: &scope.store_param_types,
        };
        branches = try_apply_enabled_macro_action(&macro_ctx, action, branches)?;
    }
    if let Some(ret) = &event.return_expr {
        for branch in &mut branches {
            let ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: merged_enabled_params(&step_params, &branch.locals),
                bindings: HashMap::new(),
                system_name: &scope.owning_system_name,
                entity_param_types: &scope.entity_param_types,
                store_param_types: &scope.store_param_types,
            };
            let (value, constraints) = try_encode_macro_value_expr(&ctx, ret, step)?;
            if !constraints.is_empty() {
                let mut parts = vec![branch.formula.clone()];
                parts.extend(constraints);
                let refs: Vec<&Bool> = parts.iter().collect();
                branch.formula = smt::bool_and(&refs);
            }
            branch.return_value = Some(value);
        }
    }
    Ok(branches)
}

#[allow(dead_code)]
fn encode_step_enabled_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    options: EnabledStepOptions,
) -> Bool {
    try_encode_step_enabled_inner(pool, vctx, entities, systems, event, step, options)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

fn try_encode_step_enabled_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRSystemAction,
    step: usize,
    options: EnabledStepOptions,
) -> Result<Bool, String> {
    let mut conditions = Vec::new();

    let depth = options.depth;
    let params = options
        .override_params
        .unwrap_or_else(|| build_step_params(&event.params, step));
    let scope = step_scope_metadata(systems, event);
    if enabled_body_contains_macro(&event.body) {
        let ctx = EnabledEncodingCtx {
            pool,
            vctx,
            entities,
            systems,
            event,
            step,
            depth,
        };
        let branches = try_encode_enabled_branches_for_event(&ctx, params)?;
        if branches.is_empty() {
            return Ok(smt::bool_const(false));
        }
        let formulas: Vec<Bool> = branches.into_iter().map(|branch| branch.formula).collect();
        let refs: Vec<&Bool> = formulas.iter().collect();
        return Ok(smt::bool_or(&refs));
    }
    conditions.push(event_fire_precondition_formula(
        pool, vctx, event, step, &params, &scope,
    )?);

    for action in &event.body {
        match action {
            IRAction::Choose {
                entity: ent_name,
                filter,
                ..
            } => {
                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let mut slot_disjuncts = Vec::new();
                for slot in 0..n_slots {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        if entity_ir.is_some() {
                            let ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: ent_name,
                                slot,
                                params: params.clone(),
                                bindings: HashMap::new(),
                                system_name: &scope.owning_system_name,
                                entity_param_types: &scope.entity_param_types,
                                store_param_types: &scope.store_param_types,
                            };
                            let filt = try_encode_slot_expr(&ctx, filter, step)?;
                            let filt_bool = filt.to_bool()?;
                            slot_disjuncts.push(smt::bool_and(&[active, &filt_bool]));
                        }
                    }
                }
                if slot_disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => unreachable!(),
            IRAction::Create {
                entity: ent_name, ..
            } => {
                let n_slots = pool.slots_for(ent_name);
                let mut slot_disjuncts = Vec::new();
                for slot in 0..n_slots {
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        slot_disjuncts.push(smt::bool_not(active));
                    }
                }
                if slot_disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    let from_param = event.params.iter().find_map(|p| {
                        if p.name == *target {
                            if let IRType::Entity { name } = &p.ty {
                                return Some(name.as_str());
                            }
                        }
                        None
                    });
                    if let Some(entity_name) = from_param {
                        return entities.iter().find(|e| e.name == entity_name);
                    }
                    let matches: Vec<_> = entities
                        .iter()
                        .filter(|e| e.transitions.iter().any(|t| t.name == *transition))
                        .collect();
                    if matches.len() == 1 {
                        Some(matches[0])
                    } else {
                        None
                    }
                });
                let Some(ent) = resolved_entity else {
                    continue;
                };
                let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) else {
                    continue;
                };

                let target_param_eq: Option<&SmtValue> = if event
                    .params
                    .iter()
                    .any(|p| p.name == *target && matches!(p.ty, IRType::Entity { .. }))
                {
                    params.get(target.as_str())
                } else {
                    None
                };

                let n_slots = pool.slots_for(&ent.name);
                let mut slot_disjuncts = Vec::new();
                for slot in 0..n_slots {
                    let mut conjuncts = Vec::new();
                    if let Some(SmtValue::Bool(active)) = pool.active_at(&ent.name, slot, step) {
                        conjuncts.push(active.clone());
                    } else {
                        continue;
                    }

                    let slot_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: &ent.name,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: &scope.owning_system_name,
                        entity_param_types: &scope.entity_param_types,
                        store_param_types: &scope.store_param_types,
                    };
                    let action_params =
                        try_build_apply_params(&slot_ctx, trans, args, apply_refs, step)?;
                    let action_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: &ent.name,
                        slot,
                        params: action_params,
                        bindings: HashMap::new(),
                        system_name: &scope.owning_system_name,
                        entity_param_types: &scope.entity_param_types,
                        store_param_types: &scope.store_param_types,
                    };
                    let guard_val = try_encode_slot_expr(&action_ctx, &trans.guard, step)?;
                    let guard_bool = guard_val.to_bool()?;
                    conjuncts.push(guard_bool);

                    if let Some(param_val) = target_param_eq {
                        #[allow(clippy::cast_possible_wrap)]
                        let slot_val = smt::int_val(slot as i64);
                        if let Ok(eq) = smt::smt_eq(param_val, &slot_val) {
                            conjuncts.push(eq);
                        }
                    }

                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    slot_disjuncts.push(smt::bool_and(&refs));
                }
                if slot_disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::ForAll { .. } => {}
            IRAction::CrossCall {
                system: sys_name,
                command: cmd_name,
                args: cross_args,
            } => {
                if depth < 5 {
                    if let Some(target_sys) = systems.iter().find(|s| s.name == *sys_name) {
                        let matching: Vec<&IRSystemAction> = target_sys
                            .actions
                            .iter()
                            .filter(|s| s.name == *cmd_name)
                            .collect();
                        if !matching.is_empty() {
                            let empty_ept: HashMap<String, String> = HashMap::new();
                            let clause_bools: Vec<Bool> = matching
                                .iter()
                                .filter(|target_step| target_step.params.len() == cross_args.len())
                                .map(|target_step| {
                                    let arg_ctx = SlotEncodeCtx {
                                        pool,
                                        vctx,
                                        entity: "",
                                        slot: 0,
                                        params: params.clone(),
                                        bindings: HashMap::new(),
                                        system_name: "",
                                        entity_param_types: &empty_ept,
                                        store_param_types: &empty_ept,
                                    };
                                    let mut cross_params: HashMap<String, SmtValue> =
                                        HashMap::new();
                                    for (target_param, arg_expr) in
                                        target_step.params.iter().zip(cross_args.iter())
                                    {
                                        let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
                                        cross_params.insert(target_param.name.clone(), val);
                                    }
                                    try_encode_step_enabled_inner(
                                        pool,
                                        vctx,
                                        entities,
                                        systems,
                                        target_step,
                                        step,
                                        EnabledStepOptions::with_override(cross_params, depth + 1),
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?;
                            if !clause_bools.is_empty() {
                                let refs: Vec<&Bool> = clause_bools.iter().collect();
                                conditions.push(smt::bool_or(&refs));
                            }
                        }
                    }
                }
            }
            IRAction::ExprStmt { expr } => {
                let empty_spt: HashMap<String, String> = HashMap::new();
                let val = try_encode_guard_expr(pool, vctx, expr, &params, &empty_spt, step)?;
                conditions.push(val);
            }
        }
    }

    if conditions.is_empty() {
        Ok(smt::bool_const(true))
    } else {
        let refs: Vec<&Bool> = conditions.iter().collect();
        Ok(smt::bool_and(&refs))
    }
}
