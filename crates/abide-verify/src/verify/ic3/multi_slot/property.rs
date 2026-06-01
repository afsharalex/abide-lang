use super::*;

type Ic3MatchBindings = Vec<(String, String)>;

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct Ic3SlotBinding<'a> {
    pub(in crate::verify::ic3) var: &'a str,
    pub(in crate::verify::ic3) slot: usize,
}

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct Ic3TwoSlotPropertyCtx<'a> {
    pub(in crate::verify::ic3) entity: &'a IREntity,
    pub(in crate::verify::ic3) vctx: &'a VerifyContext,
    pub(in crate::verify::ic3) left: Ic3SlotBinding<'a>,
    pub(in crate::verify::ic3) right: Ic3SlotBinding<'a>,
    pub(in crate::verify::ic3) n_slots: usize,
}

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct Ic3SingleSlotPropertyCtx<'a> {
    pub(in crate::verify::ic3) entity: &'a IREntity,
    pub(in crate::verify::ic3) vctx: &'a VerifyContext,
    pub(in crate::verify::ic3) slot: usize,
    pub(in crate::verify::ic3) n_slots: usize,
}

/// Negate a property for multi-slot encoding.
///
/// For `all o: Order | P(o)`, violation means some active slot violates `P`.
/// For nested entity quantifiers, violation ranges over active slot pairs.
pub(in crate::verify::ic3) fn negate_property_smt_multi(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    n_slots: usize,
) -> Result<String, String> {
    match property {
        IRExpr::Always { body, .. } => negate_property_smt_multi(body, entity, vctx, n_slots),
        IRExpr::Forall {
            var,
            domain: IRType::Entity { .. },
            body,
            ..
        } => {
            // Check if body is another Forall (nested inter-entity quantifier)
            if let IRExpr::Forall {
                var: var2,
                domain: IRType::Entity { .. },
                body: inner_body,
                ..
            } = body.as_ref()
            {
                // Nested: all a | all b | P(a, b)
                // Violation: ∃ s1, s2 | active(s1) ∧ active(s2) ∧ ¬P(s1, s2)
                let mut disjuncts = Vec::new();
                for s1 in 0..n_slots {
                    for s2 in 0..n_slots {
                        let neg = negate_inner_property_two_slots(
                            inner_body,
                            Ic3TwoSlotPropertyCtx {
                                entity,
                                vctx,
                                left: Ic3SlotBinding {
                                    var: var.as_str(),
                                    slot: s1,
                                },
                                right: Ic3SlotBinding {
                                    var: var2.as_str(),
                                    slot: s2,
                                },
                                n_slots,
                            },
                        )?;
                        disjuncts.push(format!("(and s{s1}_active s{s2}_active {neg})"));
                    }
                }
                return Ok(format!("(or {})", disjuncts.join(" ")));
            }

            // Single quantifier: all o: E | P(o)
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg = negate_inner_property_slot(body, entity, vctx, slot, n_slots)?;
                disjuncts.push(format!("(and s{slot}_active {neg})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
        _ => {
            // Non-quantified property: check against all active slots
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg = negate_inner_property_slot(property, entity, vctx, slot, n_slots)?;
                disjuncts.push(format!("(and s{slot}_active {neg})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
    }
}

/// Negate an inner property with two bound variables mapped to two slots.
/// For `P(a, b)` where a → slot s1 and b → slot s2.
pub(in crate::verify::ic3) fn negate_inner_property_two_slots(
    property: &IRExpr,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
) -> Result<String, String> {
    let pos = guard_to_smt_two_slots(property, ctx)?;
    Ok(format!("(not {pos})"))
}

/// Encode a guard with two slot bindings (for inter-entity properties).
pub(in crate::verify::ic3) fn guard_to_smt_two_slots(
    expr: &IRExpr,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
) -> Result<String, String> {
    guard_to_smt_two_slots_scoped(expr, ctx, &HashSet::new(), &Ic3SlotEntityLocals::new())
}

pub(in crate::verify::ic3) fn guard_let_to_smt_two_slots_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let entity = ctx.entity;
    let vctx = ctx.vctx;
    let var1 = ctx.left.var;
    let slot1 = ctx.left.slot;
    let var2 = ctx.right.var;
    let slot2 = ctx.right.slot;
    let n_slots = ctx.n_slots;

    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_two_slots_scoped(body, ctx, locals, entity_locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        if let IRType::Entity { name } = domain {
            if name == &entity.name {
                let mut disjuncts = Vec::new();
                for chosen_slot in 0..n_slots {
                    let active = format!("s{chosen_slot}_active");
                    let mut pred_entity_locals = entity_locals.clone();
                    pred_entity_locals.insert(var.clone(), chosen_slot);
                    let pred = if let Some(predicate) = predicate {
                        guard_to_smt_two_slots_scoped(predicate, ctx, locals, &pred_entity_locals)?
                    } else {
                        "true".to_owned()
                    };
                    let mut rest_entity_locals = entity_locals.clone();
                    rest_entity_locals.insert(binding.name.clone(), chosen_slot);
                    let rest_smt = guard_let_to_smt_two_slots_scoped(
                        rest,
                        body,
                        ctx,
                        locals,
                        &rest_entity_locals,
                    )?;
                    disjuncts.push(format!("(and {active} {pred} {rest_smt})"));
                }
                return if disjuncts.is_empty() {
                    Ok("false".to_owned())
                } else {
                    Ok(format!("(or {})", disjuncts.join(" ")))
                };
            }
        }
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate: &IRExpr, scope: &HashSet<String>| {
                guard_to_smt_two_slots_scoped(predicate, ctx, scope, entity_locals)
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_two_slots_scoped(rest, body, ctx, &scope, entity_locals)?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            Ic3DirectChooseInput {
                var,
                domain,
                predicate: predicate.as_deref(),
                locals,
            },
            Ic3DirectChooseHooks {
                encode_term: |term: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_two_slots_scoped(term, ctx, scope, entity_locals)
                },
                encode_predicate: |predicate: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_two_slots_scoped(predicate, ctx, scope, entity_locals)
                },
                match_bindings: |scrutinee: &IRExpr,
                                 pattern: &crate::ir::types::IRPattern,
                                 scope: &HashSet<String>| {
                    let scrut =
                        guard_to_smt_two_slots_scoped(scrutinee, ctx, scope, entity_locals)?;
                    ic3_match_pattern_bindings(&scrut, pattern, vctx)
                },
                match_cond: |scrutinee: &IRExpr,
                             pattern: &crate::ir::types::IRPattern,
                             scope: &HashSet<String>| {
                    let scrut =
                        guard_to_smt_two_slots_scoped(scrutinee, ctx, scope, entity_locals)?;
                    ic3_match_pattern_cond(&scrut, pattern, vctx)
                },
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_two_slots_scoped(predicate, ctx, scope, entity_locals)
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate: &IRExpr, scope: &HashSet<String>| {
                guard_to_smt_two_slots_scoped(predicate, ctx, scope, entity_locals)
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    if matches!(binding.ty, IRType::Entity { .. }) {
        if let IRExpr::Var { name, .. } = &binding.expr {
            if let Some(bound_slot) = entity_locals.get(name) {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), *bound_slot);
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    ctx,
                    locals,
                    &scope_entity_locals,
                );
            }
            if name == var1 {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), slot1);
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    ctx,
                    locals,
                    &scope_entity_locals,
                );
            }
            if name == var2 {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), slot2);
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    ctx,
                    locals,
                    &scope_entity_locals,
                );
            }
        }
    }

    let rhs = guard_to_smt_two_slots_scoped(&binding.expr, ctx, locals, entity_locals)?;
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_two_slots_scoped(rest, body, ctx, &scope, entity_locals)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

fn two_slot_field_to_smt(
    inner: &IRExpr,
    field: &str,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let var1 = ctx.left.var;
    let slot1 = ctx.left.slot;
    let var2 = ctx.right.var;
    let slot2 = ctx.right.slot;

    if let IRExpr::Var { name, .. } = inner {
        if locals.contains(name) {
            return Err(format!(
                "local {name} cannot be used for field projection in inter-entity property"
            ));
        }
        let slot = if let Some(bound_slot) = entity_locals.get(name) {
            *bound_slot
        } else if name == var1 {
            slot1
        } else if name == var2 {
            slot2
        } else {
            return Err(format!(
                "unknown variable {name} in inter-entity property (expected {var1}, {var2}, or a bound entity local)"
            ));
        };
        for (i, f) in ctx.entity.fields.iter().enumerate() {
            if f.name == *field {
                return Ok(format!("s{slot}_f{i}"));
            }
        }
    }

    Err(format!(
        "unsupported field access in inter-entity property: {field}"
    ))
}

fn two_slot_var_to_smt(
    name: &str,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    if locals.contains(name) {
        return Ok(name.to_owned());
    }
    if entity_locals.contains_key(name) {
        return Err(format!(
            "bare entity local {name} in inter-entity property — use field access (e.g., {name}.field) instead"
        ));
    }

    let var1 = ctx.left.var;
    let var2 = ctx.right.var;
    if name == var1 || name == var2 {
        return Err(format!(
            "bare entity variable {name} in inter-entity property — \
             use field access (e.g., {name}.field) instead"
        ));
    }
    for (i, f) in ctx.entity.fields.iter().enumerate() {
        if f.name == *name {
            return Ok(format!("s{}_f{i}", ctx.left.slot));
        }
    }
    Err(format!("unknown variable {name} in inter-entity property"))
}

fn two_slot_binop_to_smt(
    op: &str,
    left: &IRExpr,
    right: &IRExpr,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let l = guard_to_smt_two_slots_scoped(left, ctx, locals, entity_locals)?;
    let r = guard_to_smt_two_slots_scoped(right, ctx, locals, entity_locals)?;
    match op {
        "OpEq" => Ok(format!("(= {l} {r})")),
        "OpNEq" => Ok(format!("(not (= {l} {r}))")),
        "OpLt" => Ok(format!("(< {l} {r})")),
        "OpLe" => Ok(format!("(<= {l} {r})")),
        "OpGt" => Ok(format!("(> {l} {r})")),
        "OpGe" => Ok(format!("(>= {l} {r})")),
        "OpAnd" => Ok(format!("(and {l} {r})")),
        "OpOr" => Ok(format!("(or {l} {r})")),
        "OpImplies" => Ok(format!("(=> {l} {r})")),
        "OpAdd" => Ok(format!("(+ {l} {r})")),
        "OpSub" => Ok(format!("(- {l} {r})")),
        "OpMul" => Ok(format!("(* {l} {r})")),
        _ => Err(format!("unsupported op in inter-entity property: {op}")),
    }
}

fn two_slot_match_arm_scope(
    scrut: &str,
    arm: &crate::ir::types::IRMatchArm,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<(Ic3MatchBindings, HashSet<String>), String> {
    let bindings = ic3_match_pattern_bindings(scrut, &arm.pattern, vctx)?;
    let mut scope = locals.clone();
    for (name, _) in &bindings {
        scope.insert(name.clone());
    }
    Ok((bindings, scope))
}

fn two_slot_match_to_smt(
    scrutinee: &IRExpr,
    arms: &[crate::ir::types::IRMatchArm],
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    if !ic3_match_has_final_catch_all(arms) {
        return Err(
            "non-exhaustive match without final wildcard/var arm is not supported in inter-entity IC3 encoding"
                .to_owned(),
        );
    }

    let scrut = guard_to_smt_two_slots_scoped(scrutinee, ctx, locals, entity_locals)?;
    let last = arms.last().expect("checked non-empty match arms");
    let (bindings, scope) = two_slot_match_arm_scope(&scrut, last, ctx.vctx, locals)?;
    let body = guard_to_smt_two_slots_scoped(&last.body, ctx, &scope, entity_locals)?;
    let mut acc = wrap_smt_let_bindings(&bindings, body);

    for arm in arms[..arms.len() - 1].iter().rev() {
        let (bindings, scope) = two_slot_match_arm_scope(&scrut, arm, ctx.vctx, locals)?;
        let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, ctx.vctx)?;
        let cond = if let Some(guard) = &arm.guard {
            let guard_smt = guard_to_smt_two_slots_scoped(guard, ctx, &scope, entity_locals)?;
            wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
        } else {
            wrap_smt_let_bindings(&bindings, pat)
        };
        let body = guard_to_smt_two_slots_scoped(&arm.body, ctx, &scope, entity_locals)?;
        let body = wrap_smt_let_bindings(&bindings, body);
        acc = format!("(ite {cond} {body} {acc})");
    }
    Ok(acc)
}

fn two_slot_if_else_to_smt(
    cond: &IRExpr,
    then_body: &IRExpr,
    else_body: Option<&IRExpr>,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let cond_smt = guard_to_smt_two_slots_scoped(cond, ctx, locals, entity_locals)?;
    let then_smt = guard_to_smt_two_slots_scoped(then_body, ctx, locals, entity_locals)?;
    if let Some(else_body) = else_body {
        let else_smt = guard_to_smt_two_slots_scoped(else_body, ctx, locals, entity_locals)?;
        Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
    } else {
        Ok(format!("(=> {cond_smt} {then_smt})"))
    }
}

fn two_slot_quantifier_to_smt(
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    kind: &str,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    ic3_finite_quantifier_formula(
        var,
        domain,
        body,
        ctx.vctx,
        locals,
        |body, scope| guard_to_smt_two_slots_scoped(body, ctx, scope, entity_locals),
        kind,
    )?
    .ok_or_else(|| "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned())
}

pub(in crate::verify::ic3) fn guard_to_smt_two_slots_scoped(
    expr: &IRExpr,
    ctx: Ic3TwoSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let vctx = ctx.vctx;

    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::Field {
            expr: inner, field, ..
        } => two_slot_field_to_smt(inner, field, ctx, locals, entity_locals),
        IRExpr::Var { name, .. } => two_slot_var_to_smt(name, ctx, locals, entity_locals),
        IRExpr::BinOp {
            op, left, right, ..
        } => two_slot_binop_to_smt(op, left, right, ctx, locals, entity_locals),
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_two_slots_scoped(operand, ctx, locals, entity_locals)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => {
                if *value < 0 {
                    Ok(format!("(- {})", -value))
                } else {
                    Ok(value.to_string())
                }
            }
            _ => Err("unsupported literal in inter-entity property".to_owned()),
        },
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => ic3_ctor_term_with(enum_name, ctor, args, vctx, |arg| {
            guard_to_smt_two_slots_scoped(arg, ctx, locals, entity_locals)
        }),
        IRExpr::Match {
            scrutinee, arms, ..
        } => two_slot_match_to_smt(scrutinee, arms, ctx, locals, entity_locals),
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => two_slot_if_else_to_smt(
            cond,
            then_body,
            else_body.as_deref(),
            ctx,
            locals,
            entity_locals,
        ),
        IRExpr::Let { bindings, body, .. } => {
            guard_let_to_smt_two_slots_scoped(bindings, body, ctx, locals, entity_locals)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_two_slots_scoped(expr, ctx, locals, entity_locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => two_slot_quantifier_to_smt(var, domain, body, "forall", ctx, locals, entity_locals),
        IRExpr::Exists {
            var, domain, body, ..
        } => two_slot_quantifier_to_smt(var, domain, body, "exists", ctx, locals, entity_locals),
        IRExpr::One {
            var, domain, body, ..
        } => two_slot_quantifier_to_smt(var, domain, body, "one", ctx, locals, entity_locals),
        IRExpr::Lone {
            var, domain, body, ..
        } => two_slot_quantifier_to_smt(var, domain, body, "lone", ctx, locals, entity_locals),
        _ => Err(format!(
            "unsupported expression in inter-entity property: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Negate an inner property expression for a specific slot.
pub(in crate::verify::ic3) fn negate_inner_property_slot(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_slot(property, entity, vctx, slot, n_slots)?;
    Ok(format!("(not {pos})"))
}

/// Like `expr_to_smt` but prefixes field variables with slot index.
pub(in crate::verify::ic3) fn expr_to_smt_slot(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
) -> Result<String, String> {
    expr_to_smt_slot_scoped(
        expr,
        entity,
        vctx,
        slot,
        n_slots,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
}

pub(in crate::verify::ic3) fn guard_let_to_smt_slot_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    ctx: Ic3SingleSlotPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let entity = ctx.entity;
    let vctx = ctx.vctx;
    let slot = ctx.slot;
    let n_slots = ctx.n_slots;

    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, locals, entity_locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        if let IRType::Entity { name } = domain {
            if name == &entity.name {
                let mut disjuncts = Vec::new();
                for chosen_slot in 0..n_slots {
                    let active = format!("s{chosen_slot}_active");
                    let mut pred_entity_locals = entity_locals.clone();
                    pred_entity_locals.insert(var.clone(), chosen_slot);
                    let pred = if let Some(predicate) = predicate {
                        guard_to_smt_slot_scoped(
                            predicate,
                            entity,
                            vctx,
                            slot,
                            n_slots,
                            locals,
                            &pred_entity_locals,
                        )?
                    } else {
                        "true".to_owned()
                    };
                    let mut rest_entity_locals = entity_locals.clone();
                    rest_entity_locals.insert(binding.name.clone(), chosen_slot);
                    let rest_smt =
                        guard_let_to_smt_slot_scoped(rest, body, ctx, locals, &rest_entity_locals)?;
                    disjuncts.push(format!("(and {active} {pred} {rest_smt})"));
                }
                return if disjuncts.is_empty() {
                    Ok("false".to_owned())
                } else {
                    Ok(format!("(or {})", disjuncts.join(" ")))
                };
            }
        }
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate: &IRExpr, scope: &HashSet<String>| {
                guard_to_smt_slot_scoped(
                    predicate,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_slot_scoped(rest, body, ctx, &scope, entity_locals)?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            Ic3DirectChooseInput {
                var,
                domain,
                predicate: predicate.as_deref(),
                locals,
            },
            Ic3DirectChooseHooks {
                encode_term: |term: &IRExpr, scope: &HashSet<String>| {
                    expr_to_smt_slot_scoped(term, entity, vctx, slot, n_slots, scope, entity_locals)
                },
                encode_predicate: |predicate: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_slot_scoped(
                        predicate,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        scope,
                        entity_locals,
                    )
                },
                match_bindings: |scrutinee: &IRExpr,
                                 pattern: &crate::ir::types::IRPattern,
                                 scope: &HashSet<String>| {
                    let scrut = expr_to_smt_slot_scoped(
                        scrutinee,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        scope,
                        entity_locals,
                    )?;
                    ic3_match_pattern_bindings(&scrut, pattern, vctx)
                },
                match_cond: |scrutinee: &IRExpr,
                             pattern: &crate::ir::types::IRPattern,
                             scope: &HashSet<String>| {
                    let scrut = expr_to_smt_slot_scoped(
                        scrutinee,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        scope,
                        entity_locals,
                    )?;
                    ic3_match_pattern_cond(&scrut, pattern, vctx)
                },
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_slot_scoped(
                        predicate,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        scope,
                        entity_locals,
                    )
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate: &IRExpr, scope: &HashSet<String>| {
                guard_to_smt_slot_scoped(
                    predicate,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    if matches!(binding.ty, IRType::Entity { .. }) {
        if let IRExpr::Var { name, .. } = &binding.expr {
            if let Some(bound_slot) = entity_locals.get(name) {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(binding.name.clone(), *bound_slot);
                return guard_let_to_smt_slot_scoped(rest, body, ctx, locals, &scope_entity_locals);
            }
        }
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_slot_scoped(
            &binding.expr,
            entity,
            vctx,
            slot,
            n_slots,
            locals,
            entity_locals,
        )?
    } else {
        expr_to_smt_slot_scoped(
            &binding.expr,
            entity,
            vctx,
            slot,
            n_slots,
            locals,
            entity_locals,
        )?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_slot_scoped(rest, body, ctx, &scope, entity_locals)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

pub(in crate::verify::ic3) fn expr_to_smt_slot_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("s{slot}_f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
            }
            if entity_locals.contains_key(name) {
                return Err(format!(
                    "bare entity local {name} in IC3 encoding — use field access (e.g., {name}.field) instead"
                ));
            }
            Err(format!("unknown variable in IC3 encoding: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if ic3_expr_type(inner).is_some_and(|ty| ic3_enum_payload_type_has_field(ty, field)) {
                let inner_smt = expr_to_smt_slot_scoped(
                    inner,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                return Ok(format!("({field} {inner_smt})"));
            }
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                if let Some(bound_slot) = entity_locals.get(name) {
                    for (i, f) in entity.fields.iter().enumerate() {
                        if f.name == *field {
                            return Ok(format!("s{bound_slot}_f{i}"));
                        }
                    }
                }
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("s{slot}_f{i}"));
                    }
                }
            }
            Err(format!("unsupported field access in IC3 encoding: {field}"))
        }
        // Arithmetic: recurse with slot context
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l =
                expr_to_smt_slot_scoped(left, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let r =
                expr_to_smt_slot_scoped(right, entity, vctx, slot, n_slots, locals, entity_locals)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                "OpDiv" => Ok(format!("(div {l} {r})")),
                "OpMod" => Ok(format!("(mod {l} {r})")),
                _ => Err(format!(
                    "unsupported binary op in IC3 slot value encoding: {op}"
                )),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNeg" => {
            let inner = expr_to_smt_slot_scoped(
                operand,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            Ok(format!("(- {inner})"))
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m =
                expr_to_smt_slot_scoped(map, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let k =
                expr_to_smt_slot_scoped(key, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let v =
                expr_to_smt_slot_scoped(value, entity, vctx, slot, n_slots, locals, entity_locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m =
                expr_to_smt_slot_scoped(map, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let k =
                expr_to_smt_slot_scoped(key, entity, vctx, slot, n_slots, locals, entity_locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 slot value encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_slot_scoped(
                scrutinee,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = expr_to_smt_slot_scoped(
                    &last.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_slot_scoped(
                        guard,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_slot_scoped(
                    &arm.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt =
                guard_to_smt_slot_scoped(cond, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let then_smt = expr_to_smt_slot_scoped(
                then_body,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = expr_to_smt_slot_scoped(
                    else_body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Err("if/else without else is not supported in IC3 value encoding".to_owned())
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    guard_to_smt_slot_scoped(
                        &binding.expr,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?
                } else {
                    expr_to_smt_slot_scoped(
                        &binding.expr,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_slot_scoped(
                body,
                entity,
                vctx,
                slot,
                n_slots,
                &scope,
                entity_locals,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_slot_scoped(expr, entity, vctx, slot, n_slots, locals, entity_locals)
        }
        IRExpr::Card { expr: inner, .. } => {
            if let Some(cardinality) = ic3_finite_literal_cardinality(inner) {
                return Ok(cardinality);
            }
            if let IRExpr::SetComp {
                var,
                domain,
                source: None,
                filter,
                projection,
                ..
            } = inner.as_ref()
            {
                if let Some(cardinality) = ic3_finite_setcomp_cardinality(
                    var,
                    domain,
                    filter,
                    projection.as_deref(),
                    vctx,
                    locals,
                    |body, scope| {
                        guard_to_smt_slot_scoped(
                            body,
                            entity,
                            vctx,
                            slot,
                            n_slots,
                            scope,
                            entity_locals,
                        )
                    },
                )? {
                    return Ok(cardinality);
                }
            }
            Err("cardinality (#) not supported in IC3 slot value encoding".to_owned())
        }
        // Literals and constructors don't need slot context
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } => expr_to_smt(expr, entity, vctx),
        _ => Err(format!(
            "unsupported expression in IC3 slot value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Like `guard_to_smt` but resolves field variables to a specific slot.
pub(in crate::verify::ic3) fn guard_to_smt_slot(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
) -> Result<String, String> {
    guard_to_smt_slot_scoped(
        guard,
        entity,
        vctx,
        slot,
        n_slots,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
}

pub(in crate::verify::ic3) fn guard_to_smt_slot_scoped(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = expr_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = expr_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let cmp = match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                };
                Ok(cmp)
            }
            "OpAnd" => {
                let l = guard_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_slot_scoped(
                    left,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_slot_scoped(
                    right,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported binary op in IC3 guard encoding: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_slot_scoped(
                operand,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            expr_to_smt_slot_scoped(guard, entity, vctx, slot, n_slots, locals, entity_locals)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 guard encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_slot_scoped(
                scrutinee,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_slot_scoped(
                    &last.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt = guard_to_smt_slot_scoped(
                        guard,
                        entity,
                        vctx,
                        slot,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_slot_scoped(
                    &arm.body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    &scope,
                    entity_locals,
                )?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt =
                guard_to_smt_slot_scoped(cond, entity, vctx, slot, n_slots, locals, entity_locals)?;
            let then_smt = guard_to_smt_slot_scoped(
                then_body,
                entity,
                vctx,
                slot,
                n_slots,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_slot_scoped(
                    else_body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_slot_scoped(
            bindings,
            body,
            Ic3SingleSlotPropertyCtx {
                entity,
                vctx,
                slot,
                n_slots,
            },
            locals,
            entity_locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_slot_scoped(expr, entity, vctx, slot, n_slots, locals, entity_locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_slot_scoped(body, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in IC3 slot guard encoding".to_owned()
        }),
        _ => Err(format!(
            "unsupported expression in IC3 guard encoding: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}
