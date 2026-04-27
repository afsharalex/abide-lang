use super::*;

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
                            inner_body, entity, vctx, var, s1, var2, s2, n_slots,
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
#[allow(clippy::too_many_arguments)]
pub(in crate::verify::ic3) fn negate_inner_property_two_slots(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
) -> Result<String, String> {
    let pos = guard_to_smt_two_slots(property, entity, vctx, var1, slot1, var2, slot2, n_slots)?;
    Ok(format!("(not {pos})"))
}

/// Encode a guard with two slot bindings (for inter-entity properties).
#[allow(clippy::too_many_lines)]
#[allow(clippy::too_many_arguments)]
pub(in crate::verify::ic3) fn guard_to_smt_two_slots(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
) -> Result<String, String> {
    guard_to_smt_two_slots_scoped(
        expr,
        entity,
        vctx,
        var1,
        slot1,
        var2,
        slot2,
        n_slots,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::verify::ic3) fn guard_let_to_smt_two_slots_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_two_slots_scoped(
            body,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            locals,
            entity_locals,
        );
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
                        guard_to_smt_two_slots_scoped(
                            predicate,
                            entity,
                            vctx,
                            var1,
                            slot1,
                            var2,
                            slot2,
                            n_slots,
                            locals,
                            &pred_entity_locals,
                        )?
                    } else {
                        "true".to_owned()
                    };
                    let mut rest_entity_locals = entity_locals.clone();
                    rest_entity_locals.insert(binding.name.clone(), chosen_slot);
                    let rest_smt = guard_let_to_smt_two_slots_scoped(
                        rest,
                        body,
                        entity,
                        vctx,
                        var1,
                        slot1,
                        var2,
                        slot2,
                        n_slots,
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
            |predicate, scope| {
                guard_to_smt_two_slots_scoped(
                    predicate,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_two_slots_scoped(
            rest,
            body,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            &scope,
            entity_locals,
        )?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| {
                guard_to_smt_two_slots_scoped(
                    term,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            |predicate, scope| {
                guard_to_smt_two_slots_scoped(
                    predicate,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_two_slots_scoped(
                    scrutinee,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_two_slots_scoped(
                    scrutinee,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| {
                    guard_to_smt_two_slots_scoped(
                        predicate,
                        entity,
                        vctx,
                        var1,
                        slot1,
                        var2,
                        slot2,
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
            |predicate, scope| {
                guard_to_smt_two_slots_scoped(
                    predicate,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
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
                return guard_let_to_smt_two_slots_scoped(
                    rest,
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
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
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
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
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    &scope_entity_locals,
                );
            }
        }
    }

    let rhs = guard_to_smt_two_slots_scoped(
        &binding.expr,
        entity,
        vctx,
        var1,
        slot1,
        var2,
        slot2,
        n_slots,
        locals,
        entity_locals,
    )?;
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_two_slots_scoped(
        rest,
        body,
        entity,
        vctx,
        var1,
        slot1,
        var2,
        slot2,
        n_slots,
        &scope,
        entity_locals,
    )?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub(in crate::verify::ic3) fn guard_to_smt_two_slots_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    var1: &str,
    slot1: usize,
    var2: &str,
    slot2: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
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
        } => {
            // Determine which slot this field access refers to
            if let IRExpr::Var { name, .. } = inner.as_ref() {
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
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("s{slot}_f{i}"));
                    }
                }
            }
            Err(format!(
                "unsupported field access in inter-entity property: {field}"
            ))
        }
        IRExpr::Var { name, .. } => {
            if locals.contains(name) {
                return Ok(name.clone());
            }
            if entity_locals.contains_key(name) {
                return Err(format!(
                    "bare entity local {name} in inter-entity property — use field access (e.g., {name}.field) instead"
                ));
            }
            // Bare quantifier variables (a, b) without field access are not valid
            // value expressions — they represent entity instances, not values.
            if name == var1 || name == var2 {
                return Err(format!(
                    "bare entity variable {name} in inter-entity property — \
                     use field access (e.g., {name}.field) instead"
                ));
            }
            // Try as a field name (unqualified field access like `status`)
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    // Ambiguous: which slot does this unqualified field belong to?
                    // Default to slot1, but this is a spec issue — should use qualified access.
                    return Ok(format!("s{slot1}_f{i}"));
                }
            }
            Err(format!("unknown variable {name} in inter-entity property"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
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
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(=> {l} {r})"))
            }
            "OpAdd" | "OpSub" | "OpMul" => {
                let l = guard_to_smt_two_slots_scoped(
                    left,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let r = guard_to_smt_two_slots_scoped(
                    right,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                let op_sym = match op.as_str() {
                    "OpAdd" => "+",
                    "OpSub" => "-",
                    "OpMul" => "*",
                    _ => unreachable!(),
                };
                Ok(format!("({op_sym} {l} {r})"))
            }
            _ => Err(format!("unsupported op in inter-entity property: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_two_slots_scoped(
                operand,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
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
            guard_to_smt_two_slots_scoped(
                arg,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )
        }),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in inter-entity IC3 encoding"
                        .to_owned(),
                );
            }
            let scrut = guard_to_smt_two_slots_scoped(
                scrutinee,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
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
                let body = guard_to_smt_two_slots_scoped(
                    &last.body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
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
                    let guard_smt = guard_to_smt_two_slots_scoped(
                        guard,
                        entity,
                        vctx,
                        var1,
                        slot1,
                        var2,
                        slot2,
                        n_slots,
                        &scope,
                        entity_locals,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_two_slots_scoped(
                    &arm.body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
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
            let cond_smt = guard_to_smt_two_slots_scoped(
                cond,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
            let then_smt = guard_to_smt_two_slots_scoped(
                then_body,
                entity,
                vctx,
                var1,
                slot1,
                var2,
                slot2,
                n_slots,
                locals,
                entity_locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_two_slots_scoped(
                    else_body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    locals,
                    entity_locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_two_slots_scoped(
            bindings,
            body,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            locals,
            entity_locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => guard_to_smt_two_slots_scoped(
            expr,
            entity,
            vctx,
            var1,
            slot1,
            var2,
            slot2,
            n_slots,
            locals,
            entity_locals,
        ),
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| {
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
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
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
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
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
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
                guard_to_smt_two_slots_scoped(
                    body,
                    entity,
                    vctx,
                    var1,
                    slot1,
                    var2,
                    slot2,
                    n_slots,
                    scope,
                    entity_locals,
                )
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in inter-entity IC3 encoding".to_owned()
        }),
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

#[allow(clippy::too_many_arguments)]
pub(in crate::verify::ic3) fn guard_let_to_smt_slot_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    slot: usize,
    n_slots: usize,
    locals: &HashSet<String>,
    entity_locals: &Ic3SlotEntityLocals,
) -> Result<String, String> {
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
                    let rest_smt = guard_let_to_smt_slot_scoped(
                        rest,
                        body,
                        entity,
                        vctx,
                        slot,
                        n_slots,
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
            |predicate, scope| {
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
        let rest_smt = guard_let_to_smt_slot_scoped(
            rest,
            body,
            entity,
            vctx,
            slot,
            n_slots,
            &scope,
            entity_locals,
        )?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            locals,
            |term, scope| {
                expr_to_smt_slot_scoped(term, entity, vctx, slot, n_slots, scope, entity_locals)
            },
            |predicate, scope| {
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
            |scrutinee, pattern, scope| {
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
            |scrutinee, pattern, scope| {
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
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| {
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
            |predicate, scope| {
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
                return guard_let_to_smt_slot_scoped(
                    rest,
                    body,
                    entity,
                    vctx,
                    slot,
                    n_slots,
                    locals,
                    &scope_entity_locals,
                );
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
    let rest_smt = guard_let_to_smt_slot_scoped(
        rest,
        body,
        entity,
        vctx,
        slot,
        n_slots,
        &scope,
        entity_locals,
    )?;
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
            entity,
            vctx,
            slot,
            n_slots,
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
