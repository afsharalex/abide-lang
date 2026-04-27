use super::*;

pub(in crate::verify::ic3) fn expr_to_smt_sys(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
) -> Result<String, String> {
    expr_to_smt_sys_scoped(expr, entity, vctx, ent_name, slot, &HashSet::new())
}

pub(in crate::verify::ic3) fn guard_let_to_smt_sys_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    locals: &HashSet<String>,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_sys_scoped(predicate, entity, vctx, ent_name, slot, scope)
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt =
            guard_let_to_smt_sys_scoped(rest, body, entity, vctx, ent_name, slot, &scope)?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, locals)?
    } else {
        expr_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, locals)?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_sys_scoped(rest, body, entity, vctx, ent_name, slot, &scope)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

pub(in crate::verify::ic3) fn expr_to_smt_sys_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    locals: &HashSet<String>,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("{ent_name}_{slot}_f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
            }
            Err(format!("unknown variable in system IC3: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { .. } = inner.as_ref() {
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("{ent_name}_{slot}_f{i}"));
                    }
                }
            }
            Err(format!("unsupported field access in system IC3: {field}"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
            let r = expr_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                _ => Err(format!("unsupported op in system IC3 value: {op}")),
            }
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_sys_scoped(map, entity, vctx, ent_name, slot, locals)?;
            let k = expr_to_smt_sys_scoped(key, entity, vctx, ent_name, slot, locals)?;
            let v = expr_to_smt_sys_scoped(value, entity, vctx, ent_name, slot, locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_sys_scoped(map, entity, vctx, ent_name, slot, locals)?;
            let k = expr_to_smt_sys_scoped(key, entity, vctx, ent_name, slot, locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 value encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_scoped(scrutinee, entity, vctx, ent_name, slot, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body =
                    expr_to_smt_sys_scoped(&last.body, entity, vctx, ent_name, slot, &scope)?;
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
                    let guard_smt =
                        guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_sys_scoped(&arm.body, entity, vctx, ent_name, slot, &scope)?;
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
            let cond_smt = guard_to_smt_sys_scoped(cond, entity, vctx, ent_name, slot, locals)?;
            let then_smt = expr_to_smt_sys_scoped(then_body, entity, vctx, ent_name, slot, locals)?;
            if let Some(else_body) = else_body {
                let else_smt =
                    expr_to_smt_sys_scoped(else_body, entity, vctx, ent_name, slot, locals)?;
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
                    guard_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, &scope)?
                } else {
                    expr_to_smt_sys_scoped(&binding.expr, entity, vctx, ent_name, slot, &scope)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_sys_scoped(
                body, entity, vctx, ent_name, slot, &scope,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_sys_scoped(expr, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } => expr_to_smt(expr, entity, vctx),
        _ => Err(format!(
            "unsupported expression in system IC3 value: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Encode a guard with system-level slot naming.
pub(in crate::verify::ic3) fn guard_to_smt_sys(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
) -> Result<String, String> {
    guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &HashSet::new())
}

pub(in crate::verify::ic3) fn guard_to_smt_sys_scoped(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    ent_name: &str,
    slot: usize,
    locals: &HashSet<String>,
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
                let l = expr_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = expr_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                })
            }
            "OpAnd" => {
                let l = guard_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = guard_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = guard_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_sys_scoped(left, entity, vctx, ent_name, slot, locals)?;
                let r = guard_to_smt_sys_scoped(right, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported op in system IC3 guard: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys_scoped(operand, entity, vctx, ent_name, slot, locals)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            expr_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 guard encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_scoped(scrutinee, entity, vctx, ent_name, slot, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body =
                    guard_to_smt_sys_scoped(&last.body, entity, vctx, ent_name, slot, &scope)?;
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
                    let guard_smt =
                        guard_to_smt_sys_scoped(guard, entity, vctx, ent_name, slot, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body =
                    guard_to_smt_sys_scoped(&arm.body, entity, vctx, ent_name, slot, &scope)?;
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
            let cond_smt = guard_to_smt_sys_scoped(cond, entity, vctx, ent_name, slot, locals)?;
            let then_smt =
                guard_to_smt_sys_scoped(then_body, entity, vctx, ent_name, slot, locals)?;
            if let Some(else_body) = else_body {
                let else_smt =
                    guard_to_smt_sys_scoped(else_body, entity, vctx, ent_name, slot, locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            guard_let_to_smt_sys_scoped(bindings, body, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_sys_scoped(expr, entity, vctx, ent_name, slot, locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_scoped(body, entity, vctx, ent_name, slot, scope),
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 guard encoding".to_owned()
        }),
        _ => Err(format!(
            "unsupported expression in system IC3 guard: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Encode a guard with two entity-slot bindings for inter-entity system properties.
#[allow(
    dead_code,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::similar_names
)]
pub(in crate::verify::ic3) fn guard_to_smt_sys_two(
    expr: &IRExpr,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    ent2_name: &str,
    slot2: usize,
    var2: &str,
) -> Result<String, String> {
    guard_to_smt_sys_two_scoped(
        expr,
        entity1,
        entity2,
        vctx,
        ent1_name,
        slot1,
        var1,
        ent2_name,
        slot2,
        var2,
        &HashSet::new(),
    )
}

#[allow(
    dead_code,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::similar_names
)]
pub(in crate::verify::ic3) fn guard_let_to_smt_sys_two_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    ent2_name: &str,
    slot2: usize,
    var2: &str,
    locals: &HashSet<String>,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_sys_two_scoped(
            body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, locals,
        );
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate, scope| {
                guard_to_smt_sys_two_scoped(
                    predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_sys_two_scoped(
            rest, body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
            &scope,
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
                guard_to_smt_sys_two_scoped(
                    term, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            |predicate, scope| {
                guard_to_smt_sys_two_scoped(
                    predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_sys_two_scoped(
                    scrutinee, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = guard_to_smt_sys_two_scoped(
                    scrutinee, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
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
                    guard_to_smt_sys_two_scoped(
                        predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name,
                        slot2, var2, scope,
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
                guard_to_smt_sys_two_scoped(
                    predicate, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, scope,
                )
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    let rhs = guard_to_smt_sys_two_scoped(
        &binding.expr,
        entity1,
        entity2,
        vctx,
        ent1_name,
        slot1,
        var1,
        ent2_name,
        slot2,
        var2,
        locals,
    )?;
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_sys_two_scoped(
        rest, body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, &scope,
    )?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

#[allow(
    dead_code,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::similar_names
)]
pub(in crate::verify::ic3) fn guard_to_smt_sys_two_scoped(
    expr: &IRExpr,
    entity1: &IREntity,
    entity2: &IREntity,
    vctx: &VerifyContext,
    ent1_name: &str,
    slot1: usize,
    var1: &str,
    ent2_name: &str,
    slot2: usize,
    var2: &str,
    locals: &HashSet<String>,
) -> Result<String, String> {
    match expr {
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(value.to_string()),
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                if locals.contains(name) {
                    return Err(format!(
                        "local {name} cannot be used for field projection in cross-entity property"
                    ));
                }
                let (entity, ent_name, slot) = if name == var1 {
                    (entity1, ent1_name, slot1)
                } else if name == var2 {
                    (entity2, ent2_name, slot2)
                } else {
                    return Err(format!("unknown var {name} in cross-entity property"));
                };
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("{ent_name}_{slot}_f{i}"));
                    }
                }
                return Err(format!("field {field} not found on entity {ent_name}"));
            }
            Err(format!(
                "unsupported field access in cross-entity property: {field}"
            ))
        }
        IRExpr::Var { name, .. } => {
            if locals.contains(name) {
                Ok(name.clone())
            } else if name == var1 || name == var2 {
                Err(format!(
                    "bare entity variable {name} in cross-entity property — use field access instead"
                ))
            } else {
                Err(format!("unknown variable {name} in cross-entity property"))
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                Ok(match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                })
            }
            "OpAnd" => {
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                Ok(format!("(or {l} {r})"))
            }
            _ => {
                // Arithmetic: resolve values
                let l = guard_to_smt_sys_two_scoped(
                    left, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let r = guard_to_smt_sys_two_scoped(
                    right, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    locals,
                )?;
                let op_sym = match op.as_str() {
                    "OpAdd" => "+",
                    "OpSub" => "-",
                    "OpMul" => "*",
                    _ => return Err(format!("unsupported op in cross-entity property: {op}")),
                };
                Ok(format!("({op_sym} {l} {r})"))
            }
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys_two_scoped(
                operand, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Lit {
            value: LitVal::Int { value },
            ..
        } => {
            if *value < 0 {
                Ok(format!("(- {})", -value))
            } else {
                Ok(value.to_string())
            }
        }
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => ic3_ctor_term_with(enum_name, ctor, args, vctx, |arg| {
            guard_to_smt_sys_two_scoped(
                arg, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, locals,
            )
        }),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in cross-entity IC3 encoding"
                        .to_owned(),
                );
            }
            let scrut = guard_to_smt_sys_two_scoped(
                scrutinee, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_sys_two_scoped(
                    &last.body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, &scope,
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
                    let guard_smt = guard_to_smt_sys_two_scoped(
                        guard, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                        var2, &scope,
                    )?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_sys_two_scoped(
                    &arm.body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, &scope,
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
            let cond_smt = guard_to_smt_sys_two_scoped(
                cond, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            let then_smt = guard_to_smt_sys_two_scoped(
                then_body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                locals,
            )?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_sys_two_scoped(
                    else_body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2,
                    var2, locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => guard_let_to_smt_sys_two_scoped(
            bindings, body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
            locals,
        ),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => guard_to_smt_sys_two_scoped(
            expr, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2, locals,
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
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
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
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
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
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
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
                guard_to_smt_sys_two_scoped(
                    body, entity1, entity2, vctx, ent1_name, slot1, var1, ent2_name, slot2, var2,
                    scope,
                )
            },
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in cross-entity IC3 encoding".to_owned()
        }),
        _ => Err(format!(
            "unsupported expression in cross-entity property: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}
