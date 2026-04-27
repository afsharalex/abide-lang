use super::*;

#[allow(clippy::match_same_arms)]
pub(in crate::verify::ic3) fn expr_to_smt(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
) -> Result<String, String> {
    expr_to_smt_scoped(expr, entity, vctx, &HashSet::new())
}

pub(in crate::verify::ic3) fn guard_let_to_smt_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<String, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_scoped(body, entity, vctx, locals);
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
            |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_scoped(rest, body, entity, vctx, &scope)?;
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
            |term, scope| expr_to_smt_scoped(term, entity, vctx, scope),
            |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, scope)?;
                ic3_match_pattern_bindings(&scrut, pattern, vctx)
            },
            |scrutinee, pattern, scope| {
                let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, scope)?;
                ic3_match_pattern_cond(&scrut, pattern, vctx)
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate, scope| guard_to_smt_scoped(predicate, entity, vctx, scope),
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_scoped(&binding.expr, entity, vctx, locals)?
    } else {
        expr_to_smt_scoped(&binding.expr, entity, vctx, locals)?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_scoped(rest, body, entity, vctx, &scope)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

pub(in crate::verify::ic3) fn expr_to_smt_scoped(
    expr: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<String, String> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => {
                if *value < 0 {
                    Ok(format!("(- {})", -value))
                } else {
                    Ok(value.to_string())
                }
            }
            LitVal::Bool { value } => Ok(value.to_string()),
            LitVal::Real { value } => Ok(format!("{value}")),
            LitVal::Float { value } => Ok(format!("{value}")),
            LitVal::Str { .. } => Err("string literals not supported in IC3 encoding".to_owned()),
        },
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => ic3_ctor_term_with(enum_name, ctor, args, vctx, |arg| {
            expr_to_smt_scoped(arg, entity, vctx, locals)
        }),
        IRExpr::Var { name, .. } => {
            for (i, f) in entity.fields.iter().enumerate() {
                if f.name == *name {
                    return Ok(format!("f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
            }
            Err(format!("unknown variable in IC3 encoding: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            // Field access on entity variable: o.status → f{index}
            if let IRExpr::Var { .. } = inner.as_ref() {
                for (i, f) in entity.fields.iter().enumerate() {
                    if f.name == *field {
                        return Ok(format!("f{i}"));
                    }
                }
            }
            Err(format!("unsupported field access in IC3 encoding: {field}"))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt_scoped(left, entity, vctx, locals)?;
            let r = expr_to_smt_scoped(right, entity, vctx, locals)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                "OpDiv" => Ok(format!("(div {l} {r})")),
                "OpMod" => Ok(format!("(mod {l} {r})")),
                _ => Err(format!("unsupported binary op in IC3 value encoding: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNeg" => {
            let inner = expr_to_smt_scoped(operand, entity, vctx, locals)?;
            Ok(format!("(- {inner})"))
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_scoped(map, entity, vctx, locals)?;
            let k = expr_to_smt_scoped(key, entity, vctx, locals)?;
            let v = expr_to_smt_scoped(value, entity, vctx, locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_scoped(map, entity, vctx, locals)?;
            let k = expr_to_smt_scoped(key, entity, vctx, locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in IC3 value encoding"
                        .to_owned(),
                );
            }
            let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = expr_to_smt_scoped(&last.body, entity, vctx, &scope)?;
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
                    let guard_smt = guard_to_smt_scoped(guard, entity, vctx, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_scoped(&arm.body, entity, vctx, &scope)?;
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
            let cond_smt = guard_to_smt_scoped(cond, entity, vctx, locals)?;
            let then_smt = expr_to_smt_scoped(then_body, entity, vctx, locals)?;
            if let Some(else_body) = else_body {
                let else_smt = expr_to_smt_scoped(else_body, entity, vctx, locals)?;
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
                    guard_to_smt_scoped(&binding.expr, entity, vctx, &scope)?
                } else {
                    expr_to_smt_scoped(&binding.expr, entity, vctx, &scope)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_scoped(body, entity, vctx, &scope)?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_scoped(expr, entity, vctx, locals)
        }
        IRExpr::Card { .. } => Err("cardinality (#) not supported in IC3 CHC encoding".to_owned()),
        _ => Err(format!(
            "unsupported expression in IC3 value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Convert a guard expression to an SMT-LIB2 boolean term.
///
/// Returns `Err` for unsupported forms — never silently approximates.
/// Encode an `initial_constraint` expression as SMT, replacing `$` (and the field name)
/// with the given CHC variable name. Used for nondeterministic field defaults in create rules.
pub(in crate::verify::ic3) fn constraint_to_smt_with_dollar(
    expr: &IRExpr,
    dollar_var: &str,
    entity: &IREntity,
    vctx: &VerifyContext,
) -> Result<String, String> {
    constraint_to_smt_with_dollar_scoped(expr, dollar_var, entity, vctx, &HashSet::new())
}

pub(in crate::verify::ic3) fn constraint_to_smt_with_dollar_scoped(
    expr: &IRExpr,
    dollar_var: &str,
    entity: &IREntity,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
) -> Result<String, String> {
    match expr {
        IRExpr::Var { name, .. } if name == "$" => Ok(dollar_var.to_owned()),
        IRExpr::Var { name, .. } => {
            // Check if it's a field name (for `where field_name > 0` syntax)
            if entity.fields.iter().any(|f| f.name == *name) {
                Ok(dollar_var.to_owned())
            } else if locals.contains(name) {
                Ok(name.clone())
            } else {
                Err(format!("unknown variable in initial_constraint: {name}"))
            }
        }
        IRExpr::Lit { .. } => expr_to_smt(expr, entity, vctx),
        IRExpr::Ctor { .. } => expr_to_smt(expr, entity, vctx),
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = constraint_to_smt_with_dollar_scoped(left, dollar_var, entity, vctx, locals)?;
            let r = constraint_to_smt_with_dollar_scoped(right, dollar_var, entity, vctx, locals)?;
            match op.as_str() {
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
                _ => Err(format!("unsupported op in initial_constraint: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner =
                constraint_to_smt_with_dollar_scoped(operand, dollar_var, entity, vctx, locals)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt =
                constraint_to_smt_with_dollar_scoped(cond, dollar_var, entity, vctx, locals)?;
            let then_smt =
                constraint_to_smt_with_dollar_scoped(then_body, dollar_var, entity, vctx, locals)?;
            if let Some(else_body) = else_body {
                let else_smt = constraint_to_smt_with_dollar_scoped(
                    else_body, dollar_var, entity, vctx, locals,
                )?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    constraint_to_smt_with_dollar_scoped(
                        &binding.expr,
                        dollar_var,
                        entity,
                        vctx,
                        &scope,
                    )?
                } else {
                    expr_to_smt_scoped(&binding.expr, entity, vctx, &scope)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&constraint_to_smt_with_dollar_scoped(
                body, dollar_var, entity, vctx, &scope,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            constraint_to_smt_with_dollar_scoped(expr, dollar_var, entity, vctx, locals)
        }
        _ => Err(format!(
            "unsupported expression in initial_constraint: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

pub(in crate::verify::ic3) fn guard_to_smt(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
) -> Result<String, String> {
    guard_to_smt_scoped(guard, entity, vctx, &HashSet::new())
}

pub(in crate::verify::ic3) fn guard_to_smt_scoped(
    guard: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
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
                let l = expr_to_smt_scoped(left, entity, vctx, locals)?;
                let r = expr_to_smt_scoped(right, entity, vctx, locals)?;
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
                let l = guard_to_smt_scoped(left, entity, vctx, locals)?;
                let r = guard_to_smt_scoped(right, entity, vctx, locals)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_scoped(left, entity, vctx, locals)?;
                let r = guard_to_smt_scoped(right, entity, vctx, locals)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_scoped(left, entity, vctx, locals)?;
                let r = guard_to_smt_scoped(right, entity, vctx, locals)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported binary op in IC3 guard encoding: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_scoped(operand, entity, vctx, locals)?;
            Ok(format!("(not {inner})"))
        }
        // Field access as boolean: resolve to field variable
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            let val = expr_to_smt_scoped(guard, entity, vctx, locals)?;
            Ok(val)
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
            let scrut = expr_to_smt_scoped(scrutinee, entity, vctx, locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_scoped(&last.body, entity, vctx, &scope)?;
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
                    let guard_smt = guard_to_smt_scoped(guard, entity, vctx, &scope)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_scoped(&arm.body, entity, vctx, &scope)?;
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
            let cond_smt = guard_to_smt_scoped(cond, entity, vctx, locals)?;
            let then_smt = guard_to_smt_scoped(then_body, entity, vctx, locals)?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_scoped(else_body, entity, vctx, locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            guard_let_to_smt_scoped(bindings, body, entity, vctx, locals)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_scoped(expr, entity, vctx, locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "forall",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "exists",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "one",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_scoped(body, entity, vctx, scope),
            "lone",
        )?
        .ok_or_else(|| "quantifier domain is not yet supported in IC3 guard encoding".to_owned()),
        _ => Err(format!(
            "unsupported expression in IC3 guard encoding: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

/// Negate a property expression for the error rule.
///
/// Strips `always` and `forall` wrappers (IC3 proves these by construction),
/// then negates the inner property.
#[allow(clippy::match_same_arms)]
pub(in crate::verify::ic3) fn negate_property_smt(
    property: &IRExpr,
    entity: &IREntity,
    vctx: &VerifyContext,
) -> Result<String, String> {
    match property {
        // Strip always — IC3 proves always by construction
        IRExpr::Always { body, .. } => negate_property_smt(body, entity, vctx),
        // Strip forall over entity — IC3 checks per-entity
        IRExpr::Forall {
            domain: IRType::Entity { .. },
            body,
            ..
        } => negate_property_smt(body, entity, vctx),
        _ => {
            let pos = guard_to_smt(property, entity, vctx)?;
            Ok(format!("(not {pos})"))
        }
    }
}
