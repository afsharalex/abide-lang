use super::*;

pub(in crate::verify::ic3) fn ic3_finite_choose_candidates(
    domain: &IRType,
    vctx: &VerifyContext,
) -> Option<Vec<String>> {
    match domain {
        IRType::Bool => Some(vec!["false".to_owned(), "true".to_owned()]),
        IRType::Enum { name, variants }
            if !variants.iter().any(|variant| !variant.fields.is_empty()) =>
        {
            let (min_id, max_id) = vctx.enum_ranges.get(name).copied()?;
            Some((min_id..=max_id).map(|id| id.to_string()).collect())
        }
        _ => None,
    }
}

pub(in crate::verify::ic3) fn ic3_finite_quantifier_formula<F>(
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
    mut encode_body: F,
    kind: &str,
) -> Result<Option<String>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    let Some(candidates) = ic3_finite_choose_candidates(domain, vctx) else {
        return Ok(None);
    };

    let mut scope = locals.clone();
    scope.insert(var.to_owned());
    let preds = candidates
        .iter()
        .map(|candidate| {
            let raw = encode_body(body, &scope)?;
            Ok(format!("(let (({var} {candidate})) {raw})"))
        })
        .collect::<Result<Vec<_>, String>>()?;

    let formula = match kind {
        "forall" => {
            if preds.is_empty() {
                "true".to_owned()
            } else {
                format!("(and {})", preds.join(" "))
            }
        }
        "exists" => {
            if preds.is_empty() {
                "false".to_owned()
            } else {
                format!("(or {})", preds.join(" "))
            }
        }
        "one" => {
            if preds.is_empty() {
                "false".to_owned()
            } else {
                let mut disjuncts = Vec::new();
                for (i, pred_i) in preds.iter().enumerate() {
                    let mut conjuncts = vec![pred_i.clone()];
                    for (j, pred_j) in preds.iter().enumerate() {
                        if i != j {
                            conjuncts.push(format!("(not {pred_j})"));
                        }
                    }
                    disjuncts.push(format!("(and {})", conjuncts.join(" ")));
                }
                format!("(or {})", disjuncts.join(" "))
            }
        }
        "lone" => {
            if preds.len() <= 1 {
                "true".to_owned()
            } else {
                let mut conjuncts = Vec::new();
                for i in 0..preds.len() {
                    for j in (i + 1)..preds.len() {
                        conjuncts.push(format!("(not (and {} {}))", preds[i], preds[j]));
                    }
                }
                format!("(and {})", conjuncts.join(" "))
            }
        }
        _ => return Err(format!("unknown finite quantifier kind in IC3: {kind}")),
    };

    Ok(Some(formula))
}

pub(in crate::verify::ic3) fn ic3_finite_choose_witness<F>(
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    vctx: &VerifyContext,
    locals: &HashSet<String>,
    mut encode_predicate: F,
) -> Result<Option<(String, String)>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    let Some(candidates) = ic3_finite_choose_candidates(domain, vctx) else {
        return Ok(None);
    };
    if candidates.is_empty() {
        return Ok(Some(("false".to_owned(), "0".to_owned())));
    }

    let mut pred_scope = locals.clone();
    pred_scope.insert(var.to_owned());

    let candidate_preds = candidates
        .iter()
        .map(|candidate| {
            let pred = if let Some(predicate) = predicate {
                let raw = encode_predicate(predicate, &pred_scope)?;
                format!("(let (({var} {candidate})) {raw})")
            } else {
                "true".to_owned()
            };
            Ok((candidate.clone(), pred))
        })
        .collect::<Result<Vec<_>, String>>()?;

    let existence = if predicate.is_some() {
        format!(
            "(or {})",
            candidate_preds
                .iter()
                .map(|(_, pred)| pred.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        )
    } else {
        "true".to_owned()
    };

    let mut witness = candidate_preds
        .last()
        .map(|(candidate, _)| candidate.clone())
        .expect("candidates checked non-empty");
    for (candidate, pred) in candidate_preds[..candidate_preds.len().saturating_sub(1)]
        .iter()
        .rev()
    {
        witness = format!("(ite {pred} {candidate} {witness})");
    }

    Ok(Some((existence, witness)))
}

pub(in crate::verify::ic3) fn ic3_quantified_choose_sort(domain: &IRType) -> Option<String> {
    match domain {
        IRType::Int | IRType::Identity => Some("Int".to_owned()),
        IRType::Real | IRType::Float => Some("Real".to_owned()),
        IRType::Enum { name, variants }
            if variants.iter().any(|variant| !variant.fields.is_empty()) =>
        {
            Some(name.clone())
        }
        _ => None,
    }
}

pub(in crate::verify::ic3) fn ic3_quantified_choose_formula<F>(
    binding_name: &str,
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    locals: &HashSet<String>,
    mut encode_predicate: F,
    rest_smt: String,
) -> Result<Option<String>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    if ic3_quantified_choose_sort(domain).is_none() {
        return Ok(None);
    }

    let mut body = rest_smt;
    if let Some(predicate) = predicate {
        let mut pred_scope = locals.clone();
        pred_scope.insert(var.to_owned());
        let pred = encode_predicate(predicate, &pred_scope)?;
        body = format!("(and {pred} {body})");
    }

    let sort = ic3_quantified_choose_sort(domain).expect("checked above");
    Ok(Some(format!(
        "(exists (({binding_name} {sort})) (let (({var} {binding_name})) {body}))"
    )))
}

pub(in crate::verify::ic3) fn default_witness_for_type(ty: &IRType) -> Option<String> {
    match ty {
        IRType::Int | IRType::Identity => Some("0".to_owned()),
        IRType::Real | IRType::Float => Some("0.0".to_owned()),
        IRType::Bool => Some("false".to_owned()),
        IRType::Enum { .. } => {
            let ctor = ic3_default_ctor_term(ty)?;
            Some(ctor)
        }
        _ => None,
    }
}

pub(in crate::verify::ic3) fn ic3_default_ctor_term(ty: &IRType) -> Option<String> {
    let IRType::Enum { variants, .. } = ty else {
        return None;
    };
    let variant = variants.first()?;
    let ctor_name = variant
        .name
        .rsplit("::")
        .next()
        .unwrap_or(&variant.name)
        .to_owned();
    if variant.fields.is_empty() {
        Some(ctor_name)
    } else {
        let mut args = Vec::with_capacity(variant.fields.len());
        for field in &variant.fields {
            args.push(default_witness_for_type(&field.ty)?);
        }
        Some(format!("({ctor_name} {})", args.join(" ")))
    }
}

pub(in crate::verify::ic3) fn ic3_expr_mentions_var(expr: &IRExpr, target: &str) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == target,
        IRExpr::Field { expr, .. }
        | IRExpr::Prime { expr, .. }
        | IRExpr::UnOp { operand: expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. } => ic3_expr_mentions_var(expr, target),
        IRExpr::BinOp { left, right, .. } => {
            ic3_expr_mentions_var(left, target) || ic3_expr_mentions_var(right, target)
        }
        IRExpr::Index { map, key, .. } => {
            ic3_expr_mentions_var(map, target) || ic3_expr_mentions_var(key, target)
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            ic3_expr_mentions_var(map, target)
                || ic3_expr_mentions_var(key, target)
                || ic3_expr_mentions_var(value, target)
        }
        IRExpr::Ctor { args, .. } => args
            .iter()
            .any(|(_, expr)| ic3_expr_mentions_var(expr, target)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            ic3_expr_mentions_var(scrutinee, target)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| ic3_expr_mentions_var(guard, target))
                        || ic3_expr_mentions_var(&arm.body, target)
                })
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            ic3_expr_mentions_var(cond, target)
                || ic3_expr_mentions_var(then_body, target)
                || else_body
                    .as_ref()
                    .is_some_and(|expr| ic3_expr_mentions_var(expr, target))
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings
                .iter()
                .any(|binding| ic3_expr_mentions_var(&binding.expr, target))
                || ic3_expr_mentions_var(body, target)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. }
        | IRExpr::Card { expr: body, .. } => ic3_expr_mentions_var(body, target),
        IRExpr::Until { left, right, .. } | IRExpr::Since { left, right, .. } => {
            ic3_expr_mentions_var(left, target) || ic3_expr_mentions_var(right, target)
        }
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            ic3_expr_mentions_var(body, target)
                || in_filter
                    .as_ref()
                    .is_some_and(|expr| ic3_expr_mentions_var(expr, target))
        }
        IRExpr::Choose { predicate, .. } => predicate
            .as_ref()
            .is_some_and(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::Saw { args, .. } => args
            .iter()
            .flatten()
            .any(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements
            .iter()
            .any(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::MapLit { entries, .. } => entries.iter().any(|(key, value)| {
            ic3_expr_mentions_var(key, target) || ic3_expr_mentions_var(value, target)
        }),
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            ic3_expr_mentions_var(filter, target)
                || projection
                    .as_ref()
                    .is_some_and(|expr| ic3_expr_mentions_var(expr, target))
        }
        IRExpr::App { func, arg, .. } => {
            ic3_expr_mentions_var(func, target) || ic3_expr_mentions_var(arg, target)
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(|expr| ic3_expr_mentions_var(expr, target)),
        IRExpr::VarDecl { init, rest, .. } => {
            ic3_expr_mentions_var(init, target) || ic3_expr_mentions_var(rest, target)
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            ic3_expr_mentions_var(cond, target)
                || invariants
                    .iter()
                    .any(|expr| ic3_expr_mentions_var(expr, target))
                || ic3_expr_mentions_var(body, target)
        }
        IRExpr::Lam { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } | IRExpr::Lit { .. } => {
            false
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::verify::ic3) fn ic3_direct_choose_witness<F>(
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    locals: &HashSet<String>,
    mut encode_term: F,
    mut encode_predicate: impl FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    mut match_bindings: impl FnMut(
        &IRExpr,
        &crate::ir::types::IRPattern,
        &HashSet<String>,
    ) -> Result<Vec<(String, String)>, String>,
    mut match_cond: impl FnMut(
        &IRExpr,
        &crate::ir::types::IRPattern,
        &HashSet<String>,
    ) -> Result<String, String>,
) -> Result<Option<String>, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    #[derive(Clone)]
    enum NumericBound {
        Exact(String),
        Lower(String),
        Upper(String),
    }

    fn smt_numeric_step(domain: &IRType, base: String, delta: i32) -> Option<String> {
        match domain {
            IRType::Int | IRType::Identity => Some(if delta >= 0 {
                format!("(+ {base} 1)")
            } else {
                format!("(- {base} 1)")
            }),
            IRType::Real | IRType::Float => Some(if delta >= 0 {
                format!("(+ {base} 1.0)")
            } else {
                format!("(- {base} 1.0)")
            }),
            _ => None,
        }
    }

    fn smt_max(a: String, b: String) -> String {
        format!("(ite (>= {a} {b}) {a} {b})")
    }

    fn smt_min(a: String, b: String) -> String {
        format!("(ite (<= {a} {b}) {a} {b})")
    }

    fn collect_numeric_bounds<F>(
        var: &str,
        domain: &IRType,
        predicate: Option<&IRExpr>,
        locals: &HashSet<String>,
        encode_term: &mut F,
        bounds: &mut Vec<NumericBound>,
    ) -> Result<bool, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    {
        let Some(predicate) = predicate else {
            return Ok(true);
        };
        match predicate {
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpAnd" => {
                let left_ok =
                    collect_numeric_bounds(var, domain, Some(left), locals, encode_term, bounds)?;
                let right_ok =
                    collect_numeric_bounds(var, domain, Some(right), locals, encode_term, bounds)?;
                Ok(left_ok && right_ok)
            }
            IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
                collect_numeric_bounds(var, domain, Some(expr), locals, encode_term, bounds)
            }
            IRExpr::BinOp {
                op, left, right, ..
            } => {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if name == var && !ic3_expr_mentions_var(right, var) {
                        let rhs = encode_term(right, locals)?;
                        match op.as_str() {
                            "OpEq" => bounds.push(NumericBound::Exact(rhs)),
                            "OpGe" => bounds.push(NumericBound::Lower(rhs)),
                            "OpGt" => bounds.push(NumericBound::Lower(
                                smt_numeric_step(domain, rhs, 1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            "OpLe" => bounds.push(NumericBound::Upper(rhs)),
                            "OpLt" => bounds.push(NumericBound::Upper(
                                smt_numeric_step(domain, rhs, -1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            _ => return Ok(false),
                        }
                        return Ok(true);
                    }
                }
                if let IRExpr::Var { name, .. } = right.as_ref() {
                    if name == var && !ic3_expr_mentions_var(left, var) {
                        let lhs = encode_term(left, locals)?;
                        match op.as_str() {
                            "OpEq" => bounds.push(NumericBound::Exact(lhs)),
                            "OpLe" => bounds.push(NumericBound::Lower(lhs)),
                            "OpLt" => bounds.push(NumericBound::Lower(
                                smt_numeric_step(domain, lhs, 1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            "OpGe" => bounds.push(NumericBound::Upper(lhs)),
                            "OpGt" => bounds.push(NumericBound::Upper(
                                smt_numeric_step(domain, lhs, -1)
                                    .ok_or_else(|| "non-step numeric choose domain".to_owned())?,
                            )),
                            _ => return Ok(false),
                        }
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }

    fn synthesize_numeric_witness<F>(
        var: &str,
        domain: &IRType,
        predicate: Option<&IRExpr>,
        locals: &HashSet<String>,
        encode_term: &mut F,
    ) -> Result<Option<String>, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    {
        let mut bounds = Vec::new();
        if !collect_numeric_bounds(var, domain, predicate, locals, encode_term, &mut bounds)?
            || bounds.is_empty()
        {
            return Ok(None);
        }

        let mut exacts = Vec::new();
        let mut lowers = Vec::new();
        let mut uppers = Vec::new();
        for bound in bounds {
            match bound {
                NumericBound::Exact(term) => exacts.push(term),
                NumericBound::Lower(term) => lowers.push(term),
                NumericBound::Upper(term) => uppers.push(term),
            }
        }

        if let Some(exact) = exacts.into_iter().next() {
            return Ok(Some(exact));
        }
        if !lowers.is_empty() {
            let witness = lowers
                .into_iter()
                .reduce(smt_max)
                .expect("non-empty lowers checked");
            return Ok(Some(witness));
        }
        if !uppers.is_empty() {
            let witness = uppers
                .into_iter()
                .reduce(smt_min)
                .expect("non-empty uppers checked");
            return Ok(Some(witness));
        }
        Ok(None)
    }

    fn predicate_for_witness<G>(
        var: &str,
        predicate: &IRExpr,
        witness: &str,
        locals: &HashSet<String>,
        encode_predicate: &mut G,
    ) -> Result<String, String>
    where
        G: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
    {
        let mut scope = locals.clone();
        scope.insert(var.to_owned());
        let pred = encode_predicate(predicate, &scope)?;
        Ok(format!("(let (({var} {witness})) {pred})"))
    }

    fn collect_pattern_vars(pattern: &crate::ir::types::IRPattern, out: &mut HashSet<String>) {
        use crate::ir::types::IRPattern;
        match pattern {
            IRPattern::PVar { name } => {
                out.insert(name.clone());
            }
            IRPattern::PCtor { fields, .. } => {
                for field in fields {
                    collect_pattern_vars(&field.pattern, out);
                }
            }
            IRPattern::POr { left, right } => {
                collect_pattern_vars(left, out);
                collect_pattern_vars(right, out);
            }
            IRPattern::PWild => {}
        }
    }

    fn enum_variant_for_pattern<'a>(
        domain: &'a IRType,
        pattern_name: &str,
    ) -> Option<(String, &'a crate::ir::types::IRVariant)> {
        let IRType::Enum { variants, .. } = domain else {
            return None;
        };
        for variant in variants {
            if variant.name == pattern_name
                || pattern_name
                    .rsplit("::")
                    .next()
                    .is_some_and(|short| short == variant.name)
            {
                let ctor_name = pattern_name.rsplit("::").next().unwrap_or(pattern_name);
                return Some((ctor_name.to_owned(), variant));
            }
        }
        None
    }

    fn combine_guard_and_body(guard: Option<&IRExpr>, body: &IRExpr) -> IRExpr {
        match guard {
            Some(guard) => IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(guard.clone()),
                right: Box::new(body.clone()),
                ty: IRType::Bool,
                span: None,
            },
            None => body.clone(),
        }
    }

    fn synthesize_match_var_pattern_witness<F, H, J>(
        domain: &IRType,
        pattern: &crate::ir::types::IRPattern,
        arm_predicate: &IRExpr,
        locals: &HashSet<String>,
        encode_term: &mut F,
        encode_predicate: &mut impl FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        match_bindings: &mut H,
        match_cond: &mut J,
    ) -> Result<Option<String>, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        H: FnMut(
            &IRExpr,
            &crate::ir::types::IRPattern,
            &HashSet<String>,
        ) -> Result<Vec<(String, String)>, String>,
        J: FnMut(&IRExpr, &crate::ir::types::IRPattern, &HashSet<String>) -> Result<String, String>,
    {
        use crate::ir::types::IRPattern;

        match pattern {
            IRPattern::PWild => Ok(default_witness_for_type(domain)),
            IRPattern::PVar { name } => {
                let mut scope = locals.clone();
                scope.insert(name.clone());
                visit(
                    name,
                    domain,
                    Some(arm_predicate),
                    &scope,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )
            }
            IRPattern::PCtor { name, fields } => {
                let Some((ctor_name, variant)) = enum_variant_for_pattern(domain, name) else {
                    return Ok(None);
                };

                let mut scope = locals.clone();
                for field in fields {
                    collect_pattern_vars(&field.pattern, &mut scope);
                }

                let mut args = Vec::with_capacity(variant.fields.len());
                for variant_field in &variant.fields {
                    let pattern_field =
                        fields.iter().find(|field| field.name == variant_field.name);
                    let term = match pattern_field {
                        Some(field) => synthesize_match_var_pattern_witness(
                            &variant_field.ty,
                            &field.pattern,
                            arm_predicate,
                            &scope,
                            encode_term,
                            encode_predicate,
                            match_bindings,
                            match_cond,
                        )?,
                        None => default_witness_for_type(&variant_field.ty),
                    };
                    let Some(term) = term else {
                        return Ok(None);
                    };
                    args.push(term);
                }

                if args.is_empty() {
                    Ok(Some(ctor_name.to_owned()))
                } else {
                    Ok(Some(format!("({ctor_name} {})", args.join(" "))))
                }
            }
            IRPattern::POr { .. } => Ok(None),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn visit<F, H, J>(
        var: &str,
        domain: &IRType,
        predicate: Option<&IRExpr>,
        locals: &HashSet<String>,
        encode_term: &mut F,
        encode_predicate: &mut impl FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        match_bindings: &mut H,
        match_cond: &mut J,
    ) -> Result<Option<String>, String>
    where
        F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
        H: FnMut(
            &IRExpr,
            &crate::ir::types::IRPattern,
            &HashSet<String>,
        ) -> Result<Vec<(String, String)>, String>,
        J: FnMut(&IRExpr, &crate::ir::types::IRPattern, &HashSet<String>) -> Result<String, String>,
    {
        let Some(predicate) = predicate else {
            return Ok(None);
        };

        match predicate {
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpEq" => {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if name == var && !ic3_expr_mentions_var(right, var) {
                        return Ok(Some(encode_term(right, locals)?));
                    }
                }
                if let IRExpr::Var { name, .. } = right.as_ref() {
                    if name == var && !ic3_expr_mentions_var(left, var) {
                        return Ok(Some(encode_term(left, locals)?));
                    }
                }
                Ok(None)
            }
            IRExpr::BinOp {
                op, left, right, ..
            } if matches!(op.as_str(), "OpGe" | "OpGt" | "OpLe" | "OpLt") => {
                if let IRExpr::Var { name, .. } = left.as_ref() {
                    if name == var && !ic3_expr_mentions_var(right, var) {
                        let base = encode_term(right, locals)?;
                        return Ok(match op.as_str() {
                            "OpGe" | "OpLe" => Some(base),
                            "OpGt" => smt_numeric_step(domain, base, 1),
                            "OpLt" => smt_numeric_step(domain, base, -1),
                            _ => None,
                        });
                    }
                }
                if let IRExpr::Var { name, .. } = right.as_ref() {
                    if name == var && !ic3_expr_mentions_var(left, var) {
                        let base = encode_term(left, locals)?;
                        return Ok(match op.as_str() {
                            "OpLe" | "OpGe" => Some(base),
                            "OpLt" => smt_numeric_step(domain, base, 1),
                            "OpGt" => smt_numeric_step(domain, base, -1),
                            _ => None,
                        });
                    }
                }
                Ok(None)
            }
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpAnd" => {
                if let Some(witness) = visit(
                    var,
                    domain,
                    Some(left),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )? {
                    return Ok(Some(witness));
                }
                visit(
                    var,
                    domain,
                    Some(right),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )
            }
            IRExpr::BinOp {
                op, left, right, ..
            } if op == "OpOr" => {
                let left_witness = visit(
                    var,
                    domain,
                    Some(left),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                let right_witness = visit(
                    var,
                    domain,
                    Some(right),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                match (left_witness, right_witness) {
                    (Some(left_witness), Some(right_witness)) => {
                        let left_pred = predicate_for_witness(
                            var,
                            left,
                            &left_witness,
                            locals,
                            encode_predicate,
                        )?;
                        Ok(Some(format!(
                            "(ite {left_pred} {left_witness} {right_witness})"
                        )))
                    }
                    _ => Ok(None),
                }
            }
            IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => visit(
                var,
                domain,
                Some(expr),
                locals,
                encode_term,
                encode_predicate,
                match_bindings,
                match_cond,
            ),
            IRExpr::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } if !ic3_expr_mentions_var(cond, var) => {
                let Some(else_body) = else_body.as_deref() else {
                    return Ok(None);
                };
                let then_witness = visit(
                    var,
                    domain,
                    Some(then_body),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                let else_witness = visit(
                    var,
                    domain,
                    Some(else_body),
                    locals,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                match (then_witness, else_witness) {
                    (Some(then_witness), Some(else_witness)) => {
                        let cond_smt = encode_predicate(cond, locals)?;
                        Ok(Some(format!(
                            "(ite {cond_smt} {then_witness} {else_witness})"
                        )))
                    }
                    _ => Ok(None),
                }
            }
            IRExpr::Let { bindings, body, .. } => {
                let Some((binding, rest)) = bindings.split_first() else {
                    return visit(
                        var,
                        domain,
                        Some(body),
                        locals,
                        encode_term,
                        encode_predicate,
                        match_bindings,
                        match_cond,
                    );
                };
                if ic3_expr_mentions_var(&binding.expr, var) {
                    return Ok(None);
                }
                let rhs = if binding.ty == IRType::Bool {
                    encode_predicate(&binding.expr, locals)?
                } else {
                    encode_term(&binding.expr, locals)?
                };
                let mut scope = locals.clone();
                scope.insert(binding.name.clone());
                let rest_expr = if rest.is_empty() {
                    body.as_ref().clone()
                } else {
                    IRExpr::Let {
                        bindings: rest.to_vec(),
                        body: body.clone(),
                        span: None,
                    }
                };
                let witness = visit(
                    var,
                    domain,
                    Some(&rest_expr),
                    &scope,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?;
                Ok(
                    witness
                        .map(|witness| format!("(let (({} {})) {})", binding.name, rhs, witness)),
                )
            }
            IRExpr::Match {
                scrutinee, arms, ..
            } => {
                if matches!(scrutinee.as_ref(), IRExpr::Var { name, .. } if name == var) {
                    let mut candidates = Vec::new();
                    for arm in arms {
                        let arm_predicate = combine_guard_and_body(arm.guard.as_ref(), &arm.body);
                        if let Some(candidate) = synthesize_match_var_pattern_witness(
                            domain,
                            &arm.pattern,
                            &arm_predicate,
                            locals,
                            encode_term,
                            encode_predicate,
                            match_bindings,
                            match_cond,
                        )? {
                            candidates.push(candidate);
                        }
                    }
                    if candidates.is_empty() {
                        return Ok(None);
                    }
                    let mut witness = candidates
                        .last()
                        .expect("non-empty candidates checked")
                        .clone();
                    for candidate in candidates[..candidates.len().saturating_sub(1)]
                        .iter()
                        .rev()
                    {
                        let pred = predicate_for_witness(
                            var,
                            predicate,
                            candidate,
                            locals,
                            encode_predicate,
                        )?;
                        witness = format!("(ite {pred} {candidate} {witness})");
                    }
                    return Ok(Some(witness));
                }
                if ic3_expr_mentions_var(scrutinee, var) {
                    return Ok(None);
                }
                if !ic3_match_has_final_catch_all(arms) {
                    return Ok(None);
                }
                let last = arms.last().expect("checked non-empty match arms");
                let last_bindings = match_bindings(scrutinee, &last.pattern, locals)?;
                let mut last_scope = locals.clone();
                for (name, _) in &last_bindings {
                    last_scope.insert(name.clone());
                }
                let Some(last_body) = visit(
                    var,
                    domain,
                    Some(&last.body),
                    &last_scope,
                    encode_term,
                    encode_predicate,
                    match_bindings,
                    match_cond,
                )?
                else {
                    return Ok(None);
                };
                let mut acc = wrap_smt_let_bindings(&last_bindings, last_body);
                for arm in arms[..arms.len() - 1].iter().rev() {
                    let bindings = match_bindings(scrutinee, &arm.pattern, locals)?;
                    let mut scope = locals.clone();
                    for (name, _) in &bindings {
                        scope.insert(name.clone());
                    }
                    let Some(body_witness) = visit(
                        var,
                        domain,
                        Some(&arm.body),
                        &scope,
                        encode_term,
                        encode_predicate,
                        match_bindings,
                        match_cond,
                    )?
                    else {
                        return Ok(None);
                    };
                    let body = wrap_smt_let_bindings(&bindings, body_witness);
                    let pat = match_cond(scrutinee, &arm.pattern, locals)?;
                    let cond = if let Some(guard) = &arm.guard {
                        let guard_smt = encode_predicate(guard, &scope)?;
                        wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                    } else {
                        wrap_smt_let_bindings(&bindings, pat)
                    };
                    acc = format!("(ite {cond} {body} {acc})");
                }
                Ok(Some(acc))
            }
            _ => Ok(None),
        }
    }

    if matches!(
        domain,
        IRType::Int | IRType::Identity | IRType::Real | IRType::Float
    ) {
        if let Some(witness) =
            synthesize_numeric_witness(var, domain, predicate, locals, &mut encode_term)?
        {
            return Ok(Some(witness));
        }
    }

    if let Some(witness) = visit(
        var,
        domain,
        predicate,
        locals,
        &mut encode_term,
        &mut encode_predicate,
        &mut match_bindings,
        &mut match_cond,
    )? {
        return Ok(Some(witness));
    }

    Ok(None)
}

pub(in crate::verify::ic3) fn ic3_witness_binding_formula<F>(
    binding_name: &str,
    var: &str,
    witness: String,
    predicate: Option<&IRExpr>,
    locals: &HashSet<String>,
    mut encode_predicate: F,
    rest_smt: String,
) -> Result<String, String>
where
    F: FnMut(&IRExpr, &HashSet<String>) -> Result<String, String>,
{
    if let Some(predicate) = predicate {
        let mut pred_scope = locals.clone();
        pred_scope.insert(var.to_owned());
        let pred = encode_predicate(predicate, &pred_scope)?;
        return Ok(format!(
            "(let (({binding_name} {witness})) (and (let (({var} {binding_name})) {pred}) {rest_smt}))"
        ));
    }

    Ok(format!("(let (({binding_name} {witness})) {rest_smt})"))
}
