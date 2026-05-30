use super::*;

#[allow(clippy::format_push_string)]
pub(in crate::verify::ic3) fn build_chc_string_with_semantics(
    entity: &IREntity,
    vctx: &VerifyContext,
    property: &IRExpr,
    semantics: Ic3TransitionSemantics,
) -> Result<String, String> {
    let mut chc = String::new();
    emit_ic3_datatype_decls_with_expr(
        entity.fields.iter().map(|field| &field.ty),
        property,
        &mut chc,
    );

    // Field sorts for State relation
    let field_sorts: Vec<String> = entity
        .fields
        .iter()
        .map(|f| ir_type_to_sort_name(&f.ty))
        .collect();

    // Declare State relation: State(f1,..., fn, active)
    chc.push_str("(declare-rel State (");
    for s in &field_sorts {
        chc.push_str(s);
        chc.push(' ');
    }
    chc.push_str("Bool))\n");

    // Declare Error relation
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables for each field + active flag
    for (i, f) in entity.fields.iter().enumerate() {
        chc.push_str(&format!(
            "(declare-var f{} {})\n",
            i,
            ir_type_to_sort_name(&f.ty)
        ));
    }
    chc.push_str("(declare-var active Bool)\n");
    let n = entity.fields.len();
    let vars: Vec<String> = (0..n).map(|i| format!("f{i}")).collect();
    let vars_str = vars.join(" ");

    // ── Initial state ──────────────────────────────────────────────
    // State(defaults..., false) — entity starts inactive
    chc.push_str("(rule (State ");
    for (i, f) in entity.fields.iter().enumerate() {
        if let Some(ref default_expr) = f.default {
            chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
        } else {
            // No default: field is unconstrained at init.
            // Use the declared variable so the rule is universally quantified over it.
            chc.push_str(&format!("f{i}"));
        }
        chc.push(' ');
    }
    chc.push_str("false) init)\n");

    // ── Create rule ────────────────────────────────────────────────
    // State(f0,..., fn, false) → State(defaults_or_vars, true)
    chc.push_str(&format!("(rule (=> (State {vars_str} false) (State "));
    for (i, f) in entity.fields.iter().enumerate() {
        if let Some(ref default_expr) = f.default {
            chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
        } else {
            // No default: created entity gets unconstrained field value
            chc.push_str(&format!("f{i}"));
        }
        chc.push(' ');
    }
    chc.push_str("true)) create)\n");

    // ── Transition rules ───────────────────────────────────────────
    let mut enabled_steps = vec!["(not active)".to_owned()];
    for transition in &entity.transitions {
        let guard_smt = guard_to_smt(&transition.guard, entity, vctx)?;
        enabled_steps.push(format!("(and active {guard_smt})"));

        // Build next-state: updates override, frame preserves
        let mut next_fields: Vec<String> = Vec::new();
        for (i, f) in entity.fields.iter().enumerate() {
            let updated = transition.updates.iter().find(|u| u.field == f.name);
            if let Some(upd) = updated {
                next_fields.push(expr_to_smt(&upd.value, entity, vctx)?);
            } else {
                next_fields.push(format!("f{i}")); // frame
            }
        }
        let next_str = next_fields.join(" ");

        chc.push_str(&format!(
            "(rule (=> (and (State {vars_str} active) active {guard_smt}) \
             (State {next_str} true)) trans_{})\n",
            transition.name
        ));
    }

    // ── Stutter rule ───────────────────────────────────────────────
    if semantics.allow_stutter {
        chc.push_str(&format!(
            "(rule (=> (State {vars_str} active) (State {vars_str} active)) stutter)\n"
        ));
    } else {
        let no_enabled = enabled_steps
            .iter()
            .map(|enabled| format!("(not {enabled})"))
            .collect::<Vec<_>>()
            .join(" ");
        chc.push_str(&format!(
            "(rule (=> (and (State {vars_str} active) {no_enabled}) Error) \
             deadlock_no_stutter)\n"
        ));
    }

    // ── Domain constraints for enum fields ─────────────────────────
    for (fi, f) in entity.fields.iter().enumerate() {
        if let IRType::Enum { name, variants } = &f.ty {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                continue;
            }
            if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                chc.push_str(&format!(
                    "(rule (=> (and (State {vars_str} active) active \
                     (or (< f{fi} {min_id}) (> f{fi} {max_id}))) Error) domain_f{fi})\n"
                ));
            }
        }
    }

    // ── Error rule ─────────────────────────────────────────────────
    let neg_prop = negate_property_smt(property, entity, vctx)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {vars_str} active) active {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}

/// Convert an IR type to an SMT-LIB2 sort name.
#[allow(clippy::match_same_arms)]
pub(in crate::verify::ic3) fn ir_type_to_sort_name(ty: &IRType) -> String {
    match ty {
        IRType::Int | IRType::Identity => "Int".to_owned(),
        IRType::Bool => "Bool".to_owned(),
        IRType::Real | IRType::Float => "Real".to_owned(),
        IRType::Enum { name, variants } => {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                name.clone()
            } else {
                "Int".to_owned()
            }
        }
        IRType::Map { key, value } => {
            format!(
                "(Array {} {})",
                ir_type_to_sort_name(key),
                ir_type_to_sort_name(value)
            )
        }
        IRType::Set { element } => {
            format!("(Array {} Bool)", ir_type_to_sort_name(element))
        }
        IRType::Seq { element } => {
            format!("(Array Int {})", ir_type_to_sort_name(element))
        }
        _ => "Int".to_owned(),
    }
}

pub(in crate::verify::ic3) fn collect_ic3_datatype_enums<'a>(
    ty: &'a IRType,
    out: &mut HashMap<String, &'a IRType>,
) {
    match ty {
        IRType::Enum { name, variants }
            if variants.iter().any(|variant| !variant.fields.is_empty()) =>
        {
            out.entry(name.clone()).or_insert(ty);
            for variant in variants {
                for field in &variant.fields {
                    collect_ic3_datatype_enums(&field.ty, out);
                }
            }
        }
        IRType::Map { key, value } => {
            collect_ic3_datatype_enums(key, out);
            collect_ic3_datatype_enums(value, out);
        }
        IRType::Set { element }
        | IRType::Seq { element }
        | IRType::Refinement { base: element, .. } => {
            collect_ic3_datatype_enums(element, out);
        }
        IRType::Tuple { elements } => {
            for element in elements {
                collect_ic3_datatype_enums(element, out);
            }
        }
        _ => {}
    }
}

pub(in crate::verify::ic3) fn collect_ic3_expr_datatype_enums<'a>(
    expr: &'a IRExpr,
    out: &mut HashMap<String, &'a IRType>,
) {
    if let Some(ty) = ic3_expr_type(expr) {
        collect_ic3_datatype_enums(ty, out);
    }

    match expr {
        IRExpr::Prime { expr, .. }
        | IRExpr::UnOp { operand: expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. }
        | IRExpr::Card { expr, .. } => collect_ic3_expr_datatype_enums(expr, out),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            collect_ic3_expr_datatype_enums(left, out);
            collect_ic3_expr_datatype_enums(right, out);
        }
        IRExpr::Field { expr, .. } => collect_ic3_expr_datatype_enums(expr, out),
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_ic3_expr_datatype_enums(cond, out);
            collect_ic3_expr_datatype_enums(then_body, out);
            if let Some(else_body) = else_body {
                collect_ic3_expr_datatype_enums(else_body, out);
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            for binding in bindings {
                collect_ic3_datatype_enums(&binding.ty, out);
                collect_ic3_expr_datatype_enums(&binding.expr, out);
            }
            collect_ic3_expr_datatype_enums(body, out);
        }
        IRExpr::Forall { domain, body, .. }
        | IRExpr::Exists { domain, body, .. }
        | IRExpr::One { domain, body, .. }
        | IRExpr::Lone { domain, body, .. }
        | IRExpr::Aggregate { domain, body, .. } => {
            collect_ic3_datatype_enums(domain, out);
            collect_ic3_expr_datatype_enums(body, out);
            if let IRExpr::Aggregate {
                in_filter: Some(in_filter),
                ..
            } = expr
            {
                collect_ic3_expr_datatype_enums(in_filter, out);
            }
        }
        IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. } => collect_ic3_expr_datatype_enums(body, out),
        IRExpr::Choose {
            domain, predicate, ..
        } => {
            collect_ic3_datatype_enums(domain, out);
            if let Some(predicate) = predicate {
                collect_ic3_expr_datatype_enums(predicate, out);
            }
        }
        IRExpr::SetComp {
            domain,
            source,
            filter,
            projection,
            ..
        } => {
            collect_ic3_datatype_enums(domain, out);
            if let Some(source) = source {
                collect_ic3_expr_datatype_enums(source, out);
            }
            collect_ic3_expr_datatype_enums(filter, out);
            if let Some(projection) = projection {
                collect_ic3_expr_datatype_enums(projection, out);
            }
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            collect_ic3_expr_datatype_enums(projection, out);
            for binding in bindings {
                collect_ic3_datatype_enums(&binding.domain, out);
                if let Some(source) = &binding.source {
                    collect_ic3_expr_datatype_enums(source, out);
                }
            }
            collect_ic3_expr_datatype_enums(filter, out);
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            collect_ic3_expr_datatype_enums(map, out);
            collect_ic3_expr_datatype_enums(key, out);
            collect_ic3_expr_datatype_enums(value, out);
        }
        IRExpr::Index { map, key, .. } => {
            collect_ic3_expr_datatype_enums(map, out);
            collect_ic3_expr_datatype_enums(key, out);
        }
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => {
            for element in elements {
                collect_ic3_expr_datatype_enums(element, out);
            }
        }
        IRExpr::MapLit { entries, .. } => {
            for (key, value) in entries {
                collect_ic3_expr_datatype_enums(key, out);
                collect_ic3_expr_datatype_enums(value, out);
            }
        }
        IRExpr::Ctor { args, .. } => {
            for (_, arg) in args {
                collect_ic3_expr_datatype_enums(arg, out);
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_ic3_expr_datatype_enums(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_ic3_expr_datatype_enums(guard, out);
                }
                collect_ic3_expr_datatype_enums(&arm.body, out);
            }
        }
        IRExpr::App { func, arg, .. } => {
            collect_ic3_expr_datatype_enums(func, out);
            collect_ic3_expr_datatype_enums(arg, out);
        }
        IRExpr::Block { exprs, .. } => {
            for expr in exprs {
                collect_ic3_expr_datatype_enums(expr, out);
            }
        }
        IRExpr::VarDecl { ty, init, rest, .. } => {
            collect_ic3_datatype_enums(ty, out);
            collect_ic3_expr_datatype_enums(init, out);
            collect_ic3_expr_datatype_enums(rest, out);
        }
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            collect_ic3_expr_datatype_enums(cond, out);
            for invariant in invariants {
                collect_ic3_expr_datatype_enums(invariant, out);
            }
            collect_ic3_expr_datatype_enums(body, out);
        }
        IRExpr::Saw { args, .. } => {
            for arg in args.iter().flatten() {
                collect_ic3_expr_datatype_enums(arg, out);
            }
        }
        IRExpr::Lit { .. }
        | IRExpr::Var { .. }
        | IRExpr::Lam { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => {}
    }
}

pub(in crate::verify::ic3) fn emit_ic3_datatype_decls_with_expr<'a, I>(
    types: I,
    expr: &'a IRExpr,
    chc: &mut String,
) where
    I: IntoIterator<Item = &'a IRType>,
{
    let mut enums = HashMap::new();
    for ty in types {
        collect_ic3_datatype_enums(ty, &mut enums);
    }
    collect_ic3_expr_datatype_enums(expr, &mut enums);

    let mut enums: Vec<_> = enums.into_iter().collect();
    enums.sort_by(|(left, _), (right, _)| left.cmp(right));

    for (_, ty) in enums {
        let IRType::Enum { name, variants } = ty else {
            continue;
        };
        chc.push_str("(declare-datatypes () ((");
        chc.push_str(name);
        for variant in variants {
            chc.push_str(" (");
            chc.push_str(&variant.name);
            for field in &variant.fields {
                chc.push_str(" (");
                chc.push_str(&field.name);
                chc.push(' ');
                chc.push_str(&ir_type_to_sort_name(&field.ty));
                chc.push(')');
            }
            chc.push(')');
        }
        chc.push_str(")))\n");
    }
}

pub(in crate::verify::ic3) fn wrap_smt_let_bindings(
    bindings: &[(String, String)],
    inner: String,
) -> String {
    let mut out = String::new();
    for (name, value) in bindings {
        out.push_str(&format!("(let (({name} {value})) "));
    }
    out.push_str(&inner);
    for _ in bindings {
        out.push(')');
    }
    out
}
