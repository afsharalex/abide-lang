use super::*;

pub(super) type EnumCatalog = HashMap<String, HashMap<String, i64>>;

pub(super) fn system_store_param_types(system: &IRSystem) -> HashMap<String, String> {
    system
        .store_params
        .iter()
        .map(|p| (p.name.clone(), p.entity_type.clone()))
        .collect()
}

pub(super) fn collect_unique_system_fields<'a>(
    systems: &'a [IRSystem],
) -> Result<Vec<(&'a str, &'a IRField)>, String> {
    let mut seen = HashMap::<String, String>::new();
    let mut ordered = Vec::new();
    for system in systems {
        for field in &system.fields {
            if let Some(prev) = seen.insert(field.name.clone(), system.name.clone()) {
                return Err(format!(
                    "cvc5 SyGuS pooled cross-call safety requires globally unique system field names; `{}` appears in both `{}` and `{}`",
                    field.name, prev, system.name
                ));
            }
            ordered.push((system.name.as_str(), field));
        }
    }
    Ok(ordered)
}

pub fn try_cvc5_sygus_single_entity(
    entity: &IREntity,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_single_entity_inner(entity, property, timeout_ms) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

pub fn try_cvc5_sygus_system_safety(
    system: &IRSystem,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_system_safety_inner(system, property, timeout_ms) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_pooled_system_safety(
    system: &IRSystem,
    entity: &IREntity,
    n_slots: usize,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_pooled_system_safety_inner(system, entity, n_slots, property, timeout_ms) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

pub(super) fn try_cvc5_sygus_single_entity_inner(
    entity: &IREntity,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    if !entity.derived_fields.is_empty() {
        return Err(
            "cvc5 SyGuS single-entity safety does not support derived fields yet".to_owned(),
        );
    }
    if !entity.fsm_decls.is_empty() {
        return Err(
            "cvc5 SyGuS single-entity safety does not support FSM declarations yet".to_owned(),
        );
    }

    let start = Instant::now();
    let tm = Cvc5Tm::new();
    let mut solver = Cvc5Solver::new(&tm);
    solver.set_option("sygus", "true");
    solver.set_option("incremental", "false");
    if timeout_ms > 0 {
        solver.set_option("tlimit-per", &timeout_ms.to_string());
    }
    solver.set_logic("LIA");

    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    let mut curr_order = Vec::with_capacity(entity.fields.len());
    let mut next_order = Vec::with_capacity(entity.fields.len());
    let enum_catalog = build_enum_catalog(&entity.fields)?;

    for field in &entity.fields {
        let sort = sort_for_field(&tm, field)?;
        let curr = tm.mk_var(sort.clone(), &field.name);
        let next = tm.mk_var(sort, &format!("{}_next", field.name));
        curr_vars.insert(field.name.clone(), curr.clone());
        next_vars.insert(field.name.clone(), next.clone());
        curr_order.push(curr);
        next_order.push(next);
    }

    let pre_body = mk_and(
        &tm,
        &entity
            .fields
            .iter()
            .map(|field| encode_initial_field(&tm, field, &curr_vars, &enum_catalog))
            .collect::<Result<Vec<_>, _>>()?,
    );

    let trans_clauses = entity
        .transitions
        .iter()
        .map(|trans| {
            encode_transition(
                &tm,
                trans,
                &entity.fields,
                &curr_vars,
                &next_vars,
                &enum_catalog,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if trans_clauses.is_empty() {
        return Err("cvc5 SyGuS single-entity safety requires at least one transition".to_owned());
    }
    let trans_body = mk_or(&tm, &trans_clauses);

    let property_body = encode_expr(
        &tm,
        &safety_obligation_expr(property, &entity.invariants),
        &curr_vars,
        &enum_catalog,
    )?;

    let bool_sort = tm.boolean_sort();
    let mut trans_params = curr_order.clone();
    trans_params.extend(next_order.iter().cloned());

    let pre_fun = solver.define_fun("pre_abide", &curr_order, bool_sort.clone(), pre_body, false);
    let trans_fun = solver.define_fun(
        "trans_abide",
        &trans_params,
        bool_sort.clone(),
        trans_body,
        false,
    );
    let post_fun = solver.define_fun(
        "post_abide",
        &curr_order,
        bool_sort.clone(),
        property_body,
        false,
    );
    let inv_fun = solver.synth_fun("inv_abide", &curr_order, bool_sort);

    solver.add_sygus_inv_constraint(inv_fun.clone(), pre_fun, trans_fun, post_fun);

    let result = solver.check_synth();
    if result.has_solution() {
        let _solution = solver.get_synth_solution(inv_fun);
        let _elapsed = start.elapsed();
        Ok(())
    } else if result.is_unknown() {
        Err(format!(
            "cvc5 SyGuS returned Unknown for single-entity safety ({result})"
        ))
    } else if result.has_no_solution() {
        Err(
            "cvc5 SyGuS found no invariant solution for the supported single-entity safety slice"
                .to_owned(),
        )
    } else {
        Err(format!(
            "cvc5 SyGuS returned an unrecognized result: {result}"
        ))
    }
}

pub(super) fn try_cvc5_sygus_system_safety_inner(
    system: &IRSystem,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    if !system.store_params.is_empty() {
        return Err("cvc5 SyGuS system safety does not support store params yet".to_owned());
    }
    if !system.entities.is_empty() {
        return Err("cvc5 SyGuS system safety does not support entity pools yet".to_owned());
    }
    if !system.commands.is_empty() {
        return Err(
            "cvc5 SyGuS system safety does not support command declarations yet".to_owned(),
        );
    }
    if !system.fsm_decls.is_empty() {
        return Err("cvc5 SyGuS system safety does not support FSM declarations yet".to_owned());
    }
    if !system.derived_fields.is_empty() {
        return Err("cvc5 SyGuS system safety does not support derived fields yet".to_owned());
    }
    if !system.queries.is_empty() || !system.preds.is_empty() || !system.let_bindings.is_empty() {
        return Err(
            "cvc5 SyGuS system safety does not support queries/preds/let-bindings yet".to_owned(),
        );
    }
    let tm = Cvc5Tm::new();
    let mut solver = Cvc5Solver::new(&tm);
    solver.set_option("sygus", "true");
    solver.set_option("incremental", "false");
    if timeout_ms > 0 {
        solver.set_option("tlimit-per", &timeout_ms.to_string());
    }
    solver.set_logic("LIA");

    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    let mut curr_order = Vec::with_capacity(system.fields.len());
    let mut next_order = Vec::with_capacity(system.fields.len());
    let enum_catalog = build_enum_catalog(&system.fields)?;

    for field in &system.fields {
        let sort = sort_for_field(&tm, field)?;
        let curr = tm.mk_var(sort.clone(), &field.name);
        let next = tm.mk_var(sort, &format!("{}_next", field.name));
        curr_vars.insert(field.name.clone(), curr.clone());
        next_vars.insert(field.name.clone(), next.clone());
        curr_order.push(curr);
        next_order.push(next);
    }

    let pre_body = mk_and(
        &tm,
        &system
            .fields
            .iter()
            .map(|field| encode_initial_field(&tm, field, &curr_vars, &enum_catalog))
            .collect::<Result<Vec<_>, _>>()?,
    );

    let trans_clauses = system
        .actions
        .iter()
        .map(|step| {
            encode_system_step(
                &tm,
                step,
                &system.fields,
                &curr_vars,
                &next_vars,
                &enum_catalog,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if trans_clauses.is_empty() {
        return Err("cvc5 SyGuS system safety requires at least one step".to_owned());
    }
    let trans_body = mk_or(&tm, &trans_clauses);

    let property_body = encode_expr(
        &tm,
        &safety_obligation_expr(property, &system.invariants),
        &curr_vars,
        &enum_catalog,
    )?;

    let bool_sort = tm.boolean_sort();
    let mut trans_params = curr_order.clone();
    trans_params.extend(next_order.iter().cloned());

    let pre_fun = solver.define_fun("pre_abide", &curr_order, bool_sort.clone(), pre_body, false);
    let trans_fun = solver.define_fun(
        "trans_abide",
        &trans_params,
        bool_sort.clone(),
        trans_body,
        false,
    );
    let post_fun = solver.define_fun(
        "post_abide",
        &curr_order,
        bool_sort.clone(),
        property_body,
        false,
    );
    let inv_fun = solver.synth_fun("inv_abide", &curr_order, bool_sort);

    solver.add_sygus_inv_constraint(inv_fun.clone(), pre_fun, trans_fun, post_fun);

    let result = solver.check_synth();
    if result.has_solution() {
        let _solution = solver.get_synth_solution(inv_fun);
        Ok(())
    } else if result.is_unknown() {
        Err(format!(
            "cvc5 SyGuS returned Unknown for system safety ({result})"
        ))
    } else if result.has_no_solution() {
        Err(
            "cvc5 SyGuS found no invariant solution for the supported system safety slice"
                .to_owned(),
        )
    } else {
        Err(format!(
            "cvc5 SyGuS returned an unrecognized result: {result}"
        ))
    }
}

pub(super) fn property_body(property: &IRExpr) -> &IRExpr {
    match property {
        IRExpr::Always { body, .. } => body.as_ref(),
        other => other,
    }
}

pub(super) fn safety_obligation_expr(
    property: &IRExpr,
    invariants: &[crate::ir::types::IRInvariant],
) -> IRExpr {
    let mut conjuncts = Vec::with_capacity(invariants.len() + 1);
    conjuncts.push(property_body(property).clone());
    conjuncts.extend(invariants.iter().map(|inv| inv.body.clone()));
    match conjuncts.len() {
        0 => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        1 => conjuncts.remove(0),
        _ => fold_and(conjuncts),
    }
}

pub(super) fn fold_and(mut exprs: Vec<IRExpr>) -> IRExpr {
    let first = exprs.remove(0);
    exprs.into_iter().fold(first, |lhs, rhs| IRExpr::BinOp {
        op: "OpAnd".to_owned(),
        left: Box::new(lhs),
        right: Box::new(rhs),
        ty: IRType::Bool,
        span: None,
    })
}

pub(super) fn build_enum_catalog(fields: &[IRField]) -> Result<EnumCatalog, String> {
    let mut catalog = HashMap::new();
    for field in fields {
        if let IRType::Enum { name, variants } = &field.ty {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                return Err(format!(
                    "cvc5 SyGuS safety only supports fieldless enums today (field `{}`)",
                    field.name
                ));
            }
            let mut mapping = HashMap::new();
            for (idx, variant) in variants.iter().enumerate() {
                mapping.insert(variant.name.clone(), idx as i64);
            }
            catalog.insert(name.clone(), mapping);
        }
    }
    Ok(catalog)
}

pub(super) fn sort_for_field(tm: &Cvc5Tm, field: &IRField) -> Result<cvc5_rs::Sort, String> {
    match &field.ty {
        IRType::Int => Ok(tm.integer_sort()),
        IRType::Bool => Ok(tm.boolean_sort()),
        IRType::Enum { variants, .. }
            if variants.iter().all(|variant| variant.fields.is_empty()) =>
        {
            Ok(tm.integer_sort())
        }
        _ => Err(format!(
            "cvc5 SyGuS safety only supports Int/Bool/fieldless-enum fields today (field `{}`)",
            field.name
        )),
    }
}

pub(super) fn encode_initial_field(
    tm: &Cvc5Tm,
    field: &IRField,
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    if field.initial_constraint.is_some() {
        return Err(format!(
            "cvc5 SyGuS single-entity safety does not support initial constraints yet (field `{}`)",
            field.name
        ));
    }
    let current = curr_vars
        .get(&field.name)
        .ok_or_else(|| format!("missing current variable for field `{}`", field.name))?;
    let default = field.default.as_ref().ok_or_else(|| {
        format!(
            "field `{}` needs a deterministic default for SyGuS",
            field.name
        )
    })?;
    let encoded = encode_expr(tm, default, curr_vars, enum_catalog)?;
    Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[current.clone(), encoded]))
}

pub(super) fn encode_transition(
    tm: &Cvc5Tm,
    trans: &IRTransition,
    fields: &[IRField],
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    if !trans.refs.is_empty() {
        return Err(format!(
            "cvc5 SyGuS single-entity safety does not support transition refs yet (`{}`)",
            trans.name
        ));
    }
    if trans.postcondition.is_some() {
        return Err(format!(
            "cvc5 SyGuS single-entity safety does not support transition postconditions yet (`{}`)",
            trans.name
        ));
    }

    let param_envs = enumerate_param_envs(tm, &trans.params, enum_catalog)?;
    let update_map: HashMap<_, _> = trans
        .updates
        .iter()
        .map(|upd| (upd.field.as_str(), &upd.value))
        .collect();
    let mut param_branches = Vec::with_capacity(param_envs.len());
    for param_env in param_envs {
        let mut scoped = curr_vars.clone();
        scoped.extend(param_env);

        let mut conjuncts = vec![encode_expr(tm, &trans.guard, &scoped, enum_catalog)?];
        for field in fields {
            let next = next_vars
                .get(&field.name)
                .ok_or_else(|| format!("missing next variable for field `{}`", field.name))?;
            let rhs = if let Some(expr) = update_map.get(field.name.as_str()) {
                encode_expr(tm, expr, &scoped, enum_catalog)?
            } else {
                curr_vars
                    .get(&field.name)
                    .ok_or_else(|| format!("missing current variable for field `{}`", field.name))?
                    .clone()
            };
            conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), rhs]));
        }
        param_branches.push(mk_and(tm, &conjuncts));
    }

    Ok(mk_or(tm, &param_branches))
}

pub(super) fn encode_system_step(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    fields: &[IRField],
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    if step.return_expr.is_some() {
        return Err(format!(
            "cvc5 SyGuS system safety does not support action return expressions yet (`{}`)",
            step.name
        ));
    }

    let param_envs = enumerate_param_envs(tm, &step.params, enum_catalog)?;
    let mut param_branches = Vec::with_capacity(param_envs.len());
    for param_env in param_envs {
        let mut scoped = curr_vars.clone();
        scoped.extend(param_env);

        let mut conjuncts = vec![encode_expr(tm, &step.guard, &scoped, enum_catalog)?];
        let update_map = collect_system_updates(tm, step, &scoped, enum_catalog)?;

        for field in fields {
            let next = next_vars
                .get(&field.name)
                .ok_or_else(|| format!("missing next variable for field `{}`", field.name))?;
            let rhs = update_map.get(&field.name).cloned().unwrap_or_else(|| {
                curr_vars
                    .get(&field.name)
                    .expect("missing current variable for field")
                    .clone()
            });
            conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), rhs]));
        }
        param_branches.push(mk_and(tm, &conjuncts));
    }

    Ok(mk_or(tm, &param_branches))
}

pub(super) fn collect_system_updates(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<HashMap<String, Cvc5Term>, String> {
    let mut updates = HashMap::new();
    for action in &step.body {
        let crate::ir::types::IRAction::ExprStmt { expr } = action else {
            return Err(format!(
                "cvc5 SyGuS system safety only supports ExprStmt step bodies today (`{}`)",
                step.name
            ));
        };
        let IRExpr::BinOp {
            op, left, right, ..
        } = expr
        else {
            return Err(format!(
                "cvc5 SyGuS system safety expects primed equality statements (`{}`)",
                step.name
            ));
        };
        if op != "OpEq" && op != "==" {
            return Err(format!(
                "cvc5 SyGuS system safety expects primed equality statements (`{}`)",
                step.name
            ));
        }
        let IRExpr::Prime { expr: primed, .. } = left.as_ref() else {
            return Err(format!(
                "cvc5 SyGuS system safety expects a primed lhs in ExprStmt (`{}`)",
                step.name
            ));
        };
        let IRExpr::Var { name, .. } = primed.as_ref() else {
            return Err(format!(
                "cvc5 SyGuS system safety only supports primed system field vars on the lhs (`{}`)",
                step.name
            ));
        };
        let rhs_term = encode_expr(tm, right, curr_vars, enum_catalog)?;
        updates.insert(name.clone(), rhs_term);
    }
    Ok(updates)
}

pub(super) fn enumerate_param_envs(
    tm: &Cvc5Tm,
    params: &[IRTransParam],
    enum_catalog: &EnumCatalog,
) -> Result<Vec<HashMap<String, Cvc5Term>>, String> {
    let mut envs = vec![HashMap::new()];
    for param in params {
        let values = finite_param_values(tm, param, enum_catalog)?;
        let mut next_envs = Vec::with_capacity(envs.len() * values.len());
        for env in &envs {
            for value in &values {
                let mut extended = env.clone();
                extended.insert(param.name.clone(), value.clone());
                next_envs.push(extended);
            }
        }
        envs = next_envs;
    }
    Ok(envs)
}

pub(super) fn finite_param_values(
    tm: &Cvc5Tm,
    param: &IRTransParam,
    enum_catalog: &EnumCatalog,
) -> Result<Vec<Cvc5Term>, String> {
    finite_domain_values(tm, &param.ty, enum_catalog).ok_or_else(|| {
        format!(
            "cvc5 SyGuS system safety only supports Bool and fieldless-enum action params today (`{}`)",
            param.name
        )
    })
}

pub(super) fn finite_domain_values(
    tm: &Cvc5Tm,
    domain: &IRType,
    enum_catalog: &EnumCatalog,
) -> Option<Vec<Cvc5Term>> {
    match domain {
        IRType::Bool => Some(vec![tm.mk_boolean(false), tm.mk_boolean(true)]),
        IRType::Enum { name, variants }
            if variants.iter().all(|variant| variant.fields.is_empty()) =>
        {
            let mapping = enum_catalog.get(name)?;
            let mut values: Vec<_> = variants
                .iter()
                .map(|variant| mapping.get(&variant.name).map(|idx| tm.mk_integer(*idx)))
                .collect::<Option<Vec<_>>>()?;
            if values.is_empty() {
                return None;
            }
            Some(std::mem::take(&mut values))
        }
        _ => None,
    }
}

pub(super) fn encode_finite_quantifier_expr(
    tm: &Cvc5Tm,
    kind: &str,
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
        return Err(
            "cvc5 SyGuS only supports Bool and fieldless-enum domains for finite quantifiers"
                .to_owned(),
        );
    };

    let mut bodies = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let mut scoped = vars.clone();
        scoped.insert(var.to_owned(), candidate);
        bodies.push(encode_expr(tm, body, &scoped, enum_catalog)?);
    }

    match kind {
        "forall" => Ok(mk_and(tm, &bodies)),
        "exists" => Ok(mk_or(tm, &bodies)),
        "one" => {
            if bodies.is_empty() {
                return Ok(tm.mk_boolean(false));
            }
            let mut disjuncts = Vec::new();
            for i in 0..bodies.len() {
                let mut conjuncts = vec![bodies[i].clone()];
                for (j, body_j) in bodies.iter().enumerate() {
                    if i != j {
                        conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[body_j.clone()]));
                    }
                }
                disjuncts.push(mk_and(tm, &conjuncts));
            }
            Ok(mk_or(tm, &disjuncts))
        }
        "lone" => {
            if bodies.len() <= 1 {
                return Ok(tm.mk_boolean(true));
            }
            let mut conjuncts = Vec::new();
            for i in 0..bodies.len() {
                for j in (i + 1)..bodies.len() {
                    let both = mk_and(tm, &[bodies[i].clone(), bodies[j].clone()]);
                    conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[both]));
                }
            }
            Ok(mk_and(tm, &conjuncts))
        }
        _ => Err(format!(
            "unknown finite quantifier kind in cvc5 SyGuS slice: {kind}"
        )),
    }
}

pub(super) fn sygus_expr_type(expr: &IRExpr) -> Option<&IRType> {
    match expr {
        IRExpr::Lit { ty, .. }
        | IRExpr::Var { ty, .. }
        | IRExpr::BinOp { ty, .. }
        | IRExpr::UnOp { ty, .. }
        | IRExpr::Field { ty, .. }
        | IRExpr::Choose { ty, .. }
        | IRExpr::MapUpdate { ty, .. }
        | IRExpr::Index { ty, .. }
        | IRExpr::SetLit { ty, .. }
        | IRExpr::SeqLit { ty, .. }
        | IRExpr::MapLit { ty, .. }
        | IRExpr::SetComp { ty, .. } => Some(ty),
        IRExpr::Prime { expr, .. } => sygus_expr_type(expr),
        IRExpr::Let { body, .. } => sygus_expr_type(body),
        IRExpr::Ctor { .. } => None,
        _ => None,
    }
}

pub(super) fn sygus_match_scrutinee_type(expr: &IRExpr) -> Option<IRType> {
    match expr {
        IRExpr::Ctor { enum_name, .. } => Some(IRType::Enum {
            name: enum_name.clone(),
            variants: vec![],
        }),
        other => sygus_expr_type(other).cloned(),
    }
}

pub(super) fn pattern_binders(pattern: &crate::ir::types::IRPattern, into: &mut Vec<String>) {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PVar { name } => into.push(name.clone()),
        IRPattern::PWild => {}
        IRPattern::PCtor { fields, .. } => {
            for field in fields {
                pattern_binders(&field.pattern, into);
            }
        }
        IRPattern::POr { left, right } => {
            pattern_binders(left, into);
            pattern_binders(right, into);
        }
    }
}

pub(super) fn bind_pattern_vars(
    pattern: &crate::ir::types::IRPattern,
    scrut: &Cvc5Term,
    env: &mut HashMap<String, Cvc5Term>,
) -> Result<(), String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild => Ok(()),
        IRPattern::PVar { name } => {
            env.insert(name.clone(), scrut.clone());
            Ok(())
        }
        IRPattern::PCtor { name, fields } => {
            if !fields.is_empty() {
                return Err(format!(
                    "cvc5 SyGuS match does not support constructor-field destructuring yet (`{name}`)"
                ));
            }
            Ok(())
        }
        IRPattern::POr { left, right } => {
            let mut left_names = Vec::new();
            let mut right_names = Vec::new();
            pattern_binders(left, &mut left_names);
            pattern_binders(right, &mut right_names);
            left_names.sort();
            right_names.sort();
            if left_names != right_names {
                return Err(
                    "cvc5 SyGuS match requires aligned or-pattern binders when bindings are present"
                        .to_owned(),
                );
            }
            bind_pattern_vars(left, scrut, env)
        }
    }
}

pub(super) fn encode_pattern_cond(
    tm: &Cvc5Tm,
    pattern: &crate::ir::types::IRPattern,
    scrutinee: &Cvc5Term,
    scrut_ty: Option<&IRType>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild | IRPattern::PVar { .. } => Ok(tm.mk_boolean(true)),
        IRPattern::PCtor { name, fields } => {
            if !fields.is_empty() {
                return Err(format!(
                    "cvc5 SyGuS match does not support constructor-field patterns yet (`{name}`)"
                ));
            }
            let idx = match scrut_ty {
                Some(IRType::Enum { name: enum_name, .. }) => enum_catalog
                    .get(enum_name)
                    .and_then(|mapping| {
                        mapping
                            .get(name)
                            .or_else(|| name.split_once("::").and_then(|(_, ctor)| mapping.get(ctor)))
                    })
                    .copied()
                    .ok_or_else(|| {
                        format!(
                            "unsupported enum constructor pattern `{name}` in cvc5 SyGuS slice"
                        )
                    })?,
                _ => {
                    return Err(format!(
                        "constructor pattern `{name}` requires a fieldless-enum scrutinee in cvc5 SyGuS"
                    ))
                }
            };
            Ok(tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[scrutinee.clone(), tm.mk_integer(idx)],
            ))
        }
        IRPattern::POr { left, right } => {
            let lhs = encode_pattern_cond(tm, left, scrutinee, scrut_ty, enum_catalog)?;
            let rhs = encode_pattern_cond(tm, right, scrutinee, scrut_ty, enum_catalog)?;
            Ok(mk_or(tm, &[lhs, rhs]))
        }
    }
}

pub(super) fn encode_match_expr(
    tm: &Cvc5Tm,
    scrutinee: &IRExpr,
    arms: &[crate::ir::types::IRMatchArm],
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    if arms.is_empty() {
        return Err("cvc5 SyGuS match requires at least one arm".to_owned());
    }
    let scrut_term = encode_expr(tm, scrutinee, vars, enum_catalog)?;
    let scrut_ty = sygus_expr_type(scrutinee);

    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_env = vars.clone();
        bind_pattern_vars(&arm.pattern, &scrut_term, &mut arm_env)?;
        let pat_cond = encode_pattern_cond(tm, &arm.pattern, &scrut_term, scrut_ty, enum_catalog)?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_expr(tm, guard, &arm_env, enum_catalog)?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_body = encode_expr(tm, &arm.body, &arm_env, enum_catalog)?;
        fallback = Some(match fallback {
            None => {
                if arm.guard.is_none()
                    && matches!(
                        arm.pattern,
                        crate::ir::types::IRPattern::PWild
                            | crate::ir::types::IRPattern::PVar { .. }
                    )
                {
                    arm_body
                } else {
                    return Err(
                        "cvc5 SyGuS match requires a final wildcard or var fallback arm".to_owned(),
                    );
                }
            }
            Some(else_term) => {
                tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[arm_cond, arm_body, else_term])
            }
        });
    }

    fallback.ok_or_else(|| "cvc5 SyGuS match required at least one arm".to_owned())
}

pub(super) fn encode_expr(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => Ok(tm.mk_integer(*value)),
            LitVal::Bool { value } => Ok(tm.mk_boolean(*value)),
            LitVal::Real { .. } | LitVal::Float { .. } | LitVal::Str { .. } => Err(
                "cvc5 SyGuS single-entity safety only supports integer and boolean literals today"
                    .to_owned(),
            ),
        },
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            if !args.is_empty() {
                return Err(format!(
                    "cvc5 SyGuS safety does not support payload constructors yet (`{enum_name}::{ctor}`)"
                ));
            }
            let idx = enum_catalog
                .get(enum_name)
                .and_then(|mapping| mapping.get(ctor))
                .ok_or_else(|| {
                    format!("unsupported enum constructor `{enum_name}::{ctor}` in SyGuS slice")
                })?;
            Ok(tm.mk_integer(*idx))
        }
        IRExpr::Var { name, .. } => vars
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unsupported free variable `{name}` in SyGuS slice")),
        IRExpr::UnOp { op, operand, .. } => {
            let inner = encode_expr(tm, operand, vars, enum_catalog)?;
            match op.as_str() {
                "OpNot" | "not" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[inner])),
                "OpNeg" | "-" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NEG, &[inner])),
                _ => Err(format!("unsupported unary op `{op}` in cvc5 SyGuS slice")),
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let lhs = encode_expr(tm, left, vars, enum_catalog)?;
            let rhs = encode_expr(tm, right, vars, enum_catalog)?;
            match op.as_str() {
                "OpAnd" | "and" => Ok(mk_and(tm, &[lhs, rhs])),
                "OpOr" | "or" => Ok(mk_or(tm, &[lhs, rhs])),
                "OpImplies" | "implies" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[lhs, rhs])),
                "OpEq" | "==" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[lhs, rhs])),
                "OpNEq" | "!=" => Ok(tm.mk_term(
                    Cvc5Kind::CVC5_KIND_NOT,
                    &[tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[lhs, rhs])],
                )),
                "OpLt" | "<" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_LT, &[lhs, rhs])),
                "OpLe" | "<=" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_LEQ, &[lhs, rhs])),
                "OpGt" | ">" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_GT, &[lhs, rhs])),
                "OpGe" | ">=" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_GEQ, &[lhs, rhs])),
                "OpAdd" | "+" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ADD, &[lhs, rhs])),
                "OpSub" | "-" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_SUB, &[lhs, rhs])),
                "OpMul" | "*" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_MULT, &[lhs, rhs])),
                _ => Err(format!("unsupported binary op `{op}` in cvc5 SyGuS slice")),
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut local = vars.clone();
            for binding in bindings {
                let value = encode_expr(tm, &binding.expr, &local, enum_catalog)?;
                local.insert(binding.name.clone(), value);
            }
            encode_expr(tm, body, &local, enum_catalog)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            encode_expr(tm, expr, vars, enum_catalog)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond = encode_expr(tm, cond, vars, enum_catalog)?;
            let then_term = encode_expr(tm, then_body, vars, enum_catalog)?;
            let else_term = encode_expr(
                tm,
                else_body.as_deref().ok_or_else(|| {
                    "cvc5 SyGuS slice requires an explicit else branch".to_owned()
                })?,
                vars,
                enum_catalog,
            )?;
            Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[cond, then_term, else_term]))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => encode_match_expr(tm, scrutinee, arms, vars, enum_catalog),
        IRExpr::Forall {
            var, domain, body, ..
        } => encode_finite_quantifier_expr(tm, "forall", var, domain, body, vars, enum_catalog),
        IRExpr::Exists {
            var, domain, body, ..
        } => encode_finite_quantifier_expr(tm, "exists", var, domain, body, vars, enum_catalog),
        IRExpr::One {
            var, domain, body, ..
        } => encode_finite_quantifier_expr(tm, "one", var, domain, body, vars, enum_catalog),
        IRExpr::Lone {
            var, domain, body, ..
        } => encode_finite_quantifier_expr(tm, "lone", var, domain, body, vars, enum_catalog),
        _ => Err(format!(
            "unsupported expression kind in cvc5 SyGuS single-entity safety slice: {expr:?}"
        )),
    }
}

pub(super) fn mk_and(tm: &Cvc5Tm, args: &[Cvc5Term]) -> Cvc5Term {
    match args {
        [] => tm.mk_boolean(true),
        [only] => only.clone(),
        many => tm.mk_term(Cvc5Kind::CVC5_KIND_AND, many),
    }
}

pub(super) fn mk_or(tm: &Cvc5Tm, args: &[Cvc5Term]) -> Cvc5Term {
    match args {
        [] => tm.mk_boolean(false),
        [only] => only.clone(),
        many => tm.mk_term(Cvc5Kind::CVC5_KIND_OR, many),
    }
}
