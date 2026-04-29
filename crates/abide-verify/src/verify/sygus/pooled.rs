use super::*;

struct PooledSyGuSCtx<'a> {
    slots_per_entity: &'a HashMap<String, usize>,
    active_vars: &'a HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_fields: &'a HashMap<String, Cvc5Term>,
    store_param_types: &'a HashMap<String, String>,
}

type PooledEntityBindings = HashMap<String, (String, usize)>;

struct PooledCrossCallCapture {
    formula: Cvc5Term,
    return_value: Option<Cvc5Term>,
    return_type: Option<IRType>,
}

#[derive(Clone)]
struct PooledLocalBinding {
    term: Cvc5Term,
    ty: Option<IRType>,
}

type PooledLocalBindings = HashMap<String, PooledLocalBinding>;

struct PooledActionResult {
    formula: Cvc5Term,
    locals: PooledLocalBindings,
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_multi_pooled_system_safety(
    system: &IRSystem,
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_multi_pooled_system_safety_inner(
        system,
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    ) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

pub fn try_cvc5_sygus_multi_system_pooled_safety(
    root_system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Ic3Result {
    if !cvc5_sygus_enabled() {
        return Ic3Result::Unknown(cvc5_sygus_disabled_reason());
    }
    match try_cvc5_sygus_multi_system_pooled_safety_inner(
        root_system,
        systems,
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    ) {
        Ok(()) => Ic3Result::Proved,
        Err(err) => Ic3Result::Unknown(err),
    }
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_pooled_system_safety_inner(
    system: &IRSystem,
    entity: &IREntity,
    n_slots: usize,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    let mut slots_per_entity = HashMap::new();
    slots_per_entity.insert(entity.name.clone(), n_slots);
    try_cvc5_sygus_multi_pooled_system_safety_inner(
        system,
        std::slice::from_ref(entity),
        &slots_per_entity,
        property,
        timeout_ms,
    )
}

#[cfg(test)]
pub(super) fn try_cvc5_sygus_multi_pooled_system_safety_inner(
    system: &IRSystem,
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    try_cvc5_sygus_multi_system_pooled_safety_inner(
        system,
        std::slice::from_ref(system),
        entities,
        slots_per_entity,
        property,
        timeout_ms,
    )
}

fn try_cvc5_sygus_multi_system_pooled_safety_inner(
    root_system: &IRSystem,
    systems: &[IRSystem],
    entities: &[IREntity],
    slots_per_entity: &HashMap<String, usize>,
    property: &IRExpr,
    timeout_ms: u64,
) -> Result<(), String> {
    let entities_by_name: HashMap<_, _> = entities.iter().map(|e| (e.name.clone(), e)).collect();
    let systems_by_name: HashMap<_, _> = systems.iter().map(|s| (s.name.clone(), s)).collect();
    if root_system.entities.is_empty() {
        return Err(
            "cvc5 SyGuS pooled system safety needs at least one pooled entity type".to_owned(),
        );
    }
    for entity_name in &root_system.entities {
        if !entities_by_name.contains_key(entity_name) {
            return Err(format!(
                "cvc5 SyGuS pooled system safety is missing pooled entity metadata for `{entity_name}`"
            ));
        }
        if !slots_per_entity.contains_key(entity_name) {
            return Err(format!(
                "cvc5 SyGuS pooled system safety is missing slot scope for `{entity_name}`"
            ));
        }
    }
    for system in systems {
        for store_param in &system.store_params {
            if !entities_by_name.contains_key(&store_param.entity_type) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing pooled entity metadata for store param `{}` -> `{}` in `{}`",
                    store_param.name, store_param.entity_type, system.name
                ));
            }
            if !slots_per_entity.contains_key(&store_param.entity_type) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing slot scope for store param `{}` -> `{}` in `{}`",
                    store_param.name, store_param.entity_type, system.name
                ));
            }
        }
    }
    if !root_system.commands.is_empty() {
        return Err(
            "cvc5 SyGuS pooled system safety does not support command declarations yet".to_owned(),
        );
    }
    if !root_system.fsm_decls.is_empty()
        || entities.iter().any(|entity| !entity.fsm_decls.is_empty())
    {
        return Err(
            "cvc5 SyGuS pooled system safety does not support FSM declarations yet".to_owned(),
        );
    }
    if !root_system.derived_fields.is_empty()
        || entities
            .iter()
            .any(|entity| !entity.derived_fields.is_empty())
    {
        return Err(
            "cvc5 SyGuS pooled system safety does not support derived fields yet".to_owned(),
        );
    }
    if !root_system.queries.is_empty()
        || !root_system.preds.is_empty()
        || !root_system.let_bindings.is_empty()
    {
        return Err(
            "cvc5 SyGuS pooled system safety does not support queries/preds/let-bindings yet"
                .to_owned(),
        );
    }
    for system in systems {
        if !system.commands.is_empty() {
            return Err(format!(
                "cvc5 SyGuS pooled system safety does not support command declarations yet (`{}`)",
                system.name
            ));
        }
        if !system.fsm_decls.is_empty() {
            return Err(format!(
                "cvc5 SyGuS pooled system safety does not support FSM declarations yet (`{}`)",
                system.name
            ));
        }
        if !system.derived_fields.is_empty() {
            return Err(format!(
                "cvc5 SyGuS pooled system safety does not support derived fields yet (`{}`)",
                system.name
            ));
        }
        if !system.queries.is_empty() || !system.preds.is_empty() || !system.let_bindings.is_empty()
        {
            return Err(format!(
                "cvc5 SyGuS pooled system safety does not support queries/preds/let-bindings yet (`{}`)",
                system.name
            ));
        }
        for entity_name in &system.entities {
            if !entities_by_name.contains_key(entity_name) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing pooled entity metadata for `{entity_name}`"
                ));
            }
            if !slots_per_entity.contains_key(entity_name) {
                return Err(format!(
                    "cvc5 SyGuS pooled system safety is missing slot scope for `{entity_name}`"
                ));
            }
        }
    }
    if entities.iter().any(|entity| {
        entity
            .fields
            .iter()
            .any(|field| field.initial_constraint.is_some() || field.default.is_none())
    }) {
        return Err(
            "cvc5 SyGuS pooled system safety requires deterministic entity defaults and no initial constraints"
                .to_owned(),
        );
    }
    if slots_per_entity.values().any(|n_slots| *n_slots == 0) {
        return Err(
            "cvc5 SyGuS pooled system safety needs at least one slot for every pooled entity type"
                .to_owned(),
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

    let ordered_system_fields = collect_unique_system_fields(systems)?;
    let all_fields: Vec<IRField> = ordered_system_fields
        .iter()
        .map(|(_, field)| (*field).clone())
        .chain(
            entities
                .iter()
                .flat_map(|entity| entity.fields.iter().cloned()),
        )
        .collect();
    let enum_catalog = build_enum_catalog(&all_fields)?;

    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    let mut curr_order = Vec::new();
    let mut next_order = Vec::new();

    for (_, field) in &ordered_system_fields {
        let sort = sort_for_field(&tm, field)?;
        let curr = tm.mk_var(sort.clone(), &field.name);
        let next = tm.mk_var(sort, &format!("{}_next", field.name));
        curr_vars.insert(field.name.clone(), curr.clone());
        next_vars.insert(field.name.clone(), next.clone());
        curr_order.push(curr);
        next_order.push(next);
    }

    let mut active_curr: HashMap<String, HashMap<usize, Cvc5Term>> = HashMap::new();
    let mut active_next: HashMap<String, HashMap<usize, Cvc5Term>> = HashMap::new();
    let mut slot_curr = HashMap::new();
    let mut slot_next = HashMap::new();
    for entity_name in slots_per_entity.keys() {
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        let n_slots = *slots_per_entity
            .get(entity_name)
            .ok_or_else(|| format!("missing slot count for pooled entity `{entity_name}`"))?;
        let mut entity_active_curr = HashMap::new();
        let mut entity_active_next = HashMap::new();
        for slot in 0..n_slots {
            let active = tm.mk_var(
                tm.boolean_sort(),
                &format!("{}_{}_active", entity.name, slot),
            );
            let active_n = tm.mk_var(
                tm.boolean_sort(),
                &format!("{}_{}_active_next", entity.name, slot),
            );
            entity_active_curr.insert(slot, active.clone());
            entity_active_next.insert(slot, active_n.clone());
            curr_order.push(active);
            next_order.push(active_n);

            for field in &entity.fields {
                let sort = sort_for_field(&tm, field)?;
                let curr = tm.mk_var(
                    sort.clone(),
                    &format!("{}_{}_{}", entity.name, slot, field.name),
                );
                let next = tm.mk_var(
                    sort,
                    &format!("{}_{}_{}_next", entity.name, slot, field.name),
                );
                slot_curr.insert(
                    pool_slot_field_key(&entity.name, slot, &field.name),
                    curr.clone(),
                );
                slot_next.insert(
                    pool_slot_field_key(&entity.name, slot, &field.name),
                    next.clone(),
                );
                curr_order.push(curr);
                next_order.push(next);
            }
        }
        active_curr.insert(entity.name.clone(), entity_active_curr);
        active_next.insert(entity.name.clone(), entity_active_next);
    }

    let store_param_types = system_store_param_types(root_system);

    let pre_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: &active_curr,
        slot_fields: &slot_curr,
        store_param_types: &store_param_types,
    };
    let mut pre_conjuncts = ordered_system_fields
        .iter()
        .map(|(_, field)| encode_initial_field(&tm, field, &curr_vars, &enum_catalog))
        .collect::<Result<Vec<_>, _>>()?;
    for entity_name in slots_per_entity.keys() {
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        let n_slots = *slots_per_entity
            .get(entity_name)
            .ok_or_else(|| format!("missing slot count for pooled entity `{entity_name}`"))?;
        for slot in 0..n_slots {
            pre_conjuncts.push(
                tm.mk_term(
                    Cvc5Kind::CVC5_KIND_NOT,
                    &[active_curr
                        .get(entity_name)
                        .and_then(|slots| slots.get(&slot))
                        .ok_or_else(|| {
                            format!("missing active variable for {entity_name} slot {slot}")
                        })?
                        .clone()],
                ),
            );
            for field in &entity.fields {
                let next = slot_curr
                    .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                    .ok_or_else(|| {
                        format!(
                            "missing pooled field `{}` for {entity_name} slot {slot}",
                            field.name
                        )
                    })?;
                let default = field
                    .default
                    .as_ref()
                    .expect("checked deterministic default");
                let encoded = encode_pooled_expr(
                    &tm,
                    default,
                    &curr_vars,
                    &HashMap::new(),
                    &pre_ctx,
                    &enum_catalog,
                )?;
                pre_conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), encoded]));
            }
        }
    }
    let pre_body = mk_and(&tm, &pre_conjuncts);

    let trans_clauses = root_system
        .actions
        .iter()
        .map(|step| {
            encode_pooled_system_step(
                &tm,
                step,
                root_system,
                &systems_by_name,
                &entities_by_name,
                slots_per_entity,
                &curr_vars,
                &next_vars,
                &active_curr,
                &active_next,
                &slot_curr,
                &slot_next,
                &enum_catalog,
                &[root_system.name.clone()],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if trans_clauses.is_empty() {
        return Err("cvc5 SyGuS pooled system safety requires at least one step".to_owned());
    }
    let trans_body = mk_or(&tm, &trans_clauses);

    let prop_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: &active_curr,
        slot_fields: &slot_curr,
        store_param_types: &store_param_types,
    };
    let property_body = encode_pooled_expr(
        &tm,
        &safety_obligation_expr(property, &root_system.invariants),
        &curr_vars,
        &HashMap::new(),
        &prop_ctx,
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
            "cvc5 SyGuS returned Unknown for pooled system safety ({result})"
        ))
    } else if result.has_no_solution() {
        Err(
            "cvc5 SyGuS found no invariant solution for the supported pooled-system safety slice"
                .to_owned(),
        )
    } else {
        Err(format!(
            "cvc5 SyGuS returned an unrecognized result: {result}"
        ))
    }
}

fn pool_slot_field_key(entity: &str, slot: usize, field: &str) -> String {
    format!("{entity}:{slot}:{field}")
}

fn frame_pooled_slot(
    tm: &Cvc5Tm,
    entity: &IREntity,
    slot: usize,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
) -> Result<Cvc5Term, String> {
    let mut conjuncts = vec![tm.mk_term(
        Cvc5Kind::CVC5_KIND_EQUAL,
        &[
            active_next
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing next active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
            active_curr
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing current active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
        ],
    )];
    for field in &entity.fields {
        conjuncts.push(
            tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[
                    slot_next
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                        .clone(),
                    slot_curr
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                        .clone(),
                ],
            ),
        );
    }
    Ok(mk_and(tm, &conjuncts))
}

fn frame_other_pooled_slots(
    tm: &Cvc5Tm,
    entity: &IREntity,
    excluded_slot: usize,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    n_slots: usize,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for slot in 0..n_slots {
        if slot == excluded_slot {
            continue;
        }
        frames.push(frame_pooled_slot(
            tm,
            entity,
            slot,
            active_curr,
            active_next,
            slot_curr,
            slot_next,
        )?);
    }
    Ok(frames)
}

fn frame_other_pooled_entities(
    tm: &Cvc5Tm,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    excluded_entity: &str,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for (entity_name, n_slots) in slots_per_entity {
        if entity_name == excluded_entity {
            continue;
        }
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        for slot in 0..*n_slots {
            frames.push(frame_pooled_slot(
                tm,
                entity,
                slot,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            )?);
        }
    }
    Ok(frames)
}

fn frame_all_system_fields(
    tm: &Cvc5Tm,
    systems_by_name: &HashMap<String, &IRSystem>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for system in systems_by_name.values() {
        for field in &system.fields {
            let curr = curr_vars.get(&field.name).ok_or_else(|| {
                format!(
                    "missing current system field `{}` for `{}`",
                    field.name, system.name
                )
            })?;
            let next = next_vars.get(&field.name).ok_or_else(|| {
                format!(
                    "missing next system field `{}` for `{}`",
                    field.name, system.name
                )
            })?;
            frames.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[next.clone(), curr.clone()]));
        }
    }
    Ok(frames)
}

fn frame_all_pooled_entities(
    tm: &Cvc5Tm,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
) -> Result<Vec<Cvc5Term>, String> {
    let mut frames = Vec::new();
    for (entity_name, n_slots) in slots_per_entity {
        let entity = entities_by_name
            .get(entity_name)
            .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
        for slot in 0..*n_slots {
            frames.push(frame_pooled_slot(
                tm,
                entity,
                slot,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            )?);
        }
    }
    Ok(frames)
}

fn resolve_pooled_ref_bindings(
    trans: &IRTransition,
    apply_refs: &[String],
    available_bindings: &PooledEntityBindings,
) -> Result<PooledEntityBindings, String> {
    if trans.refs.len() != apply_refs.len() {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expected {} refs for transition `{}`, got {}",
            trans.refs.len(),
            trans.name,
            apply_refs.len()
        ));
    }

    let mut resolved = HashMap::new();
    for (ref_decl, apply_ref_name) in trans.refs.iter().zip(apply_refs.iter()) {
        let binding = available_bindings.get(apply_ref_name).ok_or_else(|| {
            format!(
                "unknown pooled ref binding `{apply_ref_name}` for transition `{}`",
                trans.name
            )
        })?;
        if binding.0 != ref_decl.entity {
            return Err(format!(
                "cvc5 SyGuS pooled system safety expected ref `{}` on transition `{}` to bind entity `{}`, got `{}`",
                ref_decl.name, trans.name, ref_decl.entity, binding.0
            ));
        }
        resolved.insert(ref_decl.name.clone(), binding.clone());
    }
    Ok(resolved)
}

fn override_pooled_slot_fields(
    base: &HashMap<String, Cvc5Term>,
    entity: &IREntity,
    slot: usize,
    overrides: &HashMap<String, Cvc5Term>,
) -> HashMap<String, Cvc5Term> {
    let mut map = base.clone();
    for field in &entity.fields {
        if let Some(value) = overrides.get(&field.name) {
            map.insert(
                pool_slot_field_key(&entity.name, slot, &field.name),
                value.clone(),
            );
        }
    }
    map
}

fn mk_exists(tm: &Cvc5Tm, vars: &[Cvc5Term], body: Cvc5Term) -> Cvc5Term {
    if vars.is_empty() {
        body
    } else {
        let var_list = tm.mk_term(Cvc5Kind::CVC5_KIND_VARIABLE_LIST, vars);
        tm.mk_term(Cvc5Kind::CVC5_KIND_EXISTS, &[var_list, body])
    }
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_ops_for_target(
    tm: &Cvc5Tm,
    target_var: &str,
    target_entity: &IREntity,
    target_slot: usize,
    ops: &[IRAction],
    _system: &IRSystem,
    _systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    pool_ctx: &PooledSyGuSCtx<'_>,
    _call_stack: &[String],
) -> Result<Cvc5Term, String> {
    if ops.is_empty() {
        return Err("cvc5 SyGuS pooled system safety requires at least one nested op".to_owned());
    }
    if ops.len() > 1
        && ops.iter().all(|op| {
            matches!(
                op,
                IRAction::Apply {
                    target,
                    transition: _,
                    refs: _,
                    args: _,
                } if target == target_var
            )
        })
    {
        let mut intermediates = Vec::new();
        let mut bound = Vec::new();
        for stage in 0..(ops.len() - 1) {
            let mut fields = HashMap::new();
            for field in &target_entity.fields {
                let sort = sort_for_field(tm, field)?;
                let name = format!(
                    "__abide_sygus_{}_slot{}_{}_inter{}",
                    target_entity.name, target_slot, field.name, stage
                );
                let term = tm.mk_var(sort, &name);
                bound.push(term.clone());
                fields.insert(field.name.clone(), term);
            }
            intermediates.push(fields);
        }

        let mut conjuncts = Vec::new();
        for (idx, op) in ops.iter().enumerate() {
            let IRAction::Apply {
                target,
                transition,
                refs,
                args,
            } = op
            else {
                unreachable!("checked apply-only chain above");
            };
            if target != target_var {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports apply on the selected target variable"
                        .to_owned(),
                );
            }
            let trans = target_entity
                .transitions
                .iter()
                .find(|trans| trans.name == *transition)
                .ok_or_else(|| {
                    format!(
                        "unknown transition `{transition}` on `{}`",
                        target_entity.name
                    )
                })?;
            let mut resolved_bindings = entity_bindings.clone();
            resolved_bindings.extend(resolve_pooled_ref_bindings(trans, refs, entity_bindings)?);

            let read_target_fields = if idx == 0 {
                None
            } else {
                Some(&intermediates[idx - 1])
            };
            let write_target_fields = if idx + 1 == ops.len() {
                None
            } else {
                Some(&intermediates[idx])
            };

            let stage_read_fields = if let Some(overrides) = read_target_fields {
                override_pooled_slot_fields(slot_curr, target_entity, target_slot, overrides)
            } else {
                slot_curr.clone()
            };
            let stage_write_fields = if let Some(overrides) = write_target_fields {
                override_pooled_slot_fields(slot_next, target_entity, target_slot, overrides)
            } else {
                slot_next.clone()
            };
            let stage_pool_ctx = PooledSyGuSCtx {
                slots_per_entity: pool_ctx.slots_per_entity,
                active_vars: pool_ctx.active_vars,
                slot_fields: &stage_read_fields,
                store_param_types: pool_ctx.store_param_types,
            };
            let stage_active_next = if idx + 1 == ops.len() {
                active_next
            } else {
                active_curr
            };
            conjuncts.push(encode_pooled_transition_at_slot(
                tm,
                trans,
                target_entity,
                target_slot,
                args,
                vars,
                &resolved_bindings,
                stage_active_next,
                &stage_read_fields,
                &stage_write_fields,
                enum_catalog,
                &stage_pool_ctx,
            )?);
        }
        return Ok(mk_exists(tm, &bound, mk_and(tm, &conjuncts)));
    }
    match &ops[0] {
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => {
            if target != target_var {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports apply on the selected target variable"
                        .to_owned(),
                );
            }
            let trans = target_entity
                .transitions
                .iter()
                .find(|trans| trans.name == *transition)
                .ok_or_else(|| {
                    format!(
                        "unknown transition `{transition}` on `{}`",
                        target_entity.name
                    )
                })?;
            let mut resolved_bindings = entity_bindings.clone();
            resolved_bindings.extend(resolve_pooled_ref_bindings(trans, refs, entity_bindings)?);
            encode_pooled_transition_at_slot(
                tm,
                trans,
                target_entity,
                target_slot,
                args,
                vars,
                &resolved_bindings,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                pool_ctx,
            )
        }
        IRAction::Choose {
            var,
            entity: choose_entity,
            filter,
            ops: inner_ops,
        } => {
            entities_by_name
                .get(choose_entity)
                .ok_or_else(|| format!("unknown pooled entity `{choose_entity}`"))?;
            let n_slots = *slots_per_entity
                .get(choose_entity)
                .ok_or_else(|| format!("missing slot scope for `{choose_entity}`"))?;
            let mut branches = Vec::new();
            for slot in 0..n_slots {
                let mut bindings = entity_bindings.clone();
                bindings.insert(var.clone(), (choose_entity.clone(), slot));
                branches.push(mk_and(
                    tm,
                    &[
                        active_curr
                            .get(choose_entity)
                            .and_then(|slots| slots.get(&slot))
                            .ok_or_else(|| {
                                format!(
                                    "missing current active variable for {choose_entity} slot {slot}"
                                )
                            })?
                            .clone(),
                        encode_pooled_expr(tm, filter, vars, &bindings, pool_ctx, enum_catalog)?,
                        encode_pooled_ops_for_target(
                            tm,
                            target_var,
                            target_entity,
                            target_slot,
                            inner_ops,
                            _system,
                            _systems_by_name,
                            entities_by_name,
                            slots_per_entity,
                            vars,
                            &bindings,
                            active_curr,
                            active_next,
                            slot_curr,
                            slot_next,
                            enum_catalog,
                            pool_ctx,
                            _call_stack,
                        )?,
                    ],
                ));
            }
            Ok(mk_or(tm, &branches))
        }
        other => Err(format!(
            "cvc5 SyGuS pooled system safety does not support nested op `{other:?}` yet"
        )),
    }
}

fn encode_pooled_transition_at_slot(
    tm: &Cvc5Tm,
    trans: &IRTransition,
    entity: &IREntity,
    slot: usize,
    apply_args: &[IRExpr],
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    pool_ctx: &PooledSyGuSCtx<'_>,
) -> Result<Cvc5Term, String> {
    if trans.params.len() != apply_args.len() {
        return Err(format!(
            "cvc5 SyGuS pooled system safety expected {} args for transition `{}`, got {}",
            trans.params.len(),
            trans.name,
            apply_args.len()
        ));
    }
    if trans.postcondition.is_some() {
        return Err(format!(
            "cvc5 SyGuS pooled system safety does not support transition postconditions yet (`{}`)",
            trans.name
        ));
    }

    let mut scoped = vars.clone();
    for field in &entity.fields {
        scoped.insert(
            field.name.clone(),
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone(),
        );
    }
    for (param, arg) in trans.params.iter().zip(apply_args.iter()) {
        let arg_term =
            encode_pooled_expr(tm, arg, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
        scoped.insert(param.name.clone(), arg_term);
    }

    let mut conjuncts = vec![encode_pooled_expr(
        tm,
        &trans.guard,
        &scoped,
        entity_bindings,
        pool_ctx,
        enum_catalog,
    )?];
    conjuncts.push(
        active_next
            .get(&entity.name)
            .and_then(|slots| slots.get(&slot))
            .ok_or_else(|| {
                format!(
                    "missing next active variable for {} slot {slot}",
                    entity.name
                )
            })?
            .clone(),
    );
    let update_map: HashMap<_, _> = trans
        .updates
        .iter()
        .map(|upd| (upd.field.as_str(), &upd.value))
        .collect();
    for field in &entity.fields {
        let rhs = if let Some(expr) = update_map.get(field.name.as_str()) {
            encode_pooled_expr(tm, expr, &scoped, entity_bindings, pool_ctx, enum_catalog)?
        } else {
            slot_curr
                .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                .ok_or_else(|| format!("missing current pooled field `{}`", field.name))?
                .clone()
        };
        conjuncts.push(
            tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[
                    slot_next
                        .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                        .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                        .clone(),
                    rhs,
                ],
            ),
        );
    }

    Ok(mk_and(tm, &conjuncts))
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_create_action(
    tm: &Cvc5Tm,
    create_entity: &str,
    create_fields: &[IRCreateField],
    system: &IRSystem,
    entity: &IREntity,
    vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    n_slots: usize,
) -> Result<Cvc5Term, String> {
    if create_entity != entity.name {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports creates for `{}`",
            entity.name
        ));
    }

    let create_map: HashMap<_, _> = create_fields
        .iter()
        .map(|field| (field.name.as_str(), &field.value))
        .collect();
    let local_slots_per_entity = HashMap::from([(entity.name.clone(), n_slots)]);
    let local_store_param_types = system_store_param_types(system);
    let pre_ctx = PooledSyGuSCtx {
        slots_per_entity: &local_slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &local_store_param_types,
    };
    let mut branches = Vec::new();
    for slot in 0..n_slots {
        let mut conjuncts = vec![tm.mk_term(
            Cvc5Kind::CVC5_KIND_NOT,
            &[active_curr
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing current active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone()],
        )];
        conjuncts.push(
            active_next
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing next active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
        );
        for field in &entity.fields {
            let rhs = if let Some(expr) = create_map.get(field.name.as_str()) {
                encode_pooled_expr(tm, expr, vars, &HashMap::new(), &pre_ctx, enum_catalog)?
            } else {
                encode_pooled_expr(
                    tm,
                    field
                        .default
                        .as_ref()
                        .expect("checked deterministic default"),
                    vars,
                    &HashMap::new(),
                    &pre_ctx,
                    enum_catalog,
                )?
            };
            conjuncts.push(
                tm.mk_term(
                    Cvc5Kind::CVC5_KIND_EQUAL,
                    &[
                        slot_next
                            .get(&pool_slot_field_key(&entity.name, slot, &field.name))
                            .ok_or_else(|| format!("missing next pooled field `{}`", field.name))?
                            .clone(),
                        rhs,
                    ],
                ),
            );
        }
        conjuncts.extend(frame_other_pooled_slots(
            tm,
            entity,
            slot,
            active_curr,
            active_next,
            slot_curr,
            slot_next,
            n_slots,
        )?);
        branches.push(mk_and(tm, &conjuncts));
    }
    Ok(mk_or(tm, &branches))
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_choose_action(
    tm: &Cvc5Tm,
    var: &str,
    choose_entity: &str,
    filter: &IRExpr,
    ops: &[IRAction],
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entity: &IREntity,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    n_slots: usize,
    call_stack: &[String],
) -> Result<Cvc5Term, String> {
    if choose_entity != entity.name {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports chooses over `{}`",
            entity.name
        ));
    }
    if !system.fields.is_empty() {
        // system fields remain framed for this slice
    }
    let store_param_types = system_store_param_types(system);
    let pool_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &store_param_types,
    };
    let mut branches = Vec::new();
    for slot in 0..n_slots {
        let mut bindings = HashMap::new();
        bindings.insert(var.to_owned(), (entity.name.clone(), slot));
        let mut conjuncts = vec![
            active_curr
                .get(&entity.name)
                .and_then(|slots| slots.get(&slot))
                .ok_or_else(|| {
                    format!(
                        "missing current active variable for {} slot {slot}",
                        entity.name
                    )
                })?
                .clone(),
            encode_pooled_expr(tm, filter, vars, &bindings, &pool_ctx, enum_catalog)?,
            encode_pooled_ops_for_target(
                tm,
                var,
                entity,
                slot,
                ops,
                system,
                systems_by_name,
                entities_by_name,
                slots_per_entity,
                vars,
                &bindings,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                &pool_ctx,
                call_stack,
            )?,
        ];
        conjuncts.extend(frame_other_pooled_slots(
            tm,
            entity,
            slot,
            active_curr,
            active_next,
            slot_curr,
            slot_next,
            n_slots,
        )?);
        branches.push(mk_and(tm, &conjuncts));
    }
    Ok(mk_or(tm, &branches))
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_forall_action(
    tm: &Cvc5Tm,
    var: &str,
    forall_entity: &str,
    ops: &[IRAction],
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entity: &IREntity,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    n_slots: usize,
    call_stack: &[String],
) -> Result<Cvc5Term, String> {
    if forall_entity != entity.name {
        return Err(format!(
            "cvc5 SyGuS pooled system safety only supports forall over `{}`",
            entity.name
        ));
    }
    let store_param_types = system_store_param_types(system);
    let pool_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &store_param_types,
    };
    let mut conjuncts = Vec::new();
    for slot in 0..n_slots {
        let active = active_curr
            .get(&entity.name)
            .and_then(|slots| slots.get(&slot))
            .ok_or_else(|| {
                format!(
                    "missing current active variable for {} slot {slot}",
                    entity.name
                )
            })?
            .clone();
        let mut bindings = HashMap::new();
        bindings.insert(var.to_owned(), (entity.name.clone(), slot));
        let active_branch = mk_and(
            tm,
            &[
                active.clone(),
                encode_pooled_ops_for_target(
                    tm,
                    var,
                    entity,
                    slot,
                    ops,
                    system,
                    systems_by_name,
                    entities_by_name,
                    slots_per_entity,
                    vars,
                    &bindings,
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                    enum_catalog,
                    &pool_ctx,
                    call_stack,
                )?,
            ],
        );
        let inactive_branch = mk_and(
            tm,
            &[
                tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[active]),
                frame_pooled_slot(
                    tm,
                    entity,
                    slot,
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                )?,
            ],
        );
        conjuncts.push(mk_or(tm, &[active_branch, inactive_branch]));
    }
    Ok(mk_and(tm, &conjuncts))
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_system_action(
    tm: &Cvc5Tm,
    action: &IRAction,
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    local_bindings: &PooledLocalBindings,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    call_stack: &[String],
) -> Result<PooledActionResult, String> {
    let mut merged_vars = vars.clone();
    merged_vars.extend(
        local_bindings
            .iter()
            .map(|(name, binding)| (name.clone(), binding.term.clone())),
    );
    match action {
        IRAction::Create {
            entity: create_entity,
            fields,
        } => {
            let create_target = entities_by_name
                .get(create_entity)
                .ok_or_else(|| format!("unknown pooled entity `{create_entity}`"))?;
            let n_slots = *slots_per_entity
                .get(create_entity)
                .ok_or_else(|| format!("missing slot scope for `{create_entity}`"))?;
            let mut conjuncts_local = vec![encode_pooled_create_action(
                tm,
                create_entity,
                fields,
                system,
                create_target,
                vars,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                n_slots,
            )?];
            conjuncts_local.extend(frame_other_pooled_entities(
                tm,
                entities_by_name,
                slots_per_entity,
                create_entity,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            )?);
            Ok(PooledActionResult {
                formula: mk_and(tm, &conjuncts_local),
                locals: local_bindings.clone(),
            })
        }
        IRAction::Choose {
            var,
            entity: choose_entity,
            filter,
            ops,
        } => {
            let choose_target = entities_by_name
                .get(choose_entity)
                .ok_or_else(|| format!("unknown pooled entity `{choose_entity}`"))?;
            let n_slots = *slots_per_entity
                .get(choose_entity)
                .ok_or_else(|| format!("missing slot scope for `{choose_entity}`"))?;
            let mut conjuncts_local = vec![encode_pooled_choose_action(
                tm,
                var,
                choose_entity,
                filter,
                ops,
                system,
                systems_by_name,
                choose_target,
                entities_by_name,
                slots_per_entity,
                &merged_vars,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                n_slots,
                call_stack,
            )?];
            conjuncts_local.extend(frame_other_pooled_entities(
                tm,
                entities_by_name,
                slots_per_entity,
                choose_entity,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            )?);
            Ok(PooledActionResult {
                formula: mk_and(tm, &conjuncts_local),
                locals: local_bindings.clone(),
            })
        }
        IRAction::ForAll {
            var,
            entity: forall_entity,
            ops,
        } => {
            let forall_target = entities_by_name
                .get(forall_entity)
                .ok_or_else(|| format!("unknown pooled entity `{forall_entity}`"))?;
            let n_slots = *slots_per_entity
                .get(forall_entity)
                .ok_or_else(|| format!("missing slot scope for `{forall_entity}`"))?;
            let mut conjuncts_local = vec![encode_pooled_forall_action(
                tm,
                var,
                forall_entity,
                ops,
                system,
                systems_by_name,
                forall_target,
                entities_by_name,
                slots_per_entity,
                &merged_vars,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                n_slots,
                call_stack,
            )?];
            conjuncts_local.extend(frame_other_pooled_entities(
                tm,
                entities_by_name,
                slots_per_entity,
                forall_entity,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
            )?);
            Ok(PooledActionResult {
                formula: mk_and(tm, &conjuncts_local),
                locals: local_bindings.clone(),
            })
        }
        IRAction::CrossCall {
            system: target_system_name,
            command,
            args,
        } => encode_pooled_crosscall_capture(
            tm,
            target_system_name,
            command,
            args,
            systems_by_name,
            entities_by_name,
            slots_per_entity,
            &merged_vars,
            next_vars,
            active_curr,
            active_next,
            slot_curr,
            slot_next,
            enum_catalog,
            call_stack,
        )
        .map(|capture| PooledActionResult {
            formula: capture.formula,
            locals: local_bindings.clone(),
        }),
        IRAction::LetCrossCall {
            name,
            system: target_system_name,
            command,
            args,
        } => {
            let capture = encode_pooled_crosscall_capture(
                tm,
                target_system_name,
                command,
                args,
                systems_by_name,
                entities_by_name,
                slots_per_entity,
                &merged_vars,
                next_vars,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                call_stack,
            )?;
            let ret = capture.return_value.ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled LetCrossCall requires `{target_system_name}::{command}` to return a value"
                )
            })?;
            let mut locals = local_bindings.clone();
            locals.insert(
                name.clone(),
                PooledLocalBinding {
                    term: ret,
                    ty: capture.return_type,
                },
            );
            Ok(PooledActionResult {
                formula: capture.formula,
                locals,
            })
        }
        IRAction::Match { scrutinee, arms } => encode_pooled_action_match(
            tm,
            scrutinee,
            arms,
            system,
            systems_by_name,
            entities_by_name,
            slots_per_entity,
            &merged_vars,
            next_vars,
            local_bindings,
            active_curr,
            active_next,
            slot_curr,
            slot_next,
            enum_catalog,
            call_stack,
        )
        .map(|formula| PooledActionResult {
            formula,
            locals: local_bindings.clone(),
        }),
        other => Err(format!(
            "cvc5 SyGuS pooled system safety does not support action `{other:?}` yet"
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_system_step(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    call_stack: &[String],
) -> Result<Cvc5Term, String> {
    let param_envs = enumerate_param_envs(tm, &step.params, enum_catalog)?;
    encode_pooled_system_step_with_param_envs(
        tm,
        step,
        system,
        systems_by_name,
        entities_by_name,
        slots_per_entity,
        curr_vars,
        next_vars,
        active_curr,
        active_next,
        slot_curr,
        slot_next,
        enum_catalog,
        param_envs,
        call_stack,
    )
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_system_step_with_bound_params(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    param_env: HashMap<String, Cvc5Term>,
    call_stack: &[String],
) -> Result<Cvc5Term, String> {
    encode_pooled_system_step_with_param_envs(
        tm,
        step,
        system,
        systems_by_name,
        entities_by_name,
        slots_per_entity,
        curr_vars,
        next_vars,
        active_curr,
        active_next,
        slot_curr,
        slot_next,
        enum_catalog,
        vec![param_env],
        call_stack,
    )
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_system_step_with_param_envs(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    param_envs: Vec<HashMap<String, Cvc5Term>>,
    call_stack: &[String],
) -> Result<Cvc5Term, String> {
    let mut branches = Vec::new();
    for param_env in param_envs {
        let mut vars = curr_vars.clone();
        vars.extend(param_env);
        let store_param_types = system_store_param_types(system);
        let pool_ctx = PooledSyGuSCtx {
            slots_per_entity,
            active_vars: active_curr,
            slot_fields: slot_curr,
            store_param_types: &store_param_types,
        };
        let mut conjuncts = vec![encode_pooled_expr(
            tm,
            &step.guard,
            &vars,
            &HashMap::new(),
            &pool_ctx,
            enum_catalog,
        )?];
        conjuncts.extend(frame_all_system_fields(
            tm,
            systems_by_name,
            curr_vars,
            next_vars,
        )?);
        let body_term = if step.body.is_empty() {
            mk_and(
                tm,
                &frame_all_pooled_entities(
                    tm,
                    entities_by_name,
                    slots_per_entity,
                    active_curr,
                    active_next,
                    slot_curr,
                    slot_next,
                )?,
            )
        } else if step.body.len() == 1 {
            encode_pooled_system_action(
                tm,
                &step.body[0],
                system,
                systems_by_name,
                entities_by_name,
                slots_per_entity,
                &vars,
                next_vars,
                &HashMap::new(),
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                call_stack,
            )?
            .formula
        } else {
            let mut intermediate_active = Vec::new();
            let mut intermediate_slots = Vec::new();
            let mut bound = Vec::new();
            for stage in 0..(step.body.len() - 1) {
                let mut active_map = HashMap::new();
                let mut slot_map = HashMap::new();
                for (entity_name, n_slots) in slots_per_entity {
                    let entity = entities_by_name
                        .get(entity_name)
                        .ok_or_else(|| format!("missing pooled entity `{entity_name}`"))?;
                    let mut per_slot = HashMap::new();
                    for slot in 0..*n_slots {
                        let active_name = format!(
                            "__abide_sygus_{}_slot{}_active_inter{}",
                            entity_name, slot, stage
                        );
                        let active_term = tm.mk_var(tm.boolean_sort(), &active_name);
                        bound.push(active_term.clone());
                        per_slot.insert(slot, active_term);
                        for field in &entity.fields {
                            let sort = sort_for_field(tm, field)?;
                            let name = format!(
                                "__abide_sygus_{}_slot{}_{}_inter{}",
                                entity_name, slot, field.name, stage
                            );
                            let term = tm.mk_var(sort, &name);
                            bound.push(term.clone());
                            slot_map
                                .insert(pool_slot_field_key(entity_name, slot, &field.name), term);
                        }
                    }
                    active_map.insert(entity_name.clone(), per_slot);
                }
                intermediate_active.push(active_map);
                intermediate_slots.push(slot_map);
            }
            let mut action_terms = Vec::new();
            let mut locals = HashMap::new();
            for (idx, action) in step.body.iter().enumerate() {
                let stage_active_curr = if idx == 0 {
                    active_curr
                } else {
                    &intermediate_active[idx - 1]
                };
                let stage_slot_curr = if idx == 0 {
                    slot_curr
                } else {
                    &intermediate_slots[idx - 1]
                };
                let stage_active_next = if idx + 1 == step.body.len() {
                    active_next
                } else {
                    &intermediate_active[idx]
                };
                let stage_slot_next = if idx + 1 == step.body.len() {
                    slot_next
                } else {
                    &intermediate_slots[idx]
                };
                let action_result = encode_pooled_system_action(
                    tm,
                    action,
                    system,
                    systems_by_name,
                    entities_by_name,
                    slots_per_entity,
                    &vars,
                    next_vars,
                    &locals,
                    stage_active_curr,
                    stage_active_next,
                    stage_slot_curr,
                    stage_slot_next,
                    enum_catalog,
                    call_stack,
                )?;
                action_terms.push(action_result.formula);
                locals = action_result.locals;
            }
            mk_exists(tm, &bound, mk_and(tm, &action_terms))
        };
        conjuncts.push(body_term);
        branches.push(mk_and(tm, &conjuncts));
    }
    Ok(mk_or(tm, &branches))
}

fn encode_pooled_match_expr(
    tm: &Cvc5Tm,
    scrutinee: &IRExpr,
    arms: &[crate::ir::types::IRMatchArm],
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    pool_ctx: &PooledSyGuSCtx<'_>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    if arms.is_empty() {
        return Err("cvc5 SyGuS match requires at least one arm".to_owned());
    }
    let scrut_term =
        encode_pooled_expr(tm, scrutinee, vars, entity_bindings, pool_ctx, enum_catalog)?;
    let scrut_ty = sygus_expr_type(scrutinee);
    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_vars = vars.clone();
        bind_pattern_vars(&arm.pattern, &scrut_term, &mut arm_vars)?;
        let pat_cond = encode_pattern_cond(tm, &arm.pattern, &scrut_term, scrut_ty, enum_catalog)?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_pooled_expr(
                tm,
                guard,
                &arm_vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_body = encode_pooled_expr(
            tm,
            &arm.body,
            &arm_vars,
            entity_bindings,
            pool_ctx,
            enum_catalog,
        )?;
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

fn infer_pooled_store_quant_entity(
    var: &str,
    body: &IRExpr,
    store_param_types: &HashMap<String, String>,
) -> Option<String> {
    match body {
        IRExpr::Index { map, key, .. } => match (map.as_ref(), key.as_ref()) {
            (
                IRExpr::Var {
                    name: store_name, ..
                },
                IRExpr::Var { name: key_name, .. },
            ) if key_name == var => store_param_types.get(store_name).cloned(),
            _ => None,
        },
        IRExpr::BinOp { left, right, .. } => {
            infer_pooled_store_quant_entity(var, left, store_param_types)
                .or_else(|| infer_pooled_store_quant_entity(var, right, store_param_types))
        }
        IRExpr::UnOp { operand, .. } => {
            infer_pooled_store_quant_entity(var, operand, store_param_types)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => infer_pooled_store_quant_entity(var, cond, store_param_types)
            .or_else(|| infer_pooled_store_quant_entity(var, then_body, store_param_types))
            .or_else(|| {
                else_body
                    .as_deref()
                    .and_then(|expr| infer_pooled_store_quant_entity(var, expr, store_param_types))
            }),
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            infer_pooled_store_quant_entity(var, expr, store_param_types)
        }
        _ => None,
    }
}

fn encode_pooled_expr(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    pool_ctx: &PooledSyGuSCtx<'_>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            LitVal::Int { value } => Ok(tm.mk_integer(*value)),
            LitVal::Bool { value } => Ok(tm.mk_boolean(*value)),
            LitVal::Real { .. } | LitVal::Float { .. } | LitVal::Str { .. } => Err(
                "cvc5 SyGuS pooled system safety only supports integer and boolean literals today"
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
                    "cvc5 SyGuS pooled system safety does not support payload constructors yet (`{enum_name}::{ctor}`)"
                ));
            }
            let idx = enum_catalog
                .get(enum_name)
                .and_then(|mapping| mapping.get(ctor))
                .ok_or_else(|| {
                    format!(
                        "unsupported enum constructor `{enum_name}::{ctor}` in pooled SyGuS slice"
                    )
                })?;
            Ok(tm.mk_integer(*idx))
        }
        IRExpr::Var { name, .. } => vars.get(name).cloned().ok_or_else(|| {
            if entity_bindings.contains_key(name) {
                format!("bare entity variable `{name}` is not supported in pooled SyGuS slice")
            } else {
                format!("unsupported free variable `{name}` in pooled SyGuS slice")
            }
        }),
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            let IRExpr::Var { name, .. } = recv.as_ref() else {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports field access on bound entity vars"
                        .to_owned(),
                );
            };
            let slot = entity_bindings
                .get(name)
                .ok_or_else(|| format!("unknown entity binding `{name}` in pooled SyGuS slice"))?;
            let (entity_name, slot) = slot;
            pool_ctx
                .slot_fields
                .get(&pool_slot_field_key(entity_name, *slot, field))
                .cloned()
                .ok_or_else(|| {
                    format!("unknown pooled field `{field}` on {entity_name} slot {slot}")
                })
        }
        IRExpr::Index { map, key, .. } => {
            if let IRExpr::Var {
                name: store_name, ..
            } = map.as_ref()
            {
                if let Some(entity_name) = pool_ctx.store_param_types.get(store_name.as_str()) {
                    let key_term =
                        encode_pooled_expr(tm, key, vars, entity_bindings, pool_ctx, enum_catalog)?;
                    let n_slots = *pool_ctx
                        .slots_per_entity
                        .get(entity_name)
                        .ok_or_else(|| format!("unknown pooled store entity `{entity_name}`"))?;
                    let mut disjuncts = Vec::new();
                    for slot in 0..n_slots {
                        let active = pool_ctx
                            .active_vars
                            .get(entity_name)
                            .and_then(|slots| slots.get(&slot))
                            .ok_or_else(|| {
                                format!("missing active variable for {entity_name} slot {slot}")
                            })?
                            .clone();
                        let slot_eq = tm.mk_term(
                            Cvc5Kind::CVC5_KIND_EQUAL,
                            &[key_term.clone(), tm.mk_integer(slot as i64)],
                        );
                        disjuncts.push(mk_and(tm, &[slot_eq, active]));
                    }
                    return Ok(mk_or(tm, &disjuncts));
                }
            }
            Err("cvc5 SyGuS pooled system safety only supports index on store params".to_owned())
        }
        IRExpr::UnOp { op, operand, .. } => {
            let inner =
                encode_pooled_expr(tm, operand, vars, entity_bindings, pool_ctx, enum_catalog)?;
            match op.as_str() {
                "OpNot" | "not" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[inner])),
                "OpNeg" | "-" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NEG, &[inner])),
                _ => Err(format!(
                    "unsupported unary op `{op}` in pooled cvc5 SyGuS slice"
                )),
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let lhs = encode_pooled_expr(tm, left, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let rhs = encode_pooled_expr(tm, right, vars, entity_bindings, pool_ctx, enum_catalog)?;
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
                _ => Err(format!(
                    "unsupported binary op `{op}` in pooled cvc5 SyGuS slice"
                )),
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut local = vars.clone();
            for binding in bindings {
                let value = encode_pooled_expr(
                    tm,
                    &binding.expr,
                    &local,
                    entity_bindings,
                    pool_ctx,
                    enum_catalog,
                )?;
                local.insert(binding.name.clone(), value);
            }
            encode_pooled_expr(tm, body, &local, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            encode_pooled_expr(tm, expr, vars, entity_bindings, pool_ctx, enum_catalog)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond = encode_pooled_expr(tm, cond, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let then_term =
                encode_pooled_expr(tm, then_body, vars, entity_bindings, pool_ctx, enum_catalog)?;
            let else_term = encode_pooled_expr(
                tm,
                else_body.as_deref().ok_or_else(|| {
                    "cvc5 SyGuS pooled slice requires an explicit else branch".to_owned()
                })?,
                vars,
                entity_bindings,
                pool_ctx,
                enum_catalog,
            )?;
            Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[cond, then_term, else_term]))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => encode_pooled_match_expr(
            tm,
            scrutinee,
            arms,
            vars,
            entity_bindings,
            pool_ctx,
            enum_catalog,
        ),
        IRExpr::Forall {
            var, domain, body, ..
        }
        | IRExpr::Exists {
            var, domain, body, ..
        }
        | IRExpr::One {
            var, domain, body, ..
        }
        | IRExpr::Lone {
            var, domain, body, ..
        } => {
            let kind = match expr {
                IRExpr::Forall { .. } => "forall",
                IRExpr::Exists { .. } => "exists",
                IRExpr::One { .. } => "one",
                IRExpr::Lone { .. } => "lone",
                _ => unreachable!(),
            };
            if let IRType::Entity { name } = domain {
                let n_slots = *pool_ctx
                    .slots_per_entity
                    .get(name)
                    .ok_or_else(|| format!("unknown pooled entity domain `{name}`"))?;
                let mut bodies = Vec::new();
                for slot in 0..n_slots {
                    let active = pool_ctx
                        .active_vars
                        .get(name)
                        .and_then(|slots| slots.get(&slot))
                        .ok_or_else(|| format!("missing active variable for {name} slot {slot}"))?
                        .clone();
                    let mut inner_bindings = entity_bindings.clone();
                    inner_bindings.insert(var.clone(), (name.clone(), slot));
                    let body_term = encode_pooled_expr(
                        tm,
                        body,
                        vars,
                        &inner_bindings,
                        pool_ctx,
                        enum_catalog,
                    )?;
                    bodies.push(match kind {
                        "forall" => tm.mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[active, body_term]),
                        "exists" | "one" | "lone" => mk_and(tm, &[active, body_term]),
                        _ => unreachable!(),
                    });
                }
                return match kind {
                    "forall" => Ok(mk_and(tm, &bodies)),
                    "exists" => Ok(mk_or(tm, &bodies)),
                    "one" => {
                        if bodies.is_empty() {
                            Ok(tm.mk_boolean(false))
                        } else {
                            let mut disjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                let mut conjuncts = vec![bodies[i].clone()];
                                for (j, body_j) in bodies.iter().enumerate() {
                                    if i != j {
                                        conjuncts.push(
                                            tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[body_j.clone()]),
                                        );
                                    }
                                }
                                disjuncts.push(mk_and(tm, &conjuncts));
                            }
                            Ok(mk_or(tm, &disjuncts))
                        }
                    }
                    "lone" => {
                        if bodies.len() <= 1 {
                            Ok(tm.mk_boolean(true))
                        } else {
                            let mut conjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                for j in (i + 1)..bodies.len() {
                                    conjuncts.push(tm.mk_term(
                                        Cvc5Kind::CVC5_KIND_NOT,
                                        &[mk_and(tm, &[bodies[i].clone(), bodies[j].clone()])],
                                    ));
                                }
                            }
                            Ok(mk_and(tm, &conjuncts))
                        }
                    }
                    _ => unreachable!(),
                };
            }

            if *domain == IRType::Int {
                let Some(entity_name) =
                    infer_pooled_store_quant_entity(var, body, pool_ctx.store_param_types)
                else {
                    return Err(
                        "cvc5 SyGuS pooled system safety only supports Int quantifiers when they range over store param slots"
                            .to_owned(),
                    );
                };
                let n_slots = *pool_ctx
                    .slots_per_entity
                    .get(&entity_name)
                    .ok_or_else(|| format!("unknown pooled store entity `{entity_name}`"))?;
                let mut bodies = Vec::new();
                for slot in 0..n_slots {
                    let mut scoped = vars.clone();
                    scoped.insert(var.clone(), tm.mk_integer(slot as i64));
                    let mut inner_bindings = entity_bindings.clone();
                    inner_bindings.insert(var.clone(), (entity_name.clone(), slot));
                    bodies.push(encode_pooled_expr(
                        tm,
                        body,
                        &scoped,
                        &inner_bindings,
                        pool_ctx,
                        enum_catalog,
                    )?);
                }
                return match kind {
                    "forall" => Ok(mk_and(tm, &bodies)),
                    "exists" => Ok(mk_or(tm, &bodies)),
                    "one" => {
                        if bodies.is_empty() {
                            Ok(tm.mk_boolean(false))
                        } else {
                            let mut disjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                let mut conjuncts = vec![bodies[i].clone()];
                                for (j, body_j) in bodies.iter().enumerate() {
                                    if i != j {
                                        conjuncts.push(
                                            tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[body_j.clone()]),
                                        );
                                    }
                                }
                                disjuncts.push(mk_and(tm, &conjuncts));
                            }
                            Ok(mk_or(tm, &disjuncts))
                        }
                    }
                    "lone" => {
                        if bodies.len() <= 1 {
                            Ok(tm.mk_boolean(true))
                        } else {
                            let mut conjuncts = Vec::new();
                            for i in 0..bodies.len() {
                                for j in (i + 1)..bodies.len() {
                                    conjuncts.push(tm.mk_term(
                                        Cvc5Kind::CVC5_KIND_NOT,
                                        &[mk_and(tm, &[bodies[i].clone(), bodies[j].clone()])],
                                    ));
                                }
                            }
                            Ok(mk_and(tm, &conjuncts))
                        }
                    }
                    _ => unreachable!(),
                };
            }

            let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
                return Err(
                    "cvc5 SyGuS pooled system safety only supports Bool and fieldless-enum domains for finite quantifiers"
                        .to_owned(),
                );
            };
            let mut bodies = Vec::new();
            for candidate in candidates {
                let mut scoped = vars.clone();
                scoped.insert(var.clone(), candidate);
                bodies.push(encode_pooled_expr(
                    tm,
                    body,
                    &scoped,
                    entity_bindings,
                    pool_ctx,
                    enum_catalog,
                )?);
            }
            match kind {
                "forall" => Ok(mk_and(tm, &bodies)),
                "exists" => Ok(mk_or(tm, &bodies)),
                "one" => {
                    if bodies.is_empty() {
                        Ok(tm.mk_boolean(false))
                    } else {
                        let mut disjuncts = Vec::new();
                        for i in 0..bodies.len() {
                            let mut conjuncts = vec![bodies[i].clone()];
                            for (j, body_j) in bodies.iter().enumerate() {
                                if i != j {
                                    conjuncts.push(
                                        tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[body_j.clone()]),
                                    );
                                }
                            }
                            disjuncts.push(mk_and(tm, &conjuncts));
                        }
                        Ok(mk_or(tm, &disjuncts))
                    }
                }
                "lone" => {
                    if bodies.len() <= 1 {
                        Ok(tm.mk_boolean(true))
                    } else {
                        let mut conjuncts = Vec::new();
                        for i in 0..bodies.len() {
                            for j in (i + 1)..bodies.len() {
                                conjuncts.push(tm.mk_term(
                                    Cvc5Kind::CVC5_KIND_NOT,
                                    &[mk_and(tm, &[bodies[i].clone(), bodies[j].clone()])],
                                ));
                            }
                        }
                        Ok(mk_and(tm, &conjuncts))
                    }
                }
                _ => unreachable!(),
            }
        }
        _ => Err(format!(
            "unsupported expression kind in cvc5 SyGuS pooled system safety slice: {expr:?}"
        )),
    }
}

fn bind_explicit_params(
    tm: &Cvc5Tm,
    params: &[IRTransParam],
    args: &[IRExpr],
    vars: &HashMap<String, Cvc5Term>,
    entity_bindings: &PooledEntityBindings,
    pool_ctx: &PooledSyGuSCtx<'_>,
    enum_catalog: &EnumCatalog,
    context: &str,
) -> Result<HashMap<String, Cvc5Term>, String> {
    if params.len() != args.len() {
        return Err(format!(
            "cvc5 SyGuS pooled cross-call safety expected {} args for `{context}`, got {}",
            params.len(),
            args.len()
        ));
    }
    let mut bound = HashMap::new();
    let mut scoped = vars.clone();
    for (param, arg) in params.iter().zip(args.iter()) {
        let arg_term =
            encode_pooled_expr(tm, arg, &scoped, entity_bindings, pool_ctx, enum_catalog)?;
        scoped.insert(param.name.clone(), arg_term.clone());
        bound.insert(param.name.clone(), arg_term);
    }
    Ok(bound)
}

fn extend_call_stack(call_stack: &[String], target_system_name: &str) -> Vec<String> {
    let mut next = call_stack.to_vec();
    next.push(target_system_name.to_owned());
    next
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_crosscall_capture(
    tm: &Cvc5Tm,
    target_system_name: &str,
    command: &str,
    args: &[IRExpr],
    systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    call_stack: &[String],
) -> Result<PooledCrossCallCapture, String> {
    if call_stack.iter().any(|name| name == target_system_name) {
        return Err(format!(
            "cvc5 SyGuS pooled cross-call safety does not support recursive cross-call cycles (`{}::{}`)",
            target_system_name, command
        ));
    }
    let target_system = systems_by_name.get(target_system_name).ok_or_else(|| {
        format!(
            "cvc5 SyGuS pooled cross-call safety could not find target system `{target_system_name}`"
        )
    })?;
    let target_step = target_system
        .actions
        .iter()
        .find(|step| step.name == *command)
        .ok_or_else(|| {
            format!(
                "cvc5 SyGuS pooled cross-call safety could not find target command `{target_system_name}::{command}`"
            )
        })?;
    let bound_params = bind_explicit_params(
        tm,
        &target_step.params,
        args,
        curr_vars,
        &HashMap::new(),
        &PooledSyGuSCtx {
            slots_per_entity,
            active_vars: active_curr,
            slot_fields: slot_curr,
            store_param_types: &system_store_param_types(target_system),
        },
        enum_catalog,
        &format!("{target_system_name}::{command}"),
    )?;
    let formula = encode_pooled_system_step_with_bound_params(
        tm,
        target_step,
        target_system,
        systems_by_name,
        entities_by_name,
        slots_per_entity,
        curr_vars,
        next_vars,
        active_curr,
        active_next,
        slot_curr,
        slot_next,
        enum_catalog,
        bound_params.clone(),
        &extend_call_stack(call_stack, target_system_name),
    )?;
    let return_value = if let Some(ret) = &target_step.return_expr {
        let mut ret_vars = curr_vars.clone();
        ret_vars.extend(bound_params);
        let next_ctx = PooledSyGuSCtx {
            slots_per_entity,
            active_vars: active_next,
            slot_fields: slot_next,
            store_param_types: &system_store_param_types(target_system),
        };
        Some(encode_pooled_expr(
            tm,
            ret,
            &ret_vars,
            &HashMap::new(),
            &next_ctx,
            enum_catalog,
        )?)
    } else {
        None
    };
    Ok(PooledCrossCallCapture {
        formula,
        return_value,
        return_type: target_step
            .return_expr
            .as_ref()
            .and_then(sygus_match_scrutinee_type),
    })
}

#[allow(clippy::too_many_arguments)]
fn encode_pooled_action_match(
    tm: &Cvc5Tm,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    arms: &[crate::ir::types::IRActionMatchArm],
    system: &IRSystem,
    systems_by_name: &HashMap<String, &IRSystem>,
    entities_by_name: &HashMap<String, &IREntity>,
    slots_per_entity: &HashMap<String, usize>,
    vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    local_bindings: &PooledLocalBindings,
    active_curr: &HashMap<String, HashMap<usize, Cvc5Term>>,
    active_next: &HashMap<String, HashMap<usize, Cvc5Term>>,
    slot_curr: &HashMap<String, Cvc5Term>,
    slot_next: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    call_stack: &[String],
) -> Result<Cvc5Term, String> {
    if arms.is_empty() {
        return Err("cvc5 SyGuS pooled action match requires at least one arm".to_owned());
    }
    let (prefix_formula, scrut_term, scrut_ty) = match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => {
            let binding = local_bindings.get(name).ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled action match only supports var scrutinees from local cross-call results today (`{name}`)"
                )
            })?;
            (
                tm.mk_boolean(true),
                binding.term.clone(),
                binding.ty.clone(),
            )
        }
        crate::ir::types::IRActionMatchScrutinee::CrossCall {
            system: target_system_name,
            command,
            args,
        } => {
            let capture = encode_pooled_crosscall_capture(
                tm,
                target_system_name,
                command,
                args,
                systems_by_name,
                entities_by_name,
                slots_per_entity,
                vars,
                next_vars,
                active_curr,
                active_next,
                slot_curr,
                slot_next,
                enum_catalog,
                call_stack,
            )?;
            let scrut_term = capture.return_value.ok_or_else(|| {
                format!(
                    "cvc5 SyGuS pooled action match requires `{target_system_name}::{command}` to return a value"
                )
            })?;
            (capture.formula, scrut_term, capture.return_type)
        }
    };

    let guard_store_param_types = system_store_param_types(system);
    let guard_ctx = PooledSyGuSCtx {
        slots_per_entity,
        active_vars: active_curr,
        slot_fields: slot_curr,
        store_param_types: &guard_store_param_types,
    };
    let mut fallback = None;
    for arm in arms.iter().rev() {
        if arm.body.len() != 1 {
            return Err(
                "cvc5 SyGuS pooled action match only supports single-action arms today".to_owned(),
            );
        }
        let mut arm_vars = vars.clone();
        bind_pattern_vars(&arm.pattern, &scrut_term, &mut arm_vars)?;
        let pat_cond = encode_pattern_cond(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            enum_catalog,
        )?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_pooled_expr(
                tm,
                guard,
                &arm_vars,
                &HashMap::new(),
                &guard_ctx,
                enum_catalog,
            )?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_body = encode_pooled_system_action(
            tm,
            &arm.body[0],
            system,
            systems_by_name,
            entities_by_name,
            slots_per_entity,
            &arm_vars,
            next_vars,
            &HashMap::new(),
            active_curr,
            active_next,
            slot_curr,
            slot_next,
            enum_catalog,
            call_stack,
        )?
        .formula;
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
                        "cvc5 SyGuS pooled action match requires a final wildcard or var fallback arm"
                            .to_owned(),
                    );
                }
            }
            Some(else_term) => {
                tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[arm_cond, arm_body, else_term])
            }
        });
    }

    Ok(mk_and(
        tm,
        &[
            prefix_formula,
            fallback.ok_or_else(|| {
                "cvc5 SyGuS pooled action match required at least one arm".to_owned()
            })?,
        ],
    ))
}
