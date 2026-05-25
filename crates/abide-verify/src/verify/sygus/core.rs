use super::*;
use std::collections::HashSet;

#[derive(Clone, Default)]
pub(super) struct EnumCatalog {
    fieldless: HashMap<String, HashMap<String, i64>>,
    payload: HashMap<String, PayloadEnumInfo>,
}

#[derive(Clone)]
pub(super) struct PayloadEnumInfo {
    sort: Cvc5Sort,
    variants: Vec<PayloadVariantInfo>,
}

#[derive(Clone)]
pub(super) struct PayloadVariantInfo {
    name: String,
    constructor: Cvc5Term,
    tester: Cvc5Term,
    field_order: Vec<String>,
    accessors: HashMap<String, PayloadAccessorInfo>,
}

#[derive(Clone)]
pub(super) struct PayloadAccessorInfo {
    term: Cvc5Term,
    ty: IRType,
}

impl EnumCatalog {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn insert(&mut self, enum_name: String, mapping: HashMap<String, i64>) {
        self.fieldless.insert(enum_name, mapping);
    }

    pub(super) fn get(&self, enum_name: &str) -> Option<&HashMap<String, i64>> {
        self.fieldless.get(enum_name)
    }

    pub(super) fn payload_sort(&self, enum_name: &str) -> Option<&Cvc5Sort> {
        self.payload.get(enum_name).map(|info| &info.sort)
    }

    pub(super) fn has_payload_enums(&self) -> bool {
        !self.payload.is_empty()
    }

    pub(super) fn payload_variant(
        &self,
        enum_name: &str,
        ctor: &str,
    ) -> Option<&PayloadVariantInfo> {
        self.payload
            .get(enum_name)?
            .variants
            .iter()
            .find(|variant| {
                ctor_name_matches(ctor, enum_name, &variant.name)
                    || ctor_name_matches(&variant.name, enum_name, ctor)
            })
    }

    pub(super) fn payload_accessor_for_field(
        &self,
        enum_name: &str,
        field: &str,
    ) -> Result<Option<&PayloadAccessorInfo>, String> {
        let Some(info) = self.payload.get(enum_name) else {
            return Ok(None);
        };
        let mut found = info
            .variants
            .iter()
            .filter_map(|variant| variant.accessors.get(field));
        let first = found.next();
        if found.next().is_some() {
            return Err(format!(
                "cvc5 SyGuS payload field projection `{enum_name}.{field}` is ambiguous across constructors"
            ));
        }
        Ok(first)
    }

    #[cfg(test)]
    pub(super) fn from_types(tm: &Cvc5Tm, types: &[IRType]) -> Result<Self, String> {
        let mut catalog = Self::new();
        for ty in types {
            catalog.register_type(tm, ty)?;
        }
        Ok(catalog)
    }

    pub(super) fn register_type(&mut self, tm: &Cvc5Tm, ty: &IRType) -> Result<(), String> {
        let IRType::Enum { name, variants } = ty else {
            return Ok(());
        };
        if variants.iter().any(|variant| !variant.fields.is_empty()) {
            self.register_payload_enum(tm, name, variants)
        } else {
            self.register_fieldless_enum(name, variants);
            Ok(())
        }
    }

    fn register_fieldless_enum(&mut self, name: &str, variants: &[crate::ir::types::IRVariant]) {
        self.fieldless.entry(name.to_owned()).or_insert_with(|| {
            variants
                .iter()
                .enumerate()
                .map(|(idx, variant)| (variant.name.clone(), idx as i64))
                .collect()
        });
    }

    fn register_payload_enum(
        &mut self,
        tm: &Cvc5Tm,
        name: &str,
        variants: &[crate::ir::types::IRVariant],
    ) -> Result<(), String> {
        if self.payload.contains_key(name) {
            return Ok(());
        }

        let mut decl = tm.mk_dt_decl(name, false);
        for variant in variants {
            let mut ctor = tm.mk_dt_cons_decl(&variant.name);
            for field in &variant.fields {
                ctor.add_selector(&field.name, self.sort_for_payload_field(tm, &field.ty)?);
            }
            decl.add_constructor(&ctor);
        }
        let sort = tm.mk_dt_sort(&decl);
        let datatype = sort.datatype();
        let mut payload_variants = Vec::with_capacity(variants.len());
        for (idx, variant) in variants.iter().enumerate() {
            let cvc5_ctor = datatype.constructor(idx);
            let mut accessors = HashMap::new();
            for field in &variant.fields {
                let selector = cvc5_ctor.selector_by_name(&field.name);
                accessors.insert(
                    field.name.clone(),
                    PayloadAccessorInfo {
                        term: selector.term(),
                        ty: field.ty.clone(),
                    },
                );
            }
            payload_variants.push(PayloadVariantInfo {
                name: variant.name.clone(),
                constructor: cvc5_ctor.term(),
                tester: cvc5_ctor.tester_term(),
                field_order: variant
                    .fields
                    .iter()
                    .map(|field| field.name.clone())
                    .collect(),
                accessors,
            });
        }
        self.payload.insert(
            name.to_owned(),
            PayloadEnumInfo {
                sort,
                variants: payload_variants,
            },
        );
        Ok(())
    }

    fn sort_for_payload_field(&self, tm: &Cvc5Tm, ty: &IRType) -> Result<Cvc5Sort, String> {
        match ty {
            IRType::Int => Ok(tm.integer_sort()),
            IRType::Real => Ok(tm.real_sort()),
            IRType::Bool => Ok(tm.boolean_sort()),
            IRType::Enum { name, variants }
                if variants.iter().all(|variant| variant.fields.is_empty()) =>
            {
                Ok(tm.integer_sort())
            }
            IRType::Enum { name, .. } => self.payload_sort(name).cloned().ok_or_else(|| {
                format!(
                    "cvc5 SyGuS payload datatype fields cannot reference undeclared payload enum `{name}`"
                )
            }),
            _ => Err(format!(
                "cvc5 SyGuS payload datatype fields only support Int, Bool, and enum fields today (`{ty:?}`)"
            )),
        }
    }
}

fn type_uses_real(ty: &IRType) -> bool {
    match ty {
        IRType::Real => true,
        IRType::Enum { variants, .. } => variants
            .iter()
            .flat_map(|variant| &variant.fields)
            .any(|field| type_uses_real(&field.ty)),
        _ => false,
    }
}

pub(super) fn requires_all_logic(
    enum_catalog: &EnumCatalog,
    fields: &[IRField],
    derived_fields: &[IRDerivedField],
) -> bool {
    enum_catalog.has_payload_enums()
        || fields.iter().any(|field| type_uses_real(&field.ty))
        || derived_fields.iter().any(|field| type_uses_real(&field.ty))
}

pub(super) fn real_lit_term(tm: &Cvc5Tm, value: f64) -> Result<Cvc5Term, String> {
    if !value.is_finite() {
        return Err("cvc5 SyGuS real literals must be finite".to_owned());
    }
    #[allow(clippy::cast_possible_truncation)]
    let scaled = (value * 1_000_000.0) as i64;
    Ok(tm.mk_real_from_rational(scaled, 1_000_000))
}

pub(super) fn lookup_enum_ctor_index<'a>(
    enum_catalog: &'a EnumCatalog,
    enum_name: &str,
    ctor: &str,
) -> Option<&'a i64> {
    enum_catalog.get(enum_name).and_then(|mapping| {
        mapping.get(ctor).or_else(|| {
            ctor.split_once("::")
                .and_then(|(_, bare)| mapping.get(bare))
        })
    })
}

pub(super) fn encode_enum_atom_var(
    tm: &Cvc5Tm,
    name: &str,
    ty: &IRType,
    enum_catalog: &EnumCatalog,
) -> Option<Cvc5Term> {
    let IRType::Enum {
        name: enum_name, ..
    } = ty
    else {
        return None;
    };
    lookup_enum_ctor_index(enum_catalog, enum_name, name).map(|idx| tm.mk_integer(*idx))
}

pub(super) fn system_store_param_types(system: &IRSystem) -> HashMap<String, String> {
    system
        .store_params
        .iter()
        .map(|p| (p.name.clone(), p.entity_type.clone()))
        .collect()
}

pub(super) fn collect_unique_system_fields(
    systems: &[IRSystem],
) -> Result<Vec<(&str, &IRField)>, String> {
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

#[cfg(test)]
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
    let start = Instant::now();
    let tm = Cvc5Tm::new();
    let mut solver = Cvc5Solver::new(&tm);
    solver.set_option("sygus", "true");
    solver.set_option("incremental", "false");
    if timeout_ms > 0 {
        solver.set_option("tlimit-per", &timeout_ms.to_string());
    }
    let enum_catalog =
        build_enum_catalog_with_derived(&tm, &entity.fields, &entity.derived_fields)?;
    solver.set_logic(
        if requires_all_logic(&enum_catalog, &entity.fields, &entity.derived_fields) {
            "ALL"
        } else {
            "LIA"
        },
    );

    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    let mut curr_order = Vec::with_capacity(entity.fields.len());
    let mut next_order = Vec::with_capacity(entity.fields.len());

    for field in &entity.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog)?;
        let curr = tm.mk_var(sort.clone(), &field.name);
        let next = tm.mk_var(sort, &format!("{}_next", field.name));
        curr_vars.insert(field.name.clone(), curr.clone());
        next_vars.insert(field.name.clone(), next.clone());
        curr_order.push(curr);
        next_order.push(next);
    }
    extend_with_derived_fields(&tm, &mut curr_vars, &entity.derived_fields, &enum_catalog)?;

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
                &entity.derived_fields,
                &entity.fsm_decls,
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
    if !system.let_bindings.is_empty() {
        return Err("cvc5 SyGuS system safety does not support let-bindings yet".to_owned());
    }
    let tm = Cvc5Tm::new();
    let mut solver = Cvc5Solver::new(&tm);
    solver.set_option("sygus", "true");
    solver.set_option("incremental", "false");
    if timeout_ms > 0 {
        solver.set_option("tlimit-per", &timeout_ms.to_string());
    }
    let enum_catalog =
        build_enum_catalog_with_derived(&tm, &system.fields, &system.derived_fields)?;
    solver.set_logic(
        if requires_all_logic(&enum_catalog, &system.fields, &system.derived_fields) {
            "ALL"
        } else {
            "LIA"
        },
    );

    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    let mut curr_order = Vec::with_capacity(system.fields.len());
    let mut next_order = Vec::with_capacity(system.fields.len());

    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog)?;
        let curr = tm.mk_var(sort.clone(), &field.name);
        let next = tm.mk_var(sort, &format!("{}_next", field.name));
        curr_vars.insert(field.name.clone(), curr.clone());
        next_vars.insert(field.name.clone(), next.clone());
        curr_order.push(curr);
        next_order.push(next);
    }
    extend_with_derived_fields(&tm, &mut curr_vars, &system.derived_fields, &enum_catalog)?;

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
                &system.fsm_decls,
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

pub(super) fn build_enum_catalog(tm: &Cvc5Tm, fields: &[IRField]) -> Result<EnumCatalog, String> {
    build_enum_catalog_with_derived(tm, fields, &[])
}

pub(super) fn build_enum_catalog_with_derived(
    tm: &Cvc5Tm,
    fields: &[IRField],
    derived_fields: &[IRDerivedField],
) -> Result<EnumCatalog, String> {
    let mut catalog = EnumCatalog::new();
    for field in fields {
        if let IRType::Enum { name, variants } = &field.ty {
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                catalog.register_payload_enum(tm, name, variants)?;
                continue;
            }
            let mut mapping = HashMap::new();
            for (idx, variant) in variants.iter().enumerate() {
                mapping.insert(variant.name.clone(), idx as i64);
            }
            catalog.insert(name.clone(), mapping);
        }
    }
    for derived in derived_fields {
        catalog.register_type(tm, &derived.ty)?;
    }
    Ok(catalog)
}

pub(super) fn extend_with_derived_fields(
    tm: &Cvc5Tm,
    vars: &mut HashMap<String, Cvc5Term>,
    derived_fields: &[IRDerivedField],
    enum_catalog: &EnumCatalog,
) -> Result<(), String> {
    for derived in derived_fields {
        let value = encode_expr(tm, &derived.body, vars, enum_catalog)?;
        vars.insert(derived.name.clone(), value);
    }
    Ok(())
}

pub(super) fn sort_for_field(
    tm: &Cvc5Tm,
    field: &IRField,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Sort, String> {
    match &field.ty {
        IRType::Int => Ok(tm.integer_sort()),
        IRType::Real => Ok(tm.real_sort()),
        IRType::Bool => Ok(tm.boolean_sort()),
        IRType::Enum { variants, .. }
            if variants.iter().all(|variant| variant.fields.is_empty()) =>
        {
            Ok(tm.integer_sort())
        }
        IRType::Enum { name, .. } => enum_catalog.payload_sort(name).cloned().ok_or_else(|| {
            format!(
                "cvc5 SyGuS safety could not build payload enum sort for field `{}`",
                field.name
            )
        }),
        _ => Err(format!(
            "cvc5 SyGuS safety only supports Int/Real/Bool/enum fields today (field `{}`)",
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
    let current = curr_vars
        .get(&field.name)
        .ok_or_else(|| format!("missing current variable for field `{}`", field.name))?;
    let mut conjuncts = Vec::new();
    if let Some(default) = &field.default {
        let encoded = encode_expr(tm, default, curr_vars, enum_catalog)?;
        conjuncts.push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[current.clone(), encoded]));
    }
    if let Some(initial_constraint) = &field.initial_constraint {
        let mut scoped = curr_vars.clone();
        scoped.insert("$".to_owned(), current.clone());
        conjuncts.push(encode_expr(tm, initial_constraint, &scoped, enum_catalog)?);
    }
    if conjuncts.is_empty() {
        return Err(format!(
            "field `{}` needs a deterministic default or initial constraint for SyGuS",
            field.name
        ));
    }
    Ok(mk_and(tm, &conjuncts))
}

pub(super) fn encode_transition(
    tm: &Cvc5Tm,
    trans: &IRTransition,
    fields: &[IRField],
    derived_fields: &[IRDerivedField],
    fsm_decls: &[IRFsm],
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
        conjuncts.extend(encode_fsm_constraints(
            tm,
            fsm_decls,
            |field| update_map.contains_key(field),
            &scoped,
            next_vars,
            enum_catalog,
        )?);
        if let Some(postcondition) = &trans.postcondition {
            let mut post_scoped = next_vars.clone();
            extend_with_derived_fields(tm, &mut post_scoped, derived_fields, enum_catalog)?;
            post_scoped.extend(
                scoped
                    .iter()
                    .filter(|(name, _)| !curr_vars.contains_key(*name))
                    .map(|(name, term)| (name.clone(), term.clone())),
            );
            conjuncts.push(encode_expr(tm, postcondition, &post_scoped, enum_catalog)?);
        }
        param_branches.push(mk_and(tm, &conjuncts));
    }

    Ok(mk_or(tm, &param_branches))
}

pub(super) fn encode_system_step(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    fields: &[IRField],
    fsm_decls: &[IRFsm],
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    let param_envs = enumerate_param_envs(tm, &step.params, enum_catalog)?;
    let mut param_branches = Vec::with_capacity(param_envs.len());
    for param_env in param_envs {
        let mut scoped = curr_vars.clone();
        scoped.extend(param_env);

        let mut conjuncts = vec![encode_expr(tm, &step.guard, &scoped, enum_catalog)?];
        let update_map = collect_system_updates(tm, step, fields, &scoped, enum_catalog)?;

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
        conjuncts.extend(encode_fsm_constraints(
            tm,
            fsm_decls,
            |field| update_map.contains_key(field),
            &scoped,
            next_vars,
            enum_catalog,
        )?);
        param_branches.push(mk_and(tm, &conjuncts));
    }

    Ok(mk_or(tm, &param_branches))
}

pub(super) fn encode_fsm_constraints(
    tm: &Cvc5Tm,
    fsm_decls: &[IRFsm],
    mut is_touched: impl FnMut(&str) -> bool,
    curr_vars: &HashMap<String, Cvc5Term>,
    next_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Vec<Cvc5Term>, String> {
    let mut constraints = Vec::new();
    for fsm in fsm_decls {
        if !is_touched(&fsm.field) {
            continue;
        }
        let curr = curr_vars
            .get(&fsm.field)
            .ok_or_else(|| format!("missing current FSM field `{}`", fsm.field))?;
        let next = next_vars
            .get(&fsm.field)
            .ok_or_else(|| format!("missing next FSM field `{}`", fsm.field))?;
        let mut allowed =
            vec![tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[curr.clone(), next.clone()])];
        for edge in &fsm.transitions {
            let from = lookup_enum_ctor_index(enum_catalog, &fsm.enum_name, &edge.from)
                .ok_or_else(|| {
                    format!(
                        "unknown FSM source `{}` for enum `{}` in cvc5 SyGuS slice",
                        edge.from, fsm.enum_name
                    )
                })?;
            let to = lookup_enum_ctor_index(enum_catalog, &fsm.enum_name, &edge.to).ok_or_else(
                || {
                    format!(
                        "unknown FSM target `{}` for enum `{}` in cvc5 SyGuS slice",
                        edge.to, fsm.enum_name
                    )
                },
            )?;
            let from_eq = tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[curr.clone(), tm.mk_integer(*from)],
            );
            let to_eq = tm.mk_term(
                Cvc5Kind::CVC5_KIND_EQUAL,
                &[next.clone(), tm.mk_integer(*to)],
            );
            allowed.push(mk_and(tm, &[from_eq, to_eq]));
        }
        constraints.push(mk_or(tm, &allowed));
    }
    Ok(constraints)
}

pub(super) fn collect_system_updates(
    tm: &Cvc5Tm,
    step: &IRSystemAction,
    fields: &[IRField],
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<HashMap<String, Cvc5Term>, String> {
    let mut updates = HashMap::new();
    let mut staged_vars = curr_vars.clone();
    for action in &step.body {
        let action_updates = collect_system_action_updates(
            tm,
            action,
            fields,
            &staged_vars,
            enum_catalog,
            &step.name,
        )?;
        for (field, value) in action_updates {
            staged_vars.insert(field.clone(), value.clone());
            updates.insert(field, value);
        }
    }
    Ok(updates)
}

fn collect_system_action_updates(
    tm: &Cvc5Tm,
    action: &crate::ir::types::IRAction,
    fields: &[IRField],
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    step_name: &str,
) -> Result<HashMap<String, Cvc5Term>, String> {
    match action {
        crate::ir::types::IRAction::ExprStmt { expr } => {
            let (name, rhs) =
                collect_system_exprstmt_update(tm, expr, curr_vars, enum_catalog, step_name)?;
            Ok(HashMap::from([(name, rhs)]))
        }
        crate::ir::types::IRAction::Match { scrutinee, arms } => {
            collect_system_match_updates(tm, scrutinee, arms, fields, curr_vars, enum_catalog)
        }
        other => Err(format!(
            "cvc5 SyGuS system safety does not support action `{other:?}` yet (`{step_name}`)"
        )),
    }
}

fn collect_system_exprstmt_update(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    step_name: &str,
) -> Result<(String, Cvc5Term), String> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = expr
    else {
        return Err(format!(
            "cvc5 SyGuS system safety expects primed equality statements (`{step_name}`)"
        ));
    };
    if op != "OpEq" && op != "==" {
        return Err(format!(
            "cvc5 SyGuS system safety expects primed equality statements (`{step_name}`)"
        ));
    }
    let IRExpr::Prime { expr: primed, .. } = left.as_ref() else {
        return Err(format!(
            "cvc5 SyGuS system safety expects a primed lhs in ExprStmt (`{step_name}`)"
        ));
    };
    let IRExpr::Var { name, .. } = primed.as_ref() else {
        return Err(format!(
            "cvc5 SyGuS system safety only supports primed system field vars on the lhs (`{step_name}`)"
        ));
    };
    Ok((
        name.clone(),
        encode_expr(tm, right, curr_vars, enum_catalog)?,
    ))
}

fn collect_system_action_sequence_updates(
    tm: &Cvc5Tm,
    actions: &[crate::ir::types::IRAction],
    fields: &[IRField],
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<HashMap<String, Cvc5Term>, String> {
    let mut updates = HashMap::new();
    let mut staged_vars = curr_vars.clone();
    for action in actions {
        let action_updates = collect_system_action_updates(
            tm,
            action,
            fields,
            &staged_vars,
            enum_catalog,
            "match arm",
        )?;
        for (field, value) in action_updates {
            staged_vars.insert(field.clone(), value.clone());
            updates.insert(field, value);
        }
    }
    Ok(updates)
}

fn merge_system_match_update_maps(
    tm: &Cvc5Tm,
    fields: &[IRField],
    cond: &Cvc5Term,
    then_updates: &HashMap<String, Cvc5Term>,
    else_updates: &HashMap<String, Cvc5Term>,
    curr_vars: &HashMap<String, Cvc5Term>,
) -> Result<HashMap<String, Cvc5Term>, String> {
    let mut touched: HashSet<String> = then_updates.keys().cloned().collect();
    touched.extend(else_updates.keys().cloned());
    let field_names: HashSet<_> = fields.iter().map(|field| field.name.as_str()).collect();
    let mut merged = HashMap::new();
    for field in touched {
        if !field_names.contains(field.as_str()) {
            return Err(format!(
                "cvc5 SyGuS system safety cannot update unknown field `{field}` in match arm"
            ));
        }
        let current = curr_vars
            .get(&field)
            .ok_or_else(|| format!("missing current variable for field `{field}`"))?;
        let then_term = then_updates
            .get(&field)
            .cloned()
            .unwrap_or_else(|| current.clone());
        let else_term = else_updates
            .get(&field)
            .cloned()
            .unwrap_or_else(|| current.clone());
        merged.insert(
            field,
            tm.mk_term(
                Cvc5Kind::CVC5_KIND_ITE,
                &[cond.clone(), then_term, else_term],
            ),
        );
    }
    Ok(merged)
}

fn collect_system_match_updates(
    tm: &Cvc5Tm,
    scrutinee: &crate::ir::types::IRActionMatchScrutinee,
    arms: &[crate::ir::types::IRActionMatchArm],
    fields: &[IRField],
    curr_vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<HashMap<String, Cvc5Term>, String> {
    if arms.is_empty() {
        return Err("cvc5 SyGuS system action match requires at least one arm".to_owned());
    }
    let (scrut_term, scrut_ty) = match scrutinee {
        crate::ir::types::IRActionMatchScrutinee::Var { name } => {
            let term = curr_vars.get(name).cloned().ok_or_else(|| {
                format!("cvc5 SyGuS system action match requires a bound scrutinee (`{name}`)")
            })?;
            let ty = fields
                .iter()
                .find(|field| field.name == *name)
                .map(|field| field.ty.clone());
            (term, ty)
        }
        crate::ir::types::IRActionMatchScrutinee::CrossCall { .. } => {
            return Err(
                "cvc5 SyGuS system action match does not support cross-call scrutinees yet"
                    .to_owned(),
            );
        }
    };

    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_vars = curr_vars.clone();
        bind_pattern_vars(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            &mut arm_vars,
            enum_catalog,
        )?;
        let pat_cond = encode_pattern_cond(
            tm,
            &arm.pattern,
            &scrut_term,
            scrut_ty.as_ref(),
            enum_catalog,
        )?;
        let guard_cond = if let Some(guard) = &arm.guard {
            encode_expr(tm, guard, &arm_vars, enum_catalog)?
        } else {
            tm.mk_boolean(true)
        };
        let arm_cond = mk_and(tm, &[pat_cond, guard_cond]);
        let arm_updates =
            collect_system_action_sequence_updates(tm, &arm.body, fields, &arm_vars, enum_catalog)?;
        fallback = Some(match fallback {
            None => {
                if arm.guard.is_none()
                    && matches!(
                        arm.pattern,
                        crate::ir::types::IRPattern::PWild
                            | crate::ir::types::IRPattern::PVar { .. }
                    )
                {
                    arm_updates
                } else {
                    return Err(
                        "cvc5 SyGuS system action match requires a final wildcard or var fallback arm"
                            .to_owned(),
                    );
                }
            }
            Some(else_updates) => merge_system_match_update_maps(
                tm,
                fields,
                &arm_cond,
                &arm_updates,
                &else_updates,
                curr_vars,
            )?,
        });
    }

    fallback.ok_or_else(|| "cvc5 SyGuS system action match required at least one arm".to_owned())
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
            "cvc5 SyGuS system safety only supports finite Bool/enum action params today (`{}`)",
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
        IRType::Enum { name, variants } => {
            let mut values = Vec::new();
            for variant in variants {
                let payload_variant = enum_catalog.payload_variant(name, &variant.name)?;
                let field_values = variant
                    .fields
                    .iter()
                    .map(|field| finite_domain_values(tm, &field.ty, enum_catalog))
                    .collect::<Option<Vec<_>>>()?;
                for args in cartesian_product_terms(&field_values) {
                    let mut children = Vec::with_capacity(1 + args.len());
                    children.push(payload_variant.constructor.clone());
                    children.extend(args);
                    values.push(tm.mk_term(Cvc5Kind::CVC5_KIND_APPLY_CONSTRUCTOR, &children));
                }
            }
            (!values.is_empty()).then_some(values)
        }
        _ => None,
    }
}

fn cartesian_product_terms(groups: &[Vec<Cvc5Term>]) -> Vec<Vec<Cvc5Term>> {
    let mut products = vec![Vec::new()];
    for group in groups {
        if group.is_empty() {
            return Vec::new();
        }
        let mut next = Vec::with_capacity(products.len() * group.len());
        for product in &products {
            for item in group {
                let mut extended = product.clone();
                extended.push(item.clone());
                next.push(extended);
            }
        }
        products = next;
    }
    products
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
            "cvc5 SyGuS only supports finite Bool/enum domains for finite quantifiers".to_owned(),
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
                        conjuncts.push(
                            tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, std::slice::from_ref(body_j)),
                        );
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

pub(super) fn encode_finite_choose_expr(
    tm: &Cvc5Tm,
    var: &str,
    domain: &IRType,
    predicate: Option<&IRExpr>,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
        return Err("cvc5 SyGuS only supports finite Bool/enum domains for choose".to_owned());
    };
    let Some(default) = candidates.first().cloned() else {
        return Err("cvc5 SyGuS choose requires a non-empty finite domain".to_owned());
    };

    let mut choice = default;
    for candidate in candidates.iter().rev() {
        let mut scoped = vars.clone();
        scoped.insert(var.to_owned(), candidate.clone());
        let cond = if let Some(predicate) = predicate {
            encode_expr(tm, predicate, &scoped, enum_catalog)?
        } else {
            tm.mk_boolean(true)
        };
        choice = tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[cond, candidate.clone(), choice]);
    }
    Ok(choice)
}

pub(super) fn zero_like(tm: &Cvc5Tm, term: &Cvc5Term) -> Cvc5Term {
    if term.sort() == tm.real_sort() {
        tm.mk_real_from_rational(0, 1)
    } else {
        tm.mk_integer(0)
    }
}

pub(super) fn one_like(tm: &Cvc5Tm, term: &Cvc5Term) -> Cvc5Term {
    if term.sort() == tm.real_sort() {
        tm.mk_real_from_rational(1, 1)
    } else {
        tm.mk_integer(1)
    }
}

pub(super) fn encode_finite_aggregate_expr(
    tm: &Cvc5Tm,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    domain: &IRType,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    let Some(candidates) = finite_domain_values(tm, domain, enum_catalog) else {
        return Err(
            "cvc5 SyGuS only supports finite Bool/enum domains for finite aggregates".to_owned(),
        );
    };
    if candidates.is_empty() {
        return match kind {
            crate::ir::types::IRAggKind::Sum | crate::ir::types::IRAggKind::Count => {
                Ok(tm.mk_integer(0))
            }
            crate::ir::types::IRAggKind::Product => Ok(tm.mk_integer(1)),
            crate::ir::types::IRAggKind::Min | crate::ir::types::IRAggKind::Max => Err(format!(
                "cvc5 SyGuS {kind:?} aggregate requires a non-empty finite domain"
            )),
        };
    }

    let mut slot_data = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let mut scoped = vars.clone();
        scoped.insert(var.to_owned(), candidate);
        let mut active = tm.mk_boolean(true);
        if let Some(filter) = in_filter {
            active = encode_expr(tm, filter, &scoped, enum_catalog)?;
        }
        if kind == crate::ir::types::IRAggKind::Count {
            let pred = encode_expr(tm, body, &scoped, enum_catalog)?;
            active = mk_and(tm, &[active, pred]);
            slot_data.push((active, tm.mk_integer(1)));
        } else {
            let value = encode_expr(tm, body, &scoped, enum_catalog)?;
            slot_data.push((active, value));
        }
    }

    match kind {
        crate::ir::types::IRAggKind::Sum | crate::ir::types::IRAggKind::Count => {
            let sample = &slot_data[0].1;
            let zero = zero_like(tm, sample);
            let mut acc = zero.clone();
            for (active, value) in &slot_data {
                let contribution = tm.mk_term(
                    Cvc5Kind::CVC5_KIND_ITE,
                    &[active.clone(), value.clone(), zero.clone()],
                );
                acc = tm.mk_term(Cvc5Kind::CVC5_KIND_ADD, &[acc, contribution]);
            }
            Ok(acc)
        }
        crate::ir::types::IRAggKind::Product => {
            let sample = &slot_data[0].1;
            let one = one_like(tm, sample);
            let mut acc = one.clone();
            for (active, value) in &slot_data {
                let contribution = tm.mk_term(
                    Cvc5Kind::CVC5_KIND_ITE,
                    &[active.clone(), value.clone(), one.clone()],
                );
                acc = tm.mk_term(Cvc5Kind::CVC5_KIND_MULT, &[acc, contribution]);
            }
            Ok(acc)
        }
        crate::ir::types::IRAggKind::Min | crate::ir::types::IRAggKind::Max => {
            let is_min = kind == crate::ir::types::IRAggKind::Min;
            let mut acc = slot_data[0].1.clone();
            let mut any_active = slot_data[0].0.clone();
            for (active, value) in slot_data.iter().skip(1) {
                let better_kind = if is_min {
                    Cvc5Kind::CVC5_KIND_LT
                } else {
                    Cvc5Kind::CVC5_KIND_GT
                };
                let better = tm.mk_term(better_kind, &[value.clone(), acc.clone()]);
                let first_active = mk_and(
                    tm,
                    &[
                        active.clone(),
                        tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[any_active.clone()]),
                    ],
                );
                let take = mk_or(tm, &[first_active, mk_and(tm, &[active.clone(), better])]);
                acc = tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[take, value.clone(), acc]);
                any_active = mk_or(tm, &[any_active, active.clone()]);
            }
            let undef = tm.mk_var(acc.sort(), &format!("__sygus_{kind:?}_{var}_undef"));
            Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[any_active, acc, undef]))
        }
    }
}

fn sum_bool_terms(tm: &Cvc5Tm, predicates: &[Cvc5Term]) -> Cvc5Term {
    let mut acc = tm.mk_integer(0);
    for predicate in predicates {
        let contribution = tm.mk_term(
            Cvc5Kind::CVC5_KIND_ITE,
            &[predicate.clone(), tm.mk_integer(1), tm.mk_integer(0)],
        );
        acc = tm.mk_term(Cvc5Kind::CVC5_KIND_ADD, &[acc, contribution]);
    }
    acc
}

fn encode_finite_source_membership<F>(
    tm: &Cvc5Tm,
    source: Option<&IRExpr>,
    candidate: &Cvc5Term,
    vars: &HashMap<String, Cvc5Term>,
    encode_with_vars: &mut F,
) -> Result<Cvc5Term, String>
where
    F: FnMut(&IRExpr, &HashMap<String, Cvc5Term>) -> Result<Cvc5Term, String>,
{
    let Some(source) = source else {
        return Ok(tm.mk_boolean(true));
    };
    let elements = match source {
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements,
        _ => {
            return Err(
                "cvc5 SyGuS cardinality only supports finite literal sources for set comprehensions"
                    .to_owned(),
            );
        }
    };
    let mut matches = Vec::with_capacity(elements.len());
    for element in elements {
        let element_term = encode_with_vars(element, vars)?;
        matches.push(tm.mk_term(
            Cvc5Kind::CVC5_KIND_EQUAL,
            &[element_term, candidate.clone()],
        ));
    }
    Ok(mk_or(tm, &matches))
}

pub(super) fn encode_finite_card_expr<F>(
    tm: &Cvc5Tm,
    expr: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    mut encode_with_vars: F,
) -> Result<Cvc5Term, String>
where
    F: FnMut(&IRExpr, &HashMap<String, Cvc5Term>) -> Result<Cvc5Term, String>,
{
    match expr {
        IRExpr::SeqLit { elements, .. } => Ok(tm.mk_integer(elements.len() as i64)),
        IRExpr::SetLit {
            elements,
            ty: IRType::Set {
                element: element_ty,
            },
            ..
        } => {
            let Some(candidates) = finite_domain_values(tm, element_ty, enum_catalog) else {
                return Err(
                    "cvc5 SyGuS cardinality only supports finite Bool/enum set literals today"
                        .to_owned(),
                );
            };
            let mut memberships = Vec::with_capacity(candidates.len());
            for candidate in candidates {
                let mut matches = Vec::with_capacity(elements.len());
                for element in elements {
                    let element_term = encode_with_vars(element, vars)?;
                    matches.push(tm.mk_term(
                        Cvc5Kind::CVC5_KIND_EQUAL,
                        &[element_term, candidate.clone()],
                    ));
                }
                memberships.push(mk_or(tm, &matches));
            }
            Ok(sum_bool_terms(tm, &memberships))
        }
        IRExpr::MapLit {
            entries,
            ty: IRType::Map { key: key_ty, .. },
            ..
        } => {
            let Some(candidates) = finite_domain_values(tm, key_ty, enum_catalog) else {
                return Err(
                    "cvc5 SyGuS cardinality only supports finite Bool/enum map literal keys today"
                        .to_owned(),
                );
            };
            let mut memberships = Vec::with_capacity(candidates.len());
            for candidate in candidates {
                let mut matches = Vec::with_capacity(entries.len());
                for (key, _) in entries {
                    let key_term = encode_with_vars(key, vars)?;
                    matches.push(
                        tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[key_term, candidate.clone()]),
                    );
                }
                memberships.push(mk_or(tm, &matches));
            }
            Ok(sum_bool_terms(tm, &memberships))
        }
        IRExpr::SetComp {
            var,
            domain,
            source,
            filter,
            projection,
            ..
        } => {
            let Some(domain_values) = finite_domain_values(tm, domain, enum_catalog) else {
                return Err(
                    "cvc5 SyGuS cardinality only supports finite Bool/enum set-comprehension domains"
                        .to_owned(),
                );
            };

            if let Some(projection) = projection {
                let Some(projection_ty) = sygus_expr_type(projection) else {
                    return Err(
                        "cvc5 SyGuS cardinality requires a finite projection type".to_owned()
                    );
                };
                let Some(projected_values) = finite_domain_values(tm, projection_ty, enum_catalog)
                else {
                    return Err(
                        "cvc5 SyGuS cardinality only supports finite Bool/enum set-comprehension projections"
                            .to_owned(),
                    );
                };
                let mut memberships = Vec::with_capacity(projected_values.len());
                for projected_value in projected_values {
                    let mut witnesses = Vec::with_capacity(domain_values.len());
                    for domain_value in &domain_values {
                        let mut scoped = vars.clone();
                        scoped.insert(var.clone(), domain_value.clone());
                        let source_member = encode_finite_source_membership(
                            tm,
                            source.as_deref(),
                            domain_value,
                            vars,
                            &mut encode_with_vars,
                        )?;
                        let filter_term = encode_with_vars(filter, &scoped)?;
                        let projection_term = encode_with_vars(projection, &scoped)?;
                        let projection_eq = tm.mk_term(
                            Cvc5Kind::CVC5_KIND_EQUAL,
                            &[projection_term, projected_value.clone()],
                        );
                        witnesses.push(mk_and(tm, &[source_member, filter_term, projection_eq]));
                    }
                    memberships.push(mk_or(tm, &witnesses));
                }
                return Ok(sum_bool_terms(tm, &memberships));
            }

            let mut memberships = Vec::with_capacity(domain_values.len());
            for domain_value in domain_values {
                let mut scoped = vars.clone();
                let source_member = encode_finite_source_membership(
                    tm,
                    source.as_deref(),
                    &domain_value,
                    vars,
                    &mut encode_with_vars,
                )?;
                scoped.insert(var.clone(), domain_value);
                let filter_term = encode_with_vars(filter, &scoped)?;
                memberships.push(mk_and(tm, &[source_member, filter_term]));
            }
            Ok(sum_bool_terms(tm, &memberships))
        }
        _ => Err(format!(
            "cvc5 SyGuS cardinality does not support expression shape: {expr:?}"
        )),
    }
}

pub(super) fn encode_finite_set_membership_expr<F>(
    tm: &Cvc5Tm,
    set_expr: &IRExpr,
    key_expr: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    mut encode_with_vars: F,
) -> Result<Cvc5Term, String>
where
    F: FnMut(&IRExpr, &HashMap<String, Cvc5Term>) -> Result<Cvc5Term, String>,
{
    let key_term = encode_with_vars(key_expr, vars)?;
    match set_expr {
        IRExpr::SetLit { elements, .. } => {
            let mut matches = Vec::with_capacity(elements.len());
            for element in elements {
                let element_term = encode_with_vars(element, vars)?;
                matches
                    .push(tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[element_term, key_term.clone()]));
            }
            Ok(mk_or(tm, &matches))
        }
        IRExpr::SetComp {
            var,
            domain,
            source,
            filter,
            projection,
            ..
        } => {
            let Some(domain_values) = finite_domain_values(tm, domain, enum_catalog) else {
                return Err(
                    "cvc5 SyGuS set membership only supports finite Bool/enum set-comprehension domains"
                        .to_owned(),
                );
            };
            let mut witnesses = Vec::with_capacity(domain_values.len());
            for domain_value in domain_values {
                let source_member = encode_finite_source_membership(
                    tm,
                    source.as_deref(),
                    &domain_value,
                    vars,
                    &mut encode_with_vars,
                )?;
                let mut scoped = vars.clone();
                scoped.insert(var.clone(), domain_value.clone());
                let filter_term = encode_with_vars(filter, &scoped)?;
                let member_term = if let Some(projection) = projection {
                    let projection_term = encode_with_vars(projection, &scoped)?;
                    tm.mk_term(
                        Cvc5Kind::CVC5_KIND_EQUAL,
                        &[projection_term, key_term.clone()],
                    )
                } else {
                    tm.mk_term(Cvc5Kind::CVC5_KIND_EQUAL, &[domain_value, key_term.clone()])
                };
                witnesses.push(mk_and(tm, &[source_member, filter_term, member_term]));
            }
            Ok(mk_or(tm, &witnesses))
        }
        _ => Err(format!(
            "cvc5 SyGuS set membership does not support expression shape: {set_expr:?}"
        )),
    }
}

fn default_term_for_type(
    tm: &Cvc5Tm,
    ty: &IRType,
    enum_catalog: &EnumCatalog,
) -> Result<Cvc5Term, String> {
    match ty {
        IRType::Bool => Ok(tm.mk_boolean(false)),
        IRType::Int => Ok(tm.mk_integer(0)),
        IRType::Real => Ok(tm.mk_real_from_rational(0, 1)),
        IRType::Enum { .. } => finite_domain_values(tm, ty, enum_catalog)
            .and_then(|values| values.into_iter().next())
            .ok_or_else(|| {
                "cvc5 SyGuS map literal lookup requires a non-empty finite enum value type"
                    .to_owned()
            }),
        other => Err(format!(
            "cvc5 SyGuS map literal lookup does not support default value for type {other:?}"
        )),
    }
}

pub(super) fn encode_finite_map_lookup_expr<F>(
    tm: &Cvc5Tm,
    map_expr: &IRExpr,
    key_expr: &IRExpr,
    vars: &HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
    mut encode_with_vars: F,
) -> Result<Option<Cvc5Term>, String>
where
    F: FnMut(&IRExpr, &HashMap<String, Cvc5Term>) -> Result<Cvc5Term, String>,
{
    let IRExpr::MapLit {
        entries,
        ty: IRType::Map { value, .. },
        ..
    } = map_expr
    else {
        return Ok(None);
    };

    let key_term = encode_with_vars(key_expr, vars)?;
    let mut choice = default_term_for_type(tm, value, enum_catalog)?;
    for (entry_key, entry_value) in entries {
        let entry_key_term = encode_with_vars(entry_key, vars)?;
        let entry_value_term = encode_with_vars(entry_value, vars)?;
        if entry_value_term.sort() != choice.sort() {
            return Err(
                "cvc5 SyGuS map literal lookup entry value has incompatible sort".to_owned(),
            );
        }
        let key_eq = tm.mk_term(
            Cvc5Kind::CVC5_KIND_EQUAL,
            &[entry_key_term, key_term.clone()],
        );
        choice = tm.mk_term(Cvc5Kind::CVC5_KIND_ITE, &[key_eq, entry_value_term, choice]);
    }
    Ok(Some(choice))
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
        IRExpr::Aggregate { body, .. } => sygus_expr_type(body),
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
    tm: &Cvc5Tm,
    pattern: &crate::ir::types::IRPattern,
    scrut: &Cvc5Term,
    scrut_ty: Option<&IRType>,
    env: &mut HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<(), String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild => Ok(()),
        IRPattern::PVar { name } => {
            env.insert(name.clone(), scrut.clone());
            Ok(())
        }
        IRPattern::PCtor { name, fields } => {
            if let Some(IRType::Enum {
                name: enum_name, ..
            }) = scrut_ty
            {
                if let Some(variant) = enum_catalog.payload_variant(enum_name, name) {
                    for field in fields {
                        let accessor = variant.accessors.get(&field.name).ok_or_else(|| {
                            format!(
                                "cvc5 SyGuS payload match cannot find constructor field `{}`",
                                field.name
                            )
                        })?;
                        let selected = tm.mk_term(
                            Cvc5Kind::CVC5_KIND_APPLY_SELECTOR,
                            &[accessor.term.clone(), scrut.clone()],
                        );
                        bind_pattern_vars(
                            tm,
                            &field.pattern,
                            &selected,
                            Some(&accessor.ty),
                            env,
                            enum_catalog,
                        )?;
                    }
                    return Ok(());
                }
            }
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
            bind_pattern_vars(tm, left, scrut, scrut_ty, env, enum_catalog)
        }
    }
}

fn ctor_name_matches(pattern_name: &str, enum_name: &str, ctor: &str) -> bool {
    pattern_name == ctor
        || pattern_name == format!("{enum_name}::{ctor}")
        || pattern_name
            .split_once("::")
            .is_some_and(|(_, bare)| bare == ctor)
}

fn bind_static_payload_pattern_vars(
    tm: &Cvc5Tm,
    pattern: &crate::ir::types::IRPattern,
    scrutinee: &IRExpr,
    env: &mut HashMap<String, Cvc5Term>,
    enum_catalog: &EnumCatalog,
) -> Result<bool, String> {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PWild => Ok(true),
        IRPattern::PVar { name } => {
            let value = encode_expr(tm, scrutinee, env, enum_catalog)?;
            env.insert(name.clone(), value);
            Ok(true)
        }
        IRPattern::PCtor { name, fields } if !fields.is_empty() => {
            let IRExpr::Ctor {
                enum_name,
                ctor,
                args,
                ..
            } = scrutinee
            else {
                return Ok(false);
            };
            if !ctor_name_matches(name, enum_name, ctor) {
                return Ok(false);
            }
            for field in fields {
                let Some((_, arg_expr)) = args.iter().find(|(arg_name, _)| arg_name == &field.name)
                else {
                    return Err(format!(
                        "cvc5 SyGuS static payload match cannot find constructor field `{}`",
                        field.name
                    ));
                };
                bind_static_payload_pattern_vars(tm, &field.pattern, arg_expr, env, enum_catalog)?;
            }
            Ok(true)
        }
        IRPattern::PCtor { .. } => Ok(false),
        IRPattern::POr { left, right } => {
            let mut left_env = env.clone();
            if bind_static_payload_pattern_vars(tm, left, scrutinee, &mut left_env, enum_catalog)? {
                *env = left_env;
                return Ok(true);
            }
            bind_static_payload_pattern_vars(tm, right, scrutinee, env, enum_catalog)
        }
    }
}

fn encode_static_payload_pattern_cond(
    tm: &Cvc5Tm,
    pattern: &crate::ir::types::IRPattern,
    scrutinee: &IRExpr,
) -> Option<Cvc5Term> {
    use crate::ir::types::IRPattern;
    match (pattern, scrutinee) {
        (IRPattern::PWild | IRPattern::PVar { .. }, _) => Some(tm.mk_boolean(true)),
        (
            IRPattern::PCtor { name, fields },
            IRExpr::Ctor {
                enum_name, ctor, ..
            },
        ) if !fields.is_empty() => Some(tm.mk_boolean(ctor_name_matches(name, enum_name, ctor))),
        (IRPattern::POr { left, right }, _) => {
            let lhs = encode_static_payload_pattern_cond(tm, left, scrutinee)?;
            let rhs = encode_static_payload_pattern_cond(tm, right, scrutinee)?;
            Some(mk_or(tm, &[lhs, rhs]))
        }
        _ => None,
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
        IRPattern::PCtor { name, fields } => match scrut_ty {
            Some(IRType::Enum {
                name: enum_name, ..
            }) if enum_catalog.payload_variant(enum_name, name).is_some() => {
                let variant = enum_catalog
                    .payload_variant(enum_name, name)
                    .expect("payload variant checked above");
                Ok(tm.mk_term(
                    Cvc5Kind::CVC5_KIND_APPLY_TESTER,
                    &[variant.tester.clone(), scrutinee.clone()],
                ))
            }
            Some(IRType::Enum {
                name: enum_name, ..
            }) => {
                if !fields.is_empty() {
                    return Err(format!(
                            "cvc5 SyGuS match does not support constructor-field patterns for fieldless enum `{enum_name}` (`{name}`)"
                        ));
                }
                let idx = enum_catalog
                    .get(enum_name)
                    .and_then(|mapping| {
                        mapping.get(name).or_else(|| {
                            name.split_once("::")
                                .and_then(|(_, ctor)| mapping.get(ctor))
                        })
                    })
                    .copied()
                    .ok_or_else(|| {
                        format!("unsupported enum constructor pattern `{name}` in cvc5 SyGuS slice")
                    })?;
                Ok(tm.mk_term(
                    Cvc5Kind::CVC5_KIND_EQUAL,
                    &[scrutinee.clone(), tm.mk_integer(idx)],
                ))
            }
            _ => Err(format!(
                "constructor pattern `{name}` requires a fieldless-enum scrutinee in cvc5 SyGuS"
            )),
        },
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
    let scrut_term = match encode_expr(tm, scrutinee, vars, enum_catalog) {
        Ok(term) => term,
        Err(_)
            if matches!(
                scrutinee,
                IRExpr::Ctor { args, .. } if !args.is_empty()
            ) =>
        {
            tm.mk_integer(0)
        }
        Err(err) => return Err(err),
    };
    let scrut_ty = sygus_match_scrutinee_type(scrutinee);

    let mut fallback = None;
    for arm in arms.iter().rev() {
        let mut arm_env = vars.clone();
        let handled_static = bind_static_payload_pattern_vars(
            tm,
            &arm.pattern,
            scrutinee,
            &mut arm_env,
            enum_catalog,
        )?;
        if !handled_static {
            bind_pattern_vars(
                tm,
                &arm.pattern,
                &scrut_term,
                scrut_ty.as_ref(),
                &mut arm_env,
                enum_catalog,
            )?;
        }
        let pat_cond = encode_static_payload_pattern_cond(tm, &arm.pattern, scrutinee)
            .map_or_else(
                || {
                    encode_pattern_cond(
                        tm,
                        &arm.pattern,
                        &scrut_term,
                        scrut_ty.as_ref(),
                        enum_catalog,
                    )
                },
                Ok,
            )?;
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

pub(super) fn encode_payload_ctor_expr<F>(
    tm: &Cvc5Tm,
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
    enum_catalog: &EnumCatalog,
    mut encode_arg: F,
) -> Result<Option<Cvc5Term>, String>
where
    F: FnMut(&IRExpr) -> Result<Cvc5Term, String>,
{
    let Some(variant) = enum_catalog.payload_variant(enum_name, ctor) else {
        return Ok(None);
    };

    let mut children = Vec::with_capacity(1 + variant.accessors.len());
    children.push(variant.constructor.clone());
    for field_name in &variant.field_order {
        let accessor = variant
            .accessors
            .get(field_name)
            .expect("field order must reference known payload accessor");
        let (_, arg_expr) = args
            .iter()
            .find(|(arg_name, _)| arg_name == field_name)
            .ok_or_else(|| {
                format!(
                    "cvc5 SyGuS payload constructor `{enum_name}::{ctor}` is missing field `{field_name}`"
                )
            })?;
        let arg_term = encode_arg(arg_expr)?;
        if arg_term.sort() != accessor.term.sort().dt_selector_codomain() {
            return Err(format!(
                "cvc5 SyGuS payload constructor `{enum_name}::{ctor}` field `{field_name}` has incompatible sort"
            ));
        }
        children.push(arg_term);
    }
    if args.len() != variant.accessors.len() {
        return Err(format!(
            "cvc5 SyGuS payload constructor `{enum_name}::{ctor}` received unexpected fields"
        ));
    }
    Ok(Some(
        tm.mk_term(Cvc5Kind::CVC5_KIND_APPLY_CONSTRUCTOR, &children),
    ))
}

pub(super) fn encode_static_payload_field_projection<F>(
    field: &str,
    args: &[(String, IRExpr)],
    mut encode_arg: F,
) -> Result<Option<Cvc5Term>, String>
where
    F: FnMut(&IRExpr) -> Result<Cvc5Term, String>,
{
    if let Some((_, arg_expr)) = args.iter().find(|(arg_name, _)| arg_name == field) {
        return Ok(Some(encode_arg(arg_expr)?));
    }
    Ok(None)
}

pub(super) fn encode_dynamic_payload_field_projection(
    tm: &Cvc5Tm,
    field: &str,
    receiver: Cvc5Term,
    receiver_ty: Option<&IRType>,
    enum_catalog: &EnumCatalog,
) -> Result<Option<Cvc5Term>, String> {
    let Some(IRType::Enum { name, .. }) = receiver_ty else {
        return Ok(None);
    };
    let Some(accessor) = enum_catalog.payload_accessor_for_field(name, field)? else {
        return Ok(None);
    };
    Ok(Some(tm.mk_term(
        Cvc5Kind::CVC5_KIND_APPLY_SELECTOR,
        &[accessor.term.clone(), receiver],
    )))
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
            LitVal::Real { value } => real_lit_term(tm, *value),
            LitVal::Bool { value } => Ok(tm.mk_boolean(*value)),
            LitVal::Float { .. } | LitVal::Str { .. } => Err(
                "cvc5 SyGuS single-entity safety only supports integer, real, and boolean literals today"
                    .to_owned(),
            ),
        },
        IRExpr::Sorry { .. } => Ok(tm.mk_boolean(true)),
        IRExpr::Todo { .. } => Err("todo expression in cvc5 SyGuS slice".to_owned()),
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            if let Some(term) =
                encode_payload_ctor_expr(tm, enum_name, ctor, args, enum_catalog, |arg| {
                    encode_expr(tm, arg, vars, enum_catalog)
                })?
            {
                return Ok(term);
            }
            if !args.is_empty() {
                return Err(format!(
                    "cvc5 SyGuS safety does not support payload constructors yet (`{enum_name}::{ctor}`)"
                ));
            }
            let idx = lookup_enum_ctor_index(enum_catalog, enum_name, ctor).ok_or_else(|| {
                format!("unsupported enum constructor `{enum_name}::{ctor}` in SyGuS slice")
            })?;
            Ok(tm.mk_integer(*idx))
        }
        IRExpr::Var { name, ty, .. } => vars
            .get(name)
            .cloned()
            .or_else(|| encode_enum_atom_var(tm, name, ty, enum_catalog))
            .ok_or_else(|| format!("unsupported free variable `{name}` in SyGuS slice")),
        IRExpr::Field {
            expr: receiver,
            field,
            ..
        } => {
            if let IRExpr::Ctor { args, .. } = receiver.as_ref() {
                if let Some(term) =
                    encode_static_payload_field_projection(field, args, |arg| {
                        encode_expr(tm, arg, vars, enum_catalog)
                    })?
                {
                    return Ok(term);
                }
            }
            let receiver_term = encode_expr(tm, receiver, vars, enum_catalog)?;
            if let Some(term) = encode_dynamic_payload_field_projection(
                tm,
                field,
                receiver_term,
                sygus_expr_type(receiver),
                enum_catalog,
            )? {
                return Ok(term);
            }
            Err(format!(
                "unsupported field projection `{field}` in cvc5 SyGuS single-entity safety slice"
            ))
        }
        IRExpr::App { func, arg, .. } => {
            let IRExpr::Lam { param, body, .. } = func.as_ref() else {
                return Err("cvc5 SyGuS only supports inline lambda application today".to_owned());
            };
            let arg_term = encode_expr(tm, arg, vars, enum_catalog)?;
            let mut scoped = vars.clone();
            scoped.insert(param.clone(), arg_term);
            encode_expr(tm, body, &scoped, enum_catalog)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let inner = encode_expr(tm, operand, vars, enum_catalog)?;
            match op.as_str() {
                "OpNot" | "not" | "!" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NOT, &[inner])),
                "OpNeg" | "-" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_NEG, &[inner])),
                _ => Err(format!("unsupported unary op `{op}` in cvc5 SyGuS slice")),
            }
        }
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => {
            let lhs = encode_expr(tm, left, vars, enum_catalog)?;
            let rhs = encode_expr(tm, right, vars, enum_catalog)?;
            match op.as_str() {
                "OpAnd" | "and" | "&&" => Ok(mk_and(tm, &[lhs, rhs])),
                "OpOr" | "or" | "||" => Ok(mk_or(tm, &[lhs, rhs])),
                "OpImplies" | "implies" | "=>" => {
                    Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_IMPLIES, &[lhs, rhs]))
                }
                "OpXor" | "xor" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_XOR, &[lhs, rhs])),
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
                "OpDiv" | "/" if matches!(ty, IRType::Real) => {
                    Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_DIVISION, &[lhs, rhs]))
                }
                "OpDiv" | "/" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_INTS_DIVISION, &[lhs, rhs])),
                "OpMod" | "%" => Ok(tm.mk_term(Cvc5Kind::CVC5_KIND_INTS_MODULUS, &[lhs, rhs])),
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
        IRExpr::Block { exprs, .. } => {
            let mut last = tm.mk_boolean(true);
            for expr in exprs {
                last = encode_expr(tm, expr, vars, enum_catalog)?;
            }
            Ok(last)
        }
        IRExpr::VarDecl {
            name, init, rest, ..
        } => {
            let value = encode_expr(tm, init, vars, enum_catalog)?;
            let mut local = vars.clone();
            local.insert(name.clone(), value);
            encode_expr(tm, rest, &local, enum_catalog)
        }
        IRExpr::Prime { expr, .. } => encode_expr(tm, expr, vars, enum_catalog),
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
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => encode_finite_choose_expr(tm, var, domain, predicate.as_deref(), vars, enum_catalog),
        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            ..
        } => encode_finite_aggregate_expr(
            tm,
            *kind,
            var,
            domain,
            body,
            in_filter.as_deref(),
            vars,
            enum_catalog,
        ),
        IRExpr::Card { expr: inner, .. } => {
            encode_finite_card_expr(tm, inner, vars, enum_catalog, |expr, scoped| {
                encode_expr(tm, expr, scoped, enum_catalog)
            })
        }
        IRExpr::Index { map, key, .. } => {
            if let Some(term) =
                encode_finite_map_lookup_expr(tm, map, key, vars, enum_catalog, |expr, scoped| {
                    encode_expr(tm, expr, scoped, enum_catalog)
                })?
            {
                return Ok(term);
            }
            encode_finite_set_membership_expr(tm, map, key, vars, enum_catalog, |expr, scoped| {
                encode_expr(tm, expr, scoped, enum_catalog)
            })
        }
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
