//! Bounded verification harness — multi-slot entity pools with time-stepped variables.
//!
//! Implements the Alloy-style bounded model: each entity type has N slots
//! (from scope), each with an `active` flag and field variables per time step.
//! Actions are transition relations, events compose actions, and the harness
//! assembles domain/transition/frame/initial constraints for the solver.

use std::collections::{HashMap, HashSet};

use super::smt::Bool;

use crate::ir::types::{
    IRAction, IRAssumptionSet, IREntity, IRExpr, IRStep, IRSystem, IRTransParam, IRTransition,
    IRType, LitVal,
};

use super::context::VerifyContext;
use super::defenv;
use super::defenv::AppHeadKind;
use super::smt::{self, SmtValue};

// ── Multi-slot entity pool ──────────────────────────────────────────

/// Multi-slot pool: each entity type has `pool_size` slots, each with
/// `bound + 1` time steps. Variables are named `{entity}_s{slot}_{field}_t{step}`.
#[derive(Debug)]
pub struct SlotPool {
    /// (`entity`, `slot`, `field`) → vec of `SmtValue` per time step
    pub field_vars: HashMap<(String, usize, String), Vec<SmtValue>>,
    /// (`entity`, `slot`) → vec of `Bool` active flags per time step
    pub active_vars: HashMap<(String, usize), Vec<SmtValue>>,
    /// Entity name → number of slots
    pub pool_sizes: HashMap<String, usize>,
    /// Bound (number of transition steps)
    pub bound: usize,
    /// system flat state field variables.
    /// (`system_name`, `field_name`) → vec of `SmtValue` per time step.
    /// Field names may be compound for struct fields: "ui.screen".
    pub system_field_vars: HashMap<(String, String), Vec<SmtValue>>,
    /// set of struct-typed system field base names per system.
    /// Used to detect `Field(Var("ui"), "screen")` as a system field access.
    pub system_struct_fields: HashMap<String, HashSet<String>>,
}

fn expr_type(expr: &IRExpr) -> Option<&IRType> {
    match expr {
        IRExpr::Lit { ty, .. }
        | IRExpr::Var { ty, .. }
        | IRExpr::BinOp { ty, .. }
        | IRExpr::UnOp { ty, .. }
        | IRExpr::App { ty, .. }
        | IRExpr::Field { ty, .. }
        | IRExpr::Choose { ty, .. }
        | IRExpr::MapUpdate { ty, .. }
        | IRExpr::Index { ty, .. }
        | IRExpr::SetLit { ty, .. }
        | IRExpr::SeqLit { ty, .. }
        | IRExpr::MapLit { ty, .. }
        | IRExpr::SetComp { ty, .. } => Some(ty),
        IRExpr::Prime { expr, .. } => expr_type(expr),
        IRExpr::Let { body, .. } => expr_type(body),
        IRExpr::Ctor { .. } => None,
        _ => None,
    }
}

impl SlotPool {
    /// Look up a field variable for a specific entity slot at a time step.
    pub fn field_at(
        &self,
        entity: &str,
        slot: usize,
        field: &str,
        step: usize,
    ) -> Option<&SmtValue> {
        self.field_vars
            .get(&(entity.to_owned(), slot, field.to_owned()))
            .and_then(|v| v.get(step))
    }

    /// Look up the active flag for a specific entity slot at a time step.
    pub fn active_at(&self, entity: &str, slot: usize, step: usize) -> Option<&SmtValue> {
        self.active_vars
            .get(&(entity.to_owned(), slot))
            .and_then(|v| v.get(step))
    }

    /// Get the number of slots for an entity type.
    pub fn slots_for(&self, entity: &str) -> usize {
        *self.pool_sizes.get(entity).unwrap_or(&0)
    }

    /// look up a system flat state field variable at a time step.
    pub fn system_field_at(&self, system: &str, field: &str, step: usize) -> Option<&SmtValue> {
        self.system_field_vars
            .get(&(system.to_owned(), field.to_owned()))
            .and_then(|v| v.get(step))
    }

    /// check if a name is a struct-typed system field base name.
    pub fn is_system_struct_field(&self, system: &str, base_name: &str) -> bool {
        self.system_struct_fields
            .get(system)
            .is_some_and(|s| s.contains(base_name))
    }
}

/// Create a multi-slot pool from IR entities with given scope sizes.
///
/// `scopes` maps entity name → number of slots.
/// Creates `slots × (bound + 1)` variables per field, plus active flags.
#[allow(clippy::implicit_hasher)]
pub fn create_slot_pool(
    entities: &[IREntity],
    scopes: &HashMap<String, usize>,
    bound: usize,
) -> SlotPool {
    create_slot_pool_with_systems(entities, scopes, bound, &[])
}

/// Create a multi-slot pool with system flat state fields ().
#[allow(clippy::implicit_hasher)]
pub fn create_slot_pool_with_systems(
    entities: &[IREntity],
    scopes: &HashMap<String, usize>,
    bound: usize,
    systems: &[IRSystem],
) -> SlotPool {
    let mut field_vars = HashMap::new();
    let mut active_vars = HashMap::new();
    let mut pool_sizes = HashMap::new();

    for entity in entities {
        let n_slots = scopes.get(&entity.name).copied().unwrap_or(1);
        pool_sizes.insert(entity.name.clone(), n_slots);

        for slot in 0..n_slots {
            // Active flag per slot per step
            let actives: Vec<SmtValue> = (0..=bound)
                .map(|step| smt::bool_var(&format!("{}_s{}__active_t{}", entity.name, slot, step)))
                .collect();
            active_vars.insert((entity.name.clone(), slot), actives);

            // Field variables per slot per step
            for field in &entity.fields {
                let vars: Vec<SmtValue> = (0..=bound)
                    .map(|step| {
                        let name = format!("{}_s{}_{}_t{}", entity.name, slot, field.name, step);
                        match &field.ty {
                            IRType::Bool => smt::bool_var(&name),
                            IRType::Real | IRType::Float => smt::real_var(&name),
                            IRType::Map { .. } | IRType::Set { .. } => {
                                smt::array_var(&name, &field.ty)
                                    .expect("internal: array sort expected for Map/Set field")
                            }
                            IRType::Seq { element } => SmtValue::Dynamic(smt::dynamic_const(
                                &name,
                                &smt::seq_sort(element).sort(),
                            )),
                            _ => smt::int_var(&name),
                        }
                    })
                    .collect();
                field_vars.insert((entity.name.clone(), slot, field.name.clone()), vars);
            }
        }
    }

    // create Z3 variables for system flat state fields.
    let mut system_field_vars = HashMap::new();
    let mut system_struct_fields: HashMap<String, HashSet<String>> = HashMap::new();
    for sys in systems {
        for field in &sys.fields {
            let vars: Vec<SmtValue> = (0..=bound)
                .map(|step| {
                    let name = format!("{}__{}_t{}", sys.name, field.name, step);
                    match &field.ty {
                        IRType::Bool => smt::bool_var(&name),
                        IRType::Real | IRType::Float => smt::real_var(&name),
                        IRType::Map { .. } | IRType::Set { .. } => smt::array_var(&name, &field.ty)
                            .expect("internal: array sort expected for Map/Set field"),
                        IRType::Seq { element } => SmtValue::Dynamic(smt::dynamic_const(
                            &name,
                            &smt::seq_sort(element).sort(),
                        )),
                        _ => smt::int_var(&name),
                    }
                })
                .collect();
            system_field_vars.insert((sys.name.clone(), field.name.clone()), vars);
            // Track struct base names (fields with "." in their name).
            if let Some(base) = field.name.split('.').next() {
                if field.name.contains('.') {
                    system_struct_fields
                        .entry(sys.name.clone())
                        .or_default()
                        .insert(base.to_owned());
                }
            }
        }
    }

    SlotPool {
        field_vars,
        active_vars,
        pool_sizes,
        bound,
        system_field_vars,
        system_struct_fields,
    }
}

// ── Slot-scoped encoding context ─────────────────────────────────────

/// Context for encoding IR expressions scoped to a specific entity slot.
///
/// Bundles pool, verification context, entity name, slot index, and
/// any in-scope action/event parameters so that `encode_slot_expr` can
/// resolve `Var` references in the right order: params first, then slot fields.
///
/// `bindings` tracks variables from prior Choose blocks, mapping
/// `var_name` -> `(entity_name, slot_index)`. This enables cross-entity
/// field references like `r.product_id` in a subsequent Choose over Product.
pub struct SlotEncodeCtx<'a> {
    pub pool: &'a SlotPool,
    pub vctx: &'a VerifyContext,
    pub entity: &'a str,
    pub slot: usize,
    pub params: HashMap<String, SmtValue>,
    pub bindings: HashMap<String, (String, usize)>,
    /// the system whose step we're encoding. Empty when not in a system step context.
    pub system_name: &'a str,
    /// entity-typed step parameter names → entity type name.
    /// Enables Field(Var("item"), "status") resolution by looking up the
    /// param's entity slot fields directly from the pool.
    pub entity_param_types: &'a HashMap<String, String>,
    /// store-typed system parameter names → entity type name.
    /// Enables `x in store` quantifiers and store membership checks in guards.
    pub store_param_types: &'a HashMap<String, String>,
}

// ── Constraint generation ───────────────────────────────────────────

/// Generate domain constraints: enum fields stay within valid variant ID range.
///
/// For every entity slot × field × step, if the field type is an enum,
/// assert `min_id <= var <= max_id`.
pub fn domain_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
) -> Vec<Bool> {
    let mut constraints = Vec::new();

    for entity in entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            for field in &entity.fields {
                if let IRType::Enum { name, .. } = &field.ty {
                    if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                        for step in 0..=pool.bound {
                            if let Some(SmtValue::Int(var)) =
                                pool.field_at(&entity.name, slot, &field.name, step)
                            {
                                constraints.push(smt::int_ge(var, &smt::int_lit(min_id)));
                                constraints.push(smt::int_le(var, &smt::int_lit(max_id)));
                            }
                        }
                    }
                }
            }
        }
    }

    constraints
}

/// Generate initial state constraints: all slots inactive at step 0.
pub fn initial_state_constraints(pool: &SlotPool) -> Vec<Bool> {
    let mut constraints = Vec::new();

    for ((_entity, _slot), actives) in &pool.active_vars {
        // All slots start inactive
        if let SmtValue::Bool(active_t0) = &actives[0] {
            constraints.push(smt::bool_not(active_t0));
        }
    }

    constraints
}

/// Symmetry breaking: for each entity type, require that slots are activated
/// in order. If slot i is inactive at step k, then slot i+1 must also be
/// inactive at step k. This eliminates equivalent states where the same
/// entities appear in different slot orderings.
///
/// Halves (or more) the search space without excluding any behaviors.
pub fn symmetry_breaking_constraints(pool: &SlotPool) -> Vec<Bool> {
    let mut constraints = Vec::new();

    // Group slots by entity type
    let mut entities: HashMap<String, usize> = HashMap::new();
    for (entity, _slot) in pool.active_vars.keys() {
        let count = entities.entry(entity.clone()).or_insert(0);
        *count = (*count).max(pool.slots_for(entity));
    }

    for (entity, n_slots) in &entities {
        if *n_slots < 2 {
            continue;
        }
        // For each step, slot i inactive → slot i+1 inactive
        for step in 0..=pool.bound {
            for slot in 0..(*n_slots - 1) {
                if let (Some(SmtValue::Bool(act_i)), Some(SmtValue::Bool(act_j))) = (
                    pool.active_at(entity, slot, step),
                    pool.active_at(entity, slot + 1, step),
                ) {
                    // ¬active[i] → ¬active[i+1] ≡ active[i+1] → active[i]
                    constraints.push(smt::bool_implies(act_j, act_i));
                }
            }
        }
    }

    constraints
}

/// Encode an entity action as a transition relation for a specific slot.
///
/// Returns a `Bool` formula: `guard(slot, step) AND updates(slot, step, step+1) AND frame(slot, step, step+1)`.
///
/// `params` supplies pre-built Z3 variables for action parameters (from `Apply` args/refs).
#[allow(clippy::implicit_hasher)]
pub fn encode_action(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity: &IREntity,
    action: &IRTransition,
    slot: usize,
    step: usize,
    params: &HashMap<String, SmtValue>,
) -> Bool {
    try_encode_action(pool, vctx, entity, action, slot, step, params)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_action(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity: &IREntity,
    action: &IRTransition,
    slot: usize,
    step: usize,
    params: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let empty_ept: HashMap<String, String> = HashMap::new();
    let ctx = SlotEncodeCtx {
        pool,
        vctx,
        entity: &entity.name,
        slot,
        params: params.clone(),
        bindings: HashMap::new(),
        system_name: "",
        entity_param_types: &empty_ept,
        store_param_types: &empty_ept,
    };

    let mut conjuncts = Vec::new();

    // Guard: encode the requires clause for this slot at this step
    let guard = try_encode_slot_expr(&ctx, &action.guard, step)?;
    conjuncts.push(guard.to_bool()?);

    // Updates: for each primed assignment, set the field at step+1
    let updated_fields: Vec<String> = action.updates.iter().map(|u| u.field.clone()).collect();

    for update in &action.updates {
        let new_val = try_encode_slot_expr(&ctx, &update.value, step)?;
        if let Some(field_next) = pool.field_at(&entity.name, slot, &update.field, step + 1) {
            conjuncts.push(smt::smt_eq(&new_val, field_next)?);
        }
    }

    // Frame: fields NOT in updates stay the same
    for field in &entity.fields {
        if !updated_fields.contains(&field.name) {
            if let (Some(curr), Some(next)) = (
                pool.field_at(&entity.name, slot, &field.name, step),
                pool.field_at(&entity.name, slot, &field.name, step + 1),
            ) {
                conjuncts.push(smt::smt_eq(curr, next)?);
            }
        }
    }

    // Active flag stays true (action doesn't deactivate)
    if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
        pool.active_at(&entity.name, slot, step),
        pool.active_at(&entity.name, slot, step + 1),
    ) {
        conjuncts.push(act_curr.clone()); // must be active to act
        conjuncts.push(act_next.clone()); // stays active after
    }

    // enforce fsm transition validity. For each
    // fsm declared on this entity whose field this action mutates,
    // assert `(old == new) OR (old, new) ∈ fsm.transitions`. Identity
    // updates (`field' = field`) are exempted per — only
    // actual changes are checked. The verifier reports a counterexample
    // for any action that drives the field along an edge not in the
    // table.
    for fsm in &entity.fsm_decls {
        if !updated_fields.contains(&fsm.field) {
            continue;
        }
        let Some(old_val) = pool.field_at(&entity.name, slot, &fsm.field, step) else {
            continue;
        };
        let Some(new_val) = pool.field_at(&entity.name, slot, &fsm.field, step + 1) else {
            continue;
        };
        let mut allowed: Vec<Bool> = Vec::new();
        // Identity case — `field' = field` is always legal regardless
        // of the table.
        if let Ok(eq) = smt::smt_eq(old_val, new_val) {
            allowed.push(eq);
        }
        // Each table entry contributes one `pre == from AND post == to`
        // disjunct. Variant ids come from the shared variant assigner
        // so they agree with how `IRExpr::Ctor` is encoded elsewhere.
        for trans in &fsm.transitions {
            let from_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.from)?;
            let to_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.to)?;
            let from_val = smt::int_val(from_id);
            let to_val = smt::int_val(to_id);
            if let (Ok(pre_eq), Ok(post_eq)) = (
                smt::smt_eq(old_val, &from_val),
                smt::smt_eq(new_val, &to_val),
            ) {
                allowed.push(smt::bool_and(&[&pre_eq, &post_eq]));
            }
        }
        if !allowed.is_empty() {
            let refs: Vec<&Bool> = allowed.iter().collect();
            conjuncts.push(smt::bool_or(&refs));
        }
    }

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    Ok(smt::bool_and(&refs))
}

/// Encode a transition with explicit read/write variable maps.
///
/// Unlike `encode_action` which reads from `step` and writes to `step+1`,
/// this function reads guards and update value expressions from `read_vars`
/// and writes updates to `write_vars`. Fields not updated are framed from
/// `read_vars` to `write_vars`.
///
/// Used for sequential Apply chaining: first Apply reads from step k and
/// writes to intermediate vars; next Apply reads from those and writes to
/// step k+1.
#[allow(clippy::implicit_hasher)]
pub fn encode_action_with_vars(
    entity: &IREntity,
    action: &IRTransition,
    _slot: usize,
    read_vars: &HashMap<String, SmtValue>,
    write_vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> Bool {
    try_encode_action_with_vars(entity, action, _slot, read_vars, write_vars, vctx, params)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_action_with_vars(
    entity: &IREntity,
    action: &IRTransition,
    _slot: usize,
    read_vars: &HashMap<String, SmtValue>,
    write_vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    // Build a context that resolves field names from read_vars
    let mut conjuncts = Vec::new();

    // Guard: evaluate against read_vars
    let guard = try_eval_expr_with_vars(&action.guard, entity, read_vars, vctx, params)?;
    conjuncts.push(guard.to_bool()?);

    // Updates: evaluate value from read_vars, constrain write_vars
    let updated_fields: Vec<String> = action.updates.iter().map(|u| u.field.clone()).collect();
    for update in &action.updates {
        let new_val = try_eval_expr_with_vars(&update.value, entity, read_vars, vctx, params)?;
        if let Some(write_val) = write_vars.get(&update.field) {
            conjuncts.push(smt::smt_eq(&new_val, write_val)?);
        }
    }

    // Frame: fields NOT in updates copied from read to write
    for field in &entity.fields {
        if !updated_fields.contains(&field.name) {
            if let (Some(read_val), Some(write_val)) =
                (read_vars.get(&field.name), write_vars.get(&field.name))
            {
                conjuncts.push(smt::smt_eq(read_val, write_val)?);
            }
        }
    }

    // enforce fsm transition validity in the
    // chained-apply path too. Without this, an event that performs
    // multiple sequential applies on the same entity could bypass the
    // single-apply fsm constraint added in `encode_action`. Each fsm
    // declared on this entity whose field this action mutates gets a
    // `(old == new) OR ⋁ (old == from_i ∧ new == to_i)` constraint
    // built against the chained read/write vars (not the pool, since
    // intermediate state lives in fresh SMT vars). Identity updates
    // are exempt — only actual changes are checked.
    for fsm in &entity.fsm_decls {
        if !updated_fields.contains(&fsm.field) {
            continue;
        }
        let Some(old_val) = read_vars.get(&fsm.field) else {
            continue;
        };
        let Some(new_val) = write_vars.get(&fsm.field) else {
            continue;
        };
        let mut allowed: Vec<Bool> = Vec::new();
        if let Ok(eq) = smt::smt_eq(old_val, new_val) {
            allowed.push(eq);
        }
        for trans in &fsm.transitions {
            let from_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.from)?;
            let to_id = vctx.variants.try_id_of(&fsm.enum_name, &trans.to)?;
            let from_val = smt::int_val(from_id);
            let to_val = smt::int_val(to_id);
            if let (Ok(pre_eq), Ok(post_eq)) = (
                smt::smt_eq(old_val, &from_val),
                smt::smt_eq(new_val, &to_val),
            ) {
                allowed.push(smt::bool_and(&[&pre_eq, &post_eq]));
            }
        }
        if !allowed.is_empty() {
            let refs: Vec<&Bool> = allowed.iter().collect();
            conjuncts.push(smt::bool_or(&refs));
        }
    }

    if conjuncts.is_empty() {
        return Ok(smt::bool_const(true));
    }
    let refs: Vec<&Bool> = conjuncts.iter().collect();
    Ok(smt::bool_and(&refs))
}

/// Evaluate an IR expression using explicit variable maps instead of `SlotPool`.
///
/// Resolves field names from `vars` (a map of `field_name` → `SmtValue`).
/// Falls back to `params` for action parameters.
#[allow(clippy::only_used_in_recursion)]
#[allow(dead_code)]
fn eval_expr_with_vars(
    expr: &IRExpr,
    entity: &IREntity,
    vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> SmtValue {
    try_eval_expr_with_vars(expr, entity, vars, vctx, params).unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::only_used_in_recursion)]
fn try_eval_expr_with_vars(
    expr: &IRExpr,
    entity: &IREntity,
    vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(encode_slot_literal(value)),
        IRExpr::Var { name, .. } => {
            if let Some(val) = params.get(name) {
                return Ok(val.clone());
            }
            if let Some(val) = vars.get(name) {
                return Ok(val.clone());
            }
            Err(format!("variable not found in chained encoding: {name}"))
        }
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                // Qualified lookup in params (cross-entity or event-level refs)
                let qualified = format!("{name}.{field}");
                if let Some(val) = params.get(&qualified) {
                    return Ok(val.clone());
                }
                // Same-entity field: only resolve from vars (intermediate state)
                if let Some(val) = vars.get(field) {
                    return Ok(val.clone());
                }
                // Check unqualified in params as last resort
                if let Some(val) = params.get(field) {
                    return Ok(val.clone());
                }
            }
            // No blind fallback — strict resolution only
            Err(format!(
                "field {field} not found in chained encoding (vars: {:?}, params: {:?})",
                vars.keys().collect::<Vec<_>>(),
                params.keys().collect::<Vec<_>>()
            ))
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = try_eval_expr_with_vars(left, entity, vars, vctx, params)?;
            let r = try_eval_expr_with_vars(right, entity, vars, vctx, params)?;
            Ok(smt::binop(op, &l, &r)?)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = try_eval_expr_with_vars(operand, entity, vars, vctx, params)?;
            Ok(smt::unop(op, &v)?)
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = try_eval_expr_with_vars(map, entity, vars, vctx, params)?;
            let k = try_eval_expr_with_vars(key, entity, vars, vctx, params)?;
            let v = try_eval_expr_with_vars(value, entity, vars, vctx, params)?;
            Ok(SmtValue::Array(
                arr.as_array()
                    .map_err(|e| format!("chained map update array encoding failed: {e}"))?
                    .store(&k.to_dynamic(), &v.to_dynamic()),
            ))
        }
        IRExpr::Index { map, key, .. } => {
            let arr = try_eval_expr_with_vars(map, entity, vars, vctx, params)?;
            let k = try_eval_expr_with_vars(key, entity, vars, vctx, params)?;
            Ok(SmtValue::Dynamic(
                arr.as_array()
                    .map_err(|e| format!("chained index array encoding failed: {e}"))?
                    .select(&k.to_dynamic()),
            ))
        }
        _ => Err(format!(
            "unsupported expression in chained action encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

/// Encode a `create` action: find an inactive slot and activate it.
///
/// Returns a `Bool` formula: `exists slot_i. !active(i, step) AND active(i, step+1) AND fields...`
///
/// Each disjunct also frames all OTHER slots of the same entity so that
/// non-selected slots cannot take arbitrary values.
#[allow(clippy::implicit_hasher)]
pub fn encode_create(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity_name: &str,
    entity_ir: Option<&IREntity>,
    create_fields: &[(String, IRExpr)],
    step: usize,
    step_params: &HashMap<String, SmtValue>,
) -> Bool {
    try_encode_create(
        pool,
        vctx,
        entity_name,
        entity_ir,
        create_fields,
        step,
        step_params,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::implicit_hasher)]
pub fn try_encode_create(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entity_name: &str,
    entity_ir: Option<&IREntity>,
    create_fields: &[(String, IRExpr)],
    step: usize,
    step_params: &HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let empty_ept: HashMap<String, String> = HashMap::new();
    let n_slots = pool.slots_for(entity_name);
    let mut slot_disjuncts = Vec::new();

    for slot in 0..n_slots {
        let ctx = SlotEncodeCtx {
            pool,
            vctx,
            entity: entity_name,
            slot,
            params: step_params.clone(),
            bindings: HashMap::new(),
            system_name: "",
            entity_param_types: &empty_ept,
            store_param_types: &empty_ept,
        };

        let mut conjuncts = Vec::new();

        // Slot must be inactive at current step
        if let Some(SmtValue::Bool(act_curr)) = pool.active_at(entity_name, slot, step) {
            conjuncts.push(smt::bool_not(act_curr));
        }
        // Activate at next step
        if let Some(SmtValue::Bool(act_next)) = pool.active_at(entity_name, slot, step + 1) {
            conjuncts.push(act_next.clone());
        }

        // Set field values at next step from create block
        let create_field_names: HashSet<&str> =
            create_fields.iter().map(|(n, _)| n.as_str()).collect();
        for (field_name, value_expr) in create_fields {
            let val = try_encode_slot_expr(&ctx, value_expr, step)?;
            if let Some(field_next) = pool.field_at(entity_name, slot, field_name, step + 1) {
                conjuncts.push(smt::smt_eq(&val, field_next)?);
            }
        }

        // Apply entity defaults for fields NOT specified in the create block.
        // Without this, unconstrained fields could take any value, making the
        // verification overly permissive.
        //
        // When `initial_constraint` is present (from `in {...}` or `where`),
        // assert the constraint with `$` / field name substituted for the
        // field's next-step value, instead of fixing to a single default.
        if let Some(ent) = entity_ir {
            for field in &ent.fields {
                if create_field_names.contains(field.name.as_str()) {
                    continue; // already set by create block
                }
                if let Some(ref constraint_expr) = field.initial_constraint {
                    // Nondeterministic: encode the constraint with $ bound to field_next.
                    if let Some(field_next) =
                        pool.field_at(entity_name, slot, &field.name, step + 1)
                    {
                        let mut params = ctx.params.clone();
                        params.insert("$".to_owned(), field_next.clone());
                        params.insert(field.name.clone(), field_next.clone());
                        let pred_ctx = SlotEncodeCtx {
                            pool: ctx.pool,
                            vctx: ctx.vctx,
                            entity: ctx.entity,
                            slot: ctx.slot,
                            params,
                            bindings: ctx.bindings.clone(),
                            system_name: "",
                            entity_param_types: &empty_ept,
                            store_param_types: &empty_ept,
                        };
                        let val = try_encode_slot_expr(&pred_ctx, constraint_expr, step + 1)?;
                        if let SmtValue::Bool(b) = val {
                            conjuncts.push(b);
                        }
                    }
                } else if let Some(ref default_expr) = field.default {
                    // Deterministic: field_next == default
                    let val = try_encode_slot_expr(&ctx, default_expr, step)?;
                    if let Some(field_next) =
                        pool.field_at(entity_name, slot, &field.name, step + 1)
                    {
                        conjuncts.push(smt::smt_eq(&val, field_next)?);
                    }
                }
            }
        }

        // Frame all OTHER slots of this entity within the disjunct
        if let Some(ent) = entity_ir {
            let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
            conjuncts.extend(slot_frame);
        }

        let refs: Vec<&Bool> = conjuncts.iter().collect();
        if !refs.is_empty() {
            slot_disjuncts.push(smt::bool_and(&refs));
        }
    }

    // Any slot can be chosen for creation
    let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
    if refs.is_empty() {
        Ok(smt::bool_const(false)) // no slots available
    } else {
        Ok(smt::bool_or(&refs))
    }
}

/// Generate stutter (idle) constraint: all fields and active flags unchanged.
pub fn stutter_constraint(pool: &SlotPool, entities: &[IREntity], step: usize) -> Bool {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut conjuncts = Vec::new();

    for entity in entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            // Active flag unchanged
            if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
                pool.active_at(&entity.name, slot, step),
                pool.active_at(&entity.name, slot, step + 1),
            ) {
                conjuncts.push(smt::bool_eq(next, curr));
            }
            // All fields unchanged
            for field in &entity.fields {
                if let (Some(curr), Some(next)) = (
                    pool.field_at(&entity.name, slot, &field.name, step),
                    pool.field_at(&entity.name, slot, &field.name, step + 1),
                ) {
                    conjuncts.push(smt::smt_eq(curr, next).expect("internal: stutter smt_eq"));
                }
            }
        }
    }

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    smt::bool_and(&refs)
}

// ── Event encoding ──────────────────────────────────────────────────

/// Frame constraint for slots NOT touched by an event at a given step.
///
/// For every entity slot NOT in `touched`, asserts that all fields and
/// the active flag are unchanged from `step` to `step + 1`.
fn frame_untouched_slots(
    pool: &SlotPool,
    entities: &[IREntity],
    touched: &HashSet<(String, usize)>,
    step: usize,
) -> Vec<Bool> {
    let mut conjuncts = Vec::new();

    for entity in entities {
        let n_slots = pool.slots_for(&entity.name);
        for slot in 0..n_slots {
            if touched.contains(&(entity.name.clone(), slot)) {
                continue;
            }
            // Active flag unchanged
            if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
                pool.active_at(&entity.name, slot, step),
                pool.active_at(&entity.name, slot, step + 1),
            ) {
                conjuncts.push(smt::bool_eq(next, curr));
            }
            // All fields unchanged
            for field in &entity.fields {
                if let (Some(curr), Some(next)) = (
                    pool.field_at(&entity.name, slot, &field.name, step),
                    pool.field_at(&entity.name, slot, &field.name, step + 1),
                ) {
                    conjuncts
                        .push(smt::smt_eq(curr, next).expect("internal: frame untouched smt_eq"));
                }
            }
        }
    }

    conjuncts
}

/// Frame all slots of an entity EXCEPT the excluded one at a given step.
///
/// For each slot != `excluded_slot`, asserts that all fields and the active
/// flag are unchanged from `step` to `step + 1`. Used inside Choose disjuncts
/// so that non-selected slots are properly framed.
fn frame_entity_slots_except(
    pool: &SlotPool,
    entity: &IREntity,
    excluded_slot: usize,
    step: usize,
) -> Vec<Bool> {
    let mut conjuncts = Vec::new();
    let n_slots = pool.slots_for(&entity.name);

    for slot in 0..n_slots {
        if slot == excluded_slot {
            continue;
        }
        // Active flag unchanged
        if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
            pool.active_at(&entity.name, slot, step),
            pool.active_at(&entity.name, slot, step + 1),
        ) {
            conjuncts.push(smt::bool_eq(next, curr));
        }
        // All fields unchanged
        for field in &entity.fields {
            if let (Some(curr), Some(next)) = (
                pool.field_at(&entity.name, slot, &field.name, step),
                pool.field_at(&entity.name, slot, &field.name, step + 1),
            ) {
                conjuncts.push(smt::smt_eq(curr, next).expect("internal: frame except smt_eq"));
            }
        }
    }

    conjuncts
}

/// Frame a specific set of entity slots at a given step.
///
/// For each `(entity_name, slot_idx)` in `slots_to_frame`, asserts that all fields
/// and the active flag are unchanged from `step` to `step + 1`. Used inside
/// CrossCall disjunctions for per-branch framing: each branch frames slots in the
/// union that it didn't individually touch.
#[allow(clippy::implicit_hasher)]
pub fn frame_specific_slots(
    pool: &SlotPool,
    entities: &[IREntity],
    slots_to_frame: &HashSet<(String, usize)>,
    step: usize,
) -> Vec<Bool> {
    let mut frames = Vec::new();
    for (entity_name, slot_idx) in slots_to_frame {
        if let Some(entity) = entities.iter().find(|e| e.name == *entity_name) {
            // Active flag unchanged
            if let (Some(SmtValue::Bool(curr)), Some(SmtValue::Bool(next))) = (
                pool.active_at(entity_name, *slot_idx, step),
                pool.active_at(entity_name, *slot_idx, step + 1),
            ) {
                frames.push(smt::bool_eq(next, curr));
            }
            // All fields unchanged
            for field in &entity.fields {
                if let (Some(curr), Some(next)) = (
                    pool.field_at(entity_name, *slot_idx, &field.name, step),
                    pool.field_at(entity_name, *slot_idx, &field.name, step + 1),
                ) {
                    frames.push(
                        smt::smt_eq(curr, next).expect("internal: frame specific slot smt_eq"),
                    );
                }
            }
        }
    }
    frames
}

/// frame system flat state fields that were not modified.
///
/// For each system field NOT in `touched_fields`, asserts `field_t{step} == field_t{step+1}`.
#[allow(clippy::implicit_hasher)]
pub fn frame_system_fields(
    pool: &SlotPool,
    system: &IRSystem,
    touched_fields: &HashSet<String>,
    step: usize,
) -> Vec<Bool> {
    let mut frames = Vec::new();
    for field in &system.fields {
        if touched_fields.contains(&field.name) {
            continue;
        }
        if let (Some(curr), Some(next)) = (
            pool.system_field_at(&system.name, &field.name, step),
            pool.system_field_at(&system.name, &field.name, step + 1),
        ) {
            frames.push(smt::smt_eq(curr, next).expect("internal: frame system field smt_eq"));
        }
    }
    frames
}

/// extract system field names that are primed (modified) in step body ExprStmts.
///
/// Walks the step body for patterns like:
/// - `OpEq(Prime(Var(name)),...)` where name is a system field
/// - `OpEq(Prime(Field(Var(base), sub)),...)` where `base.sub` is a system field
#[allow(clippy::implicit_hasher)]
pub fn extract_primed_system_fields(
    body: &[IRAction],
    system_field_names: &HashSet<String>,
) -> HashSet<String> {
    let mut touched = HashSet::new();
    for action in body {
        if let IRAction::ExprStmt { expr } = action {
            collect_primed_fields(expr, system_field_names, &mut touched);
        }
    }
    touched
}

fn collect_primed_fields(
    expr: &IRExpr,
    sys_fields: &HashSet<String>,
    touched: &mut HashSet<String>,
) {
    match expr {
        IRExpr::BinOp { left, right, .. } => {
            collect_primed_fields(left, sys_fields, touched);
            collect_primed_fields(right, sys_fields, touched);
        }
        IRExpr::Prime { expr: inner, .. } => match inner.as_ref() {
            IRExpr::Var { name, .. } if sys_fields.contains(name) => {
                touched.insert(name.clone());
            }
            IRExpr::Field {
                expr: recv, field, ..
            } => {
                if let IRExpr::Var { name, .. } = recv.as_ref() {
                    let compound = format!("{name}.{field}");
                    if sys_fields.contains(&compound) {
                        touched.insert(compound);
                    }
                }
            }
            _ => {}
        },
        _ => {}
    }
}

/// encode initial state constraints for system flat state fields.
///
/// For each system field with a default value, asserts `field_t0 == default`.
pub fn system_field_initial_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    system: &IRSystem,
) -> Vec<Bool> {
    try_system_field_initial_constraints(pool, vctx, system).unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_system_field_initial_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    system: &IRSystem,
) -> Result<Vec<Bool>, String> {
    let empty_ept: HashMap<String, String> = HashMap::new();
    let mut constraints = Vec::new();
    for field in &system.fields {
        if let Some(ref default_expr) = field.default {
            if let Some(var_at_0) = pool.system_field_at(&system.name, &field.name, 0) {
                let ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: "",
                    slot: 0,
                    params: HashMap::new(),
                    bindings: HashMap::new(),
                    system_name: &system.name,
                    entity_param_types: &empty_ept,
                    store_param_types: &empty_ept,
                };
                let val = try_encode_slot_expr(&ctx, default_expr, 0)?;
                constraints.push(smt::smt_eq(var_at_0, &val)?);
            }
        }
    }
    Ok(constraints)
}

/// Build a `HashMap<String, SmtValue>` mapping action parameter names to Z3 values
/// from the positional `args` and `refs` of an `Apply` action.
///
/// `action.params[i].name` maps to `encode(args[i])`, and `action.refs[i].name` maps
/// to the slot-resolved value for the entity variable name in `refs[i]`.
#[allow(dead_code)]
fn build_apply_params(
    ctx: &SlotEncodeCtx<'_>,
    action: &IRTransition,
    args: &[IRExpr],
    refs: &[String],
    step: usize,
) -> HashMap<String, SmtValue> {
    try_build_apply_params(ctx, action, args, refs, step).unwrap_or_else(|msg| panic!("{msg}"))
}

fn try_build_apply_params(
    ctx: &SlotEncodeCtx<'_>,
    action: &IRTransition,
    args: &[IRExpr],
    refs: &[String],
    step: usize,
) -> Result<HashMap<String, SmtValue>, String> {
    let mut map = HashMap::new();

    // Wire positional args to action params
    for (param, arg_expr) in action.params.iter().zip(args.iter()) {
        let val = try_encode_slot_expr(ctx, arg_expr, step)?;
        map.insert(param.name.clone(), val);
    }

    // Wire refs to action refs (entity variable names → resolve from slot context)
    for (ref_decl, ref_name) in action.refs.iter().zip(refs.iter()) {
        // refs are entity variable names — resolve from params first, then slot fields
        if let Some(val) = ctx.params.get(ref_name) {
            map.insert(ref_decl.name.clone(), val.clone());
        } else if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, ref_name, step) {
            map.insert(ref_decl.name.clone(), val.clone());
        }
    }

    Ok(map)
}

/// Build a `HashMap<String, SmtValue>` of Z3 variables for event parameters.
///
/// Each parameter gets a fresh Z3 variable named `param_{name}_{step}`, scoped
/// to the given step so that parameter values are independent across steps.
pub(super) fn build_step_params(params: &[IRTransParam], step: usize) -> HashMap<String, SmtValue> {
    let mut map = HashMap::new();
    for p in params {
        let var = match &p.ty {
            IRType::Bool => smt::bool_var(&format!("param_{}_{}", p.name, step)),
            IRType::Real | IRType::Float => smt::real_var(&format!("param_{}_{}", p.name, step)),
            _ => smt::int_var(&format!("param_{}_{}", p.name, step)),
        };
        map.insert(p.name.clone(), var);
    }
    map
}

/// Context for guard expression encoding — tracks entity bindings from
/// enclosing quantifiers, similar to `PropertyCtx` in `mod.rs`.
struct GuardCtx {
    /// Quantifier-bound variables: `var_name` → (`entity_name`, `slot_index`)
    bindings: HashMap<String, (String, usize)>,
    /// Event parameter Z3 variables
    params: HashMap<String, SmtValue>,
    /// system name for flat state field resolution
    system_name: String,
    /// entity-typed param names → entity type name
    entity_param_types: HashMap<String, String>,
    /// store-typed system params → entity type name
    store_param_types: HashMap<String, String>,
}

impl GuardCtx {
    fn with_binding(&self, var: &str, entity: &str, slot: usize) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(var.to_owned(), (entity.to_owned(), slot));
        Self {
            bindings,
            params: self.params.clone(),
            system_name: self.system_name.clone(),
            entity_param_types: self.entity_param_types.clone(),
            store_param_types: self.store_param_types.clone(),
        }
    }
}

fn infer_store_quant_entity(
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
        IRExpr::BinOp { left, right, .. } => infer_store_quant_entity(var, left, store_param_types)
            .or_else(|| infer_store_quant_entity(var, right, store_param_types)),
        IRExpr::UnOp { operand, .. } => infer_store_quant_entity(var, operand, store_param_types),
        _ => None,
    }
}

fn encode_store_membership(
    pool: &SlotPool,
    entity_name: &str,
    key: &SmtValue,
    step: usize,
) -> SmtValue {
    let n_slots = pool.slots_for(entity_name);
    let mut disjuncts = Vec::new();
    for slot in 0..n_slots {
        if let Some(SmtValue::Bool(active)) = pool.active_at(entity_name, slot, step) {
            let slot_id = smt::int_val(slot as i64);
            let cond = smt::smt_eq(key, &slot_id).expect("internal: store membership eq");
            disjuncts.push(smt::bool_and(&[&cond, active]));
        }
    }
    if disjuncts.is_empty() {
        return SmtValue::Bool(smt::bool_const(false));
    }
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    SmtValue::Bool(smt::bool_or(&refs))
}

/// Encode an event guard expression, expanding entity quantifiers over slots.
///
/// Uses `GuardCtx` to track entity bindings from enclosing quantifiers,
/// ensuring that field references resolve correctly across nested quantifiers.
#[allow(dead_code)]
pub(super) fn encode_guard_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    store_param_types: &HashMap<String, String>,
    step: usize,
) -> Bool {
    try_encode_guard_expr(pool, vctx, expr, step_params, store_param_types, step)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub(super) fn try_encode_guard_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    store_param_types: &HashMap<String, String>,
    step: usize,
) -> Result<Bool, String> {
    let ctx = GuardCtx {
        bindings: HashMap::new(),
        params: step_params.clone(),
        system_name: String::new(),
        entity_param_types: HashMap::new(),
        store_param_types: store_param_types.clone(),
    };
    try_encode_guard_inner(pool, vctx, &ctx, expr, step)
}

/// /14: encode guard with system field context and entity param types.
#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
fn encode_guard_expr_for_system(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    step: usize,
    system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
) -> Bool {
    try_encode_guard_expr_for_system(
        pool,
        vctx,
        expr,
        step_params,
        step,
        system_name,
        entity_param_types,
        store_param_types,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_arguments)]
fn try_encode_guard_expr_for_system(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    step_params: &HashMap<String, SmtValue>,
    step: usize,
    system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
) -> Result<Bool, String> {
    let ctx = GuardCtx {
        bindings: HashMap::new(),
        params: step_params.clone(),
        system_name: system_name.to_owned(),
        entity_param_types: entity_param_types.clone(),
        store_param_types: store_param_types.clone(),
    };
    try_encode_guard_inner(pool, vctx, &ctx, expr, step)
}

#[allow(dead_code)]
fn encode_guard_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Bool {
    try_encode_guard_inner(pool, vctx, ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

fn try_encode_guard_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<Bool, String> {
    match expr {
        IRExpr::Exists {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = try_encode_guard_inner(pool, vctx, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    disjuncts.push(smt::bool_and(&[act, &body_val]));
                }
            }
            if disjuncts.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        IRExpr::Forall {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut conjuncts = Vec::new();
            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = try_encode_guard_inner(pool, vctx, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    conjuncts.push(smt::bool_implies(act, &body_val));
                }
            }
            if conjuncts.is_empty() {
                return Ok(smt::bool_const(true));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" => {
            let l = try_encode_guard_inner(pool, vctx, ctx, left, step)?;
            let r = try_encode_guard_inner(pool, vctx, ctx, right, step)?;
            Ok(match op.as_str() {
                "OpAnd" => smt::bool_and(&[&l, &r]),
                "OpOr" => smt::bool_or(&[&l, &r]),
                "OpImplies" => smt::bool_implies(&l, &r),
                _ => unreachable!(),
            })
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => Ok(smt::bool_not(
            &try_encode_guard_inner(pool, vctx, ctx, operand, step)?,
        )),
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Ok(smt::bool_const(*value)),
        // Non-boolean expressions (comparisons, field access, etc.) —
        // encode as value using the guard context bindings
        other => Ok(try_encode_guard_value(pool, vctx, ctx, other, step)?.to_bool()?),
    }
}

/// Encode a value expression within a guard context.
/// Resolves field references using the guard's entity bindings.
#[allow(dead_code)]
fn encode_guard_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> SmtValue {
    try_encode_guard_value(pool, vctx, ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

fn try_encode_guard_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(encode_slot_literal(value)),
        IRExpr::Var { name, .. } => {
            // Check event params first
            if let Some(val) = ctx.params.get(name.as_str()) {
                return Ok(val.clone());
            }
            // Check entity bindings (last-bound entity for bare field names)
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, name, step) {
                    return Ok(val.clone());
                }
            }
            // try system flat state field
            if !ctx.system_name.is_empty() {
                if let Some(val) = pool.system_field_at(&ctx.system_name, name, step) {
                    return Ok(val.clone());
                }
            }
            // Fallback to encode_slot_expr for remaining resolution
            let fallback_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: ctx.params.clone(),
                bindings: ctx.bindings.clone(),
                system_name: &ctx.system_name,
                entity_param_types: &ctx.entity_param_types,
                store_param_types: &ctx.store_param_types,
            };
            try_encode_slot_expr(&fallback_ctx, expr, step)
        }
        // Field, App, and other complex expressions — delegate to
        // encode_slot_expr which handles entity param field access,
        // system struct fields, and function calls.
        IRExpr::Field { .. } | IRExpr::App { .. } => {
            let fallback_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: ctx.params.clone(),
                bindings: ctx.bindings.clone(),
                system_name: &ctx.system_name,
                entity_param_types: &ctx.entity_param_types,
                store_param_types: &ctx.store_param_types,
            };
            try_encode_slot_expr(&fallback_ctx, expr, step)
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = try_encode_guard_value(pool, vctx, ctx, left, step)?;
            let r = try_encode_guard_value(pool, vctx, ctx, right, step)?;
            Ok(smt::binop(op, &l, &r)?)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = try_encode_guard_value(pool, vctx, ctx, operand, step)?;
            Ok(smt::unop(op, &v)?)
        }
        IRExpr::Prime { expr, .. } => try_encode_guard_value(pool, vctx, ctx, expr, step + 1),
        // Fallback: delegate to encode_slot_expr which handles App, Field
        // on entity params, and other complex expression forms.
        other => {
            let fallback_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: ctx.params.clone(),
                bindings: ctx.bindings.clone(),
                system_name: &ctx.system_name,
                entity_param_types: &ctx.entity_param_types,
                store_param_types: &ctx.store_param_types,
            };
            try_encode_slot_expr(&fallback_ctx, other, step)
        }
    }
}

/// Encode a system event as a single transition step.
///
/// Processes the event guard, then each `IRAction` in the event body:
/// - `Choose` — existential over active slots matching filter, with per-slot framing
/// - `ForAll` — conjunction over all active slots
/// - `Apply` — resolve entity and action, encode with per-slot framing
/// - `Create` — delegate to `encode_create`
/// - `CrossCall` — resolve target system event and encode inline
/// - `ExprStmt` — encode as boolean constraint
///
/// Frames all entity slots NOT touched by the event.
#[allow(clippy::too_many_lines)]
pub fn encode_step(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
) -> Bool {
    try_encode_step(pool, vctx, entities, all_systems, event, step)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_lines)]
pub fn try_encode_step(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
) -> Result<Bool, String> {
    let (formula, touched) =
        try_encode_step_inner(pool, vctx, entities, all_systems, event, step, 0, None)?;
    Ok(apply_global_frame(pool, entities, &touched, step, formula))
}

/// Encode an event with specific parameter values (for scene checking).
///
/// Scene events supply concrete argument values (resolved from given bindings)
/// rather than fresh unconstrained Z3 variables.
#[allow(clippy::implicit_hasher)]
pub fn encode_step_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Bool {
    let (formula, touched) = encode_step_inner(
        pool,
        vctx,
        entities,
        all_systems,
        event,
        step,
        0,
        Some(params),
    );
    apply_global_frame(pool, entities, &touched, step, formula)
}

/// Apply global frame for untouched slots to an event formula.
/// Called once at the top level — never inside recursive `CrossCall` encoding.
pub(crate) fn apply_global_frame(
    pool: &SlotPool,
    entities: &[IREntity],
    touched: &HashSet<(String, usize)>,
    step: usize,
    formula: Bool,
) -> Bool {
    let frame = frame_untouched_slots(pool, entities, touched, step);
    let mut all = vec![formula];
    all.extend(frame);
    let refs: Vec<&Bool> = all.iter().collect();
    smt::bool_and(&refs)
}

/// Encode a non-Apply nested action within the bound context of a Choose or
/// `ForAll` iteration. The bound variable's fields at the given slot are made
/// available via params so nested expressions can reference them (e.g., `o.id`
/// inside `choose o: Order { create Receipt { order_id = o.id } }`).
///
/// Returns `(formulas, additional_touched)` where formulas should be conjoined
/// with the current slot's constraints and `additional_touched` contains entity
/// slots that were modified by the nested action (for global frame tracking).
#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
fn encode_nested_op(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    op: &IRAction,
    bound_var: &str,
    bound_ent_name: &str,
    bound_entity_ir: &IREntity,
    bound_slot: usize,
    step: usize,
    base_params: &HashMap<String, SmtValue>,
    depth: usize,
    // Chain of outer bound variables from enclosing Choose/ForAll scopes.
    // Each entry is (var_name, entity_name, entity_ir, slot).
    // Enables Apply targeting an outer variable to resolve to its specific slot
    // instead of a disjunction over all slots.
    outer_bindings: &[(&str, &str, &IREntity, usize)],
) -> (Vec<Bool>, HashSet<(String, usize)>) {
    try_encode_nested_op(
        pool,
        vctx,
        entities,
        all_systems,
        op,
        bound_var,
        bound_ent_name,
        bound_entity_ir,
        bound_slot,
        step,
        base_params,
        depth,
        outer_bindings,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn try_encode_nested_op(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    op: &IRAction,
    bound_var: &str,
    bound_ent_name: &str,
    bound_entity_ir: &IREntity,
    bound_slot: usize,
    step: usize,
    base_params: &HashMap<String, SmtValue>,
    depth: usize,
    outer_bindings: &[(&str, &str, &IREntity, usize)],
) -> Result<(Vec<Bool>, HashSet<(String, usize)>), String> {
    let mut formulas = Vec::new();
    let mut additional_touched: HashSet<(String, usize)> = HashSet::new();

    // Build params that include the bound variable's field mappings for this slot.
    // This allows nested expressions to resolve `bound_var.field` references.
    let mut slot_params = base_params.clone();
    for field in &bound_entity_ir.fields {
        if let Some(val) = pool.field_at(bound_ent_name, bound_slot, &field.name, step) {
            slot_params.insert(format!("{bound_var}.{}", field.name), val.clone());
        }
    }

    let empty_ept: HashMap<String, String> = HashMap::new();

    match op {
        IRAction::Create {
            entity: create_ent,
            fields,
        } => {
            let create_entity_ir = entities.iter().find(|e| e.name == *create_ent);
            let create_fields: Vec<(String, IRExpr)> = fields
                .iter()
                .map(|f| (f.name.clone(), f.value.clone()))
                .collect();
            let create_formula = try_encode_create(
                pool,
                vctx,
                create_ent,
                create_entity_ir,
                &create_fields,
                step,
                &slot_params,
            )?;
            formulas.push(create_formula);
            let n_slots = pool.slots_for(create_ent);
            for s in 0..n_slots {
                additional_touched.insert((create_ent.clone(), s));
            }
        }

        IRAction::CrossCall {
            system: target_system,
            command: command_name,
            args: cross_args,
        } => {
            if let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) {
                let matching_steps: Vec<_> = target_sys
                    .steps
                    .iter()
                    .filter(|s| s.name == *command_name)
                    .collect();
                if matching_steps.is_empty() {
                    // No matching steps — should have been caught by validation.
                } else {
                    // Collect (formula, touched) pairs per branch, then apply
                    // per-branch framing so each disjunct frames slots in the
                    // union that it didn't individually touch.
                    let mut branch_results: Vec<(Bool, HashSet<(String, usize)>)> = Vec::new();
                    for target_step in &matching_steps {
                        if target_step.params.len() == cross_args.len() {
                            let arg_ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: bound_ent_name,
                                slot: bound_slot,
                                params: slot_params.clone(),
                                bindings: HashMap::new(),
                                system_name: "",
                                entity_param_types: &empty_ept,
                                store_param_types: &empty_ept,
                            };
                            let mut cross_params: HashMap<String, SmtValue> = HashMap::new();
                            for (target_param, arg_expr) in
                                target_step.params.iter().zip(cross_args.iter())
                            {
                                let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
                                cross_params.insert(target_param.name.clone(), val);
                            }
                            let (cross_formula, cross_touched) = try_encode_step_inner(
                                pool,
                                vctx,
                                entities,
                                all_systems,
                                target_step,
                                step,
                                depth + 1,
                                Some(cross_params),
                            )?;
                            branch_results.push((cross_formula, cross_touched));
                        } else {
                            branch_results.push((smt::bool_const(false), HashSet::new()));
                        }
                    }
                    if !branch_results.is_empty() {
                        // Compute the union of all touched sets
                        let all_touched: HashSet<(String, usize)> = branch_results
                            .iter()
                            .flat_map(|(_, t)| t.iter().cloned())
                            .collect();
                        // Apply per-branch framing: each branch frames slots it didn't touch
                        let framed_disjuncts: Vec<Bool> = branch_results
                            .into_iter()
                            .map(|(formula, branch_touched)| {
                                let untouched_by_branch: HashSet<(String, usize)> =
                                    all_touched.difference(&branch_touched).cloned().collect();
                                if untouched_by_branch.is_empty() {
                                    formula
                                } else {
                                    let frame = frame_specific_slots(
                                        pool,
                                        entities,
                                        &untouched_by_branch,
                                        step,
                                    );
                                    let mut parts = vec![formula];
                                    parts.extend(frame);
                                    let refs: Vec<&Bool> = parts.iter().collect();
                                    smt::bool_and(&refs)
                                }
                            })
                            .collect();
                        let refs: Vec<&Bool> = framed_disjuncts.iter().collect();
                        formulas.push(smt::bool_or(&refs));
                        additional_touched.extend(all_touched);
                    }
                }
            }
        }

        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
            return Err(
                "macro-step let/match is not yet supported inside choose/for blocks".to_owned(),
            );
        }

        IRAction::ExprStmt { expr } => {
            let expr_ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: bound_ent_name,
                slot: bound_slot,
                params: slot_params,
                bindings: HashMap::new(),
                system_name: "",
                entity_param_types: &empty_ept,
                store_param_types: &empty_ept,
            };
            let val = try_encode_slot_expr(&expr_ctx, expr, step)?;
            formulas.push(val.to_bool()?);
        }

        IRAction::Choose {
            var: inner_var,
            entity: inner_ent,
            filter,
            ops: inner_ops,
        } => {
            let inner_n_slots = pool.slots_for(inner_ent);
            let inner_entity_ir = entities.iter().find(|e| e.name == *inner_ent);
            // Augment outer bindings with the current bound variable so that
            // deeper nested ops can resolve Apply targets to our specific slot.
            let mut inner_bindings = outer_bindings.to_vec();
            inner_bindings.push((bound_var, bound_ent_name, bound_entity_ir, bound_slot));
            let mut inner_slot_options = Vec::new();

            for inner_slot in 0..inner_n_slots {
                let inner_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: inner_ent,
                    slot: inner_slot,
                    params: slot_params.clone(),
                    bindings: HashMap::new(),
                    system_name: "",
                    entity_param_types: &empty_ept,
                    store_param_types: &empty_ept,
                };
                let mut inner_conjuncts = Vec::new();

                // Must be active
                if let Some(SmtValue::Bool(active)) = pool.active_at(inner_ent, inner_slot, step) {
                    inner_conjuncts.push(active.clone());
                }
                // Filter must hold
                let filt = try_encode_slot_expr(&inner_ctx, filter, step)?;
                inner_conjuncts.push(filt.to_bool()?);

                // Encode inner ops
                if let Some(inner_ent_ir) = inner_entity_ir {
                    let mut inner_slot_has_action = false;
                    for inner_op in inner_ops {
                        match inner_op {
                            IRAction::Apply {
                                target,
                                transition,
                                args,
                                refs: apply_refs,
                            } if target == inner_var => {
                                // Target matches inner bound var — encode on inner entity
                                if let Some(trans) = inner_ent_ir
                                    .transitions
                                    .iter()
                                    .find(|t| t.name == *transition)
                                {
                                    let action_params = try_build_apply_params(
                                        &inner_ctx, trans, args, apply_refs, step,
                                    )?;
                                    let action_formula = try_encode_action(
                                        pool,
                                        vctx,
                                        inner_ent_ir,
                                        trans,
                                        inner_slot,
                                        step,
                                        &action_params,
                                    )?;
                                    inner_conjuncts.push(action_formula);
                                    inner_slot_has_action = true;
                                }
                            }
                            _ => {
                                // Cross-entity Apply or other nested action —
                                // delegate to encode_nested_op which resolves the
                                // target to the correct entity and slot.
                                let (nested_f, nested_t) = try_encode_nested_op(
                                    pool,
                                    vctx,
                                    entities,
                                    all_systems,
                                    inner_op,
                                    inner_var,
                                    inner_ent,
                                    inner_ent_ir,
                                    inner_slot,
                                    step,
                                    &slot_params,
                                    depth,
                                    &inner_bindings,
                                )?;
                                inner_conjuncts.extend(nested_f);
                                additional_touched.extend(nested_t);
                            }
                        }
                    }

                    // If no op directly acted on the inner chosen slot, frame it
                    // so the solver cannot mutate it arbitrarily.
                    if !inner_slot_has_action {
                        for field in &inner_ent_ir.fields {
                            if let (Some(curr), Some(next)) = (
                                pool.field_at(inner_ent, inner_slot, &field.name, step),
                                pool.field_at(inner_ent, inner_slot, &field.name, step + 1),
                            ) {
                                inner_conjuncts.push(smt::smt_eq(curr, next)?);
                            }
                        }
                        if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
                            pool.active_at(inner_ent, inner_slot, step),
                            pool.active_at(inner_ent, inner_slot, step + 1),
                        ) {
                            inner_conjuncts.push(smt::bool_eq(act_next, act_curr));
                        }
                    }

                    // Frame other slots of inner entity
                    let slot_frame =
                        frame_entity_slots_except(pool, inner_ent_ir, inner_slot, step);
                    inner_conjuncts.extend(slot_frame);
                }

                let refs: Vec<&Bool> = inner_conjuncts.iter().collect();
                if !refs.is_empty() {
                    inner_slot_options.push(smt::bool_and(&refs));
                }
            }

            let refs: Vec<&Bool> = inner_slot_options.iter().collect();
            if !refs.is_empty() {
                formulas.push(smt::bool_or(&refs));
            }
            for s in 0..inner_n_slots {
                additional_touched.insert((inner_ent.clone(), s));
            }
        }

        IRAction::ForAll {
            var: inner_var,
            entity: inner_ent,
            ops: inner_ops,
        } => {
            let inner_n_slots = pool.slots_for(inner_ent);
            let inner_entity_ir = entities.iter().find(|e| e.name == *inner_ent);
            // Augment outer bindings with current bound variable
            let mut inner_bindings = outer_bindings.to_vec();
            inner_bindings.push((bound_var, bound_ent_name, bound_entity_ir, bound_slot));

            for inner_slot in 0..inner_n_slots {
                let inner_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: inner_ent,
                    slot: inner_slot,
                    params: slot_params.clone(),
                    bindings: HashMap::new(),
                    system_name: "",
                    entity_param_types: &empty_ept,
                    store_param_types: &empty_ept,
                };
                let mut op_conjuncts = Vec::new();

                if let Some(inner_ent_ir) = inner_entity_ir {
                    let mut inner_slot_has_action = false;
                    for inner_op in inner_ops {
                        match inner_op {
                            IRAction::Apply {
                                target,
                                transition,
                                args,
                                refs: apply_refs,
                            } if target == inner_var => {
                                // Target matches inner bound var — encode on inner entity
                                if let Some(trans) = inner_ent_ir
                                    .transitions
                                    .iter()
                                    .find(|t| t.name == *transition)
                                {
                                    let action_params = try_build_apply_params(
                                        &inner_ctx, trans, args, apply_refs, step,
                                    )?;
                                    let action_formula = try_encode_action(
                                        pool,
                                        vctx,
                                        inner_ent_ir,
                                        trans,
                                        inner_slot,
                                        step,
                                        &action_params,
                                    )?;
                                    op_conjuncts.push(action_formula);
                                    inner_slot_has_action = true;
                                }
                            }
                            _ => {
                                // Cross-entity Apply or other nested action
                                let (nested_f, nested_t) = try_encode_nested_op(
                                    pool,
                                    vctx,
                                    entities,
                                    all_systems,
                                    inner_op,
                                    inner_var,
                                    inner_ent,
                                    inner_ent_ir,
                                    inner_slot,
                                    step,
                                    &slot_params,
                                    depth,
                                    &inner_bindings,
                                )?;
                                op_conjuncts.extend(nested_f);
                                additional_touched.extend(nested_t);
                            }
                        }
                    }

                    // If no op directly acted on this slot, frame it so the
                    // solver cannot mutate the active entity's fields.
                    if !inner_slot_has_action {
                        for field in &inner_ent_ir.fields {
                            if let (Some(curr), Some(next)) = (
                                pool.field_at(inner_ent, inner_slot, &field.name, step),
                                pool.field_at(inner_ent, inner_slot, &field.name, step + 1),
                            ) {
                                op_conjuncts.push(
                                    smt::smt_eq(curr, next)
                                        .expect("internal: nested forall slot frame smt_eq"),
                                );
                            }
                        }
                        if let (Some(SmtValue::Bool(act_curr)), Some(SmtValue::Bool(act_next))) = (
                            pool.active_at(inner_ent, inner_slot, step),
                            pool.active_at(inner_ent, inner_slot, step + 1),
                        ) {
                            op_conjuncts.push(smt::bool_eq(act_next, act_curr));
                        }
                    }
                }

                // For each slot: (active AND ops) OR (!active AND frame)
                if let Some(SmtValue::Bool(active)) = pool.active_at(inner_ent, inner_slot, step) {
                    let active_branch = if op_conjuncts.is_empty() {
                        active.clone()
                    } else {
                        let mut active_parts = vec![active.clone()];
                        active_parts.extend(op_conjuncts);
                        let refs: Vec<&Bool> = active_parts.iter().collect();
                        smt::bool_and(&refs)
                    };

                    let mut frame_parts = vec![smt::bool_not(active)];
                    if let Some(SmtValue::Bool(act_next)) =
                        pool.active_at(inner_ent, inner_slot, step + 1)
                    {
                        frame_parts.push(smt::bool_eq(act_next, active));
                    }
                    if let Some(inner_ent_ir) = inner_entity_ir {
                        for field in &inner_ent_ir.fields {
                            if let (Some(curr), Some(next)) = (
                                pool.field_at(inner_ent, inner_slot, &field.name, step),
                                pool.field_at(inner_ent, inner_slot, &field.name, step + 1),
                            ) {
                                frame_parts.push(
                                    smt::smt_eq(curr, next)
                                        .expect("internal: nested forall frame smt_eq"),
                                );
                            }
                        }
                    }

                    let frame_refs: Vec<&Bool> = frame_parts.iter().collect();
                    let inactive_branch = smt::bool_and(&frame_refs);
                    formulas.push(smt::bool_or(&[&active_branch, &inactive_branch]));
                }

                additional_touched.insert((inner_ent.clone(), inner_slot));
            }
        }

        IRAction::Apply {
            target,
            transition,
            args,
            refs: apply_refs,
        } => {
            // Resolve which entity and slot the Apply targets.
            // Priority: immediate bound var → outer bound var chain → entity name/transition fallback
            let resolved_binding: Option<(&str, &IREntity, usize)> = if target == bound_var {
                Some((bound_ent_name, bound_entity_ir, bound_slot))
            } else {
                outer_bindings
                    .iter()
                    .find(|(var, _, _, _)| *var == target.as_str())
                    .map(|(_, ent_name, ent_ir, slot)| (*ent_name, *ent_ir, *slot))
            };

            if let Some((ent_name, ent_ir, slot)) = resolved_binding {
                // Target is a bound variable (immediate or outer) — encode on
                // its specific slot, preserving the chosen slot identity.
                if let Some(trans) = ent_ir.transitions.iter().find(|t| t.name == *transition) {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: slot_params,
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
                    };
                    let action_params =
                        try_build_apply_params(&ctx, trans, args, apply_refs, step)?;
                    let action_formula =
                        try_encode_action(pool, vctx, ent_ir, trans, slot, step, &action_params)?;
                    formulas.push(action_formula);
                    additional_touched.insert((ent_name.to_string(), slot));
                }
            } else {
                // Apply targeting an unresolved variable — resolve by entity
                // name or transition name, encode with slot disjunction.
                let resolved = entities.iter().find(|e| e.name == *target).or_else(|| {
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
                if let Some(ent) = resolved {
                    let ent_name = &ent.name;
                    if let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) {
                        let n_slots = pool.slots_for(ent_name);
                        let mut slot_options = Vec::new();
                        for s in 0..n_slots {
                            let ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: ent_name,
                                slot: s,
                                params: slot_params.clone(),
                                bindings: HashMap::new(),
                                system_name: "",
                                entity_param_types: &empty_ept,
                                store_param_types: &empty_ept,
                            };
                            let action_params =
                                try_build_apply_params(&ctx, trans, args, apply_refs, step)?;
                            let mut slot_conjuncts = Vec::new();
                            let formula =
                                try_encode_action(pool, vctx, ent, trans, s, step, &action_params)?;
                            slot_conjuncts.push(formula);
                            let slot_frame = frame_entity_slots_except(pool, ent, s, step);
                            slot_conjuncts.extend(slot_frame);
                            let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                            slot_options.push(smt::bool_and(&refs));
                        }
                        let refs: Vec<&Bool> = slot_options.iter().collect();
                        if !refs.is_empty() {
                            formulas.push(smt::bool_or(&refs));
                        }
                        for s in 0..n_slots {
                            additional_touched.insert((ent_name.clone(), s));
                        }
                    }
                }
            }
        }
    }

    Ok((formulas, additional_touched))
}

/// Inner recursive implementation of `encode_step` with depth tracking
/// to prevent infinite loops from cyclic cross-system calls.
///
/// Returns `(action_formula, touched_slots)` — the formula describing the
/// event's effects WITHOUT global framing, plus the set of entity slots
/// modified by the event. Global framing is applied once by the top-level
/// caller (`encode_step` / `encode_step_with_params`), NOT inside
/// recursive `CrossCall` invocations.
///
/// `override_params` allows callers (e.g., `CrossCall`) to supply pre-built
/// Z3 values for the target event's parameters, wiring the caller's args
/// into the target event instead of creating fresh unconstrained variables.
#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(crate) fn encode_step_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> (Bool, HashSet<(String, usize)>) {
    try_encode_step_inner(
        pool,
        vctx,
        entities,
        all_systems,
        event,
        step,
        depth,
        override_params,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[derive(Clone)]
struct MacroBranch {
    formula: Bool,
    touched: HashSet<(String, usize)>,
    locals: HashMap<String, SmtValue>,
    return_value: Option<SmtValue>,
}

#[allow(clippy::too_many_arguments)]
fn contains_macro_actions(actions: &[IRAction]) -> bool {
    actions.iter().any(|action| match action {
        IRAction::LetCrossCall { .. } | IRAction::Match { .. } => true,
        IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => contains_macro_actions(ops),
        _ => false,
    })
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(crate) fn try_encode_step_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    if contains_macro_actions(&event.body) {
        try_encode_step_inner_macro(
            pool,
            vctx,
            entities,
            all_systems,
            event,
            step,
            depth,
            override_params,
        )
    } else {
        try_encode_step_inner_legacy(
            pool,
            vctx,
            entities,
            all_systems,
            event,
            step,
            depth,
            override_params,
        )
    }
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
pub(crate) fn try_encode_step_inner_legacy(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    assert!(
        depth <= 10,
        "CrossCall recursion depth exceeded (depth {depth}) — possible cyclic cross-system calls"
    );
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut conjuncts = Vec::new();
    // Track which entity types have ALL their slots handled internally
    // (Choose/ForAll/bare Apply do their own per-slot framing).
    let mut touched: HashSet<(String, usize)> = HashSet::new();
    // Counter for unique chain instance IDs (prevents aliasing when
    // multiple Choose blocks reuse the same var name in one step).
    let mut chain_id: usize = 0;

    // Build event parameter Z3 variables once per step, share across all contexts.
    // If override_params is provided (e.g., from CrossCall), use those instead
    // so that the caller's argument values are wired into this event.
    let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));

    // build entity param type info for the guard/body encoders.
    // Maps entity-typed param names to their entity type so that
    // Field(Var("item"), "status") can resolve at any step by looking up
    // the param's entity slot in the pool.
    let entity_param_types: HashMap<String, String> = event
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();

    // derive the owning system for system field and store parameter resolution.
    let owning_system = all_systems.iter().find(|s| {
        s.steps
            .iter()
            .any(|st| std::ptr::eq(st, event) || st.name == event.name)
    });
    let owning_system_name: String = owning_system.map(|s| s.name.clone()).unwrap_or_default();
    let store_param_types: HashMap<String, String> = owning_system
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        .unwrap_or_default();

    // Event guard encoding with support for quantifiers over entity slots.
    // For guards that are trivially `true`, skip encoding.
    // For non-trivial guards, use `encode_guard_expr` which handles:
    // - Quantifiers (`exists o: Order |...`, `forall o: Order |...`) by
    // expanding over active slots
    // - Boolean connectives by recursing
    // - Param-only or literal guards via `encode_slot_expr` with event params
    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        let guard = if owning_system_name.is_empty() {
            try_encode_guard_expr(
                pool,
                vctx,
                &event.guard,
                &step_params,
                &store_param_types,
                step,
            )
        } else {
            try_encode_guard_expr_for_system(
                pool,
                vctx,
                &event.guard,
                &step_params,
                step,
                &owning_system_name,
                &entity_param_types,
                &store_param_types,
            )
        }?;
        conjuncts.push(guard);
    }

    // Map Choose-bound variable names to their entity types for Apply target resolution.
    let mut var_to_entity: HashMap<String, String> = HashMap::new();

    // Populate var_to_entity from event params with entity types
    for p in &event.params {
        if let IRType::Entity { name } = &p.ty {
            var_to_entity.insert(p.name.clone(), name.clone());
        }
    }

    // Accumulated Choose variable params: after a `choose r: Reservation...`
    // is encoded, fresh Z3 variables for `r`'s fields are created and
    // constrained to match the chosen slot. Subsequent actions can then
    // reference `r.product_id` via these shared variables without requiring
    // a cross-product of slot assignments.
    let mut choose_var_params: HashMap<String, SmtValue> = HashMap::new();

    for action in &event.body {
        match action {
            // Per-slot framing in Choose.
            // Each disjunct includes framing for all OTHER slots of the same entity,
            // so non-selected slots cannot take arbitrary values.
            //
            // After encoding, creates shared Z3 variables for the Choose-bound
            // variable's entity fields, constrained to the chosen slot's values.
            // This enables subsequent Choose blocks to reference cross-entity
            // fields (e.g., `r.product_id`) efficiently.
            IRAction::Choose {
                var,
                entity: ent_name,
                filter,
                ops,
            } => {
                // Track var → entity mapping for Apply target resolution
                var_to_entity.insert(var.clone(), ent_name.clone());

                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let mut slot_options = Vec::new();

                // Merge event params with accumulated Choose variable params
                let mut merged_params = step_params.clone();
                merged_params.extend(choose_var_params.clone());
                let mut nested_touched: HashSet<(String, usize)> = HashSet::new();

                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: merged_params.clone(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &entity_param_types,
                        store_param_types: &store_param_types,
                    };

                    let mut slot_conjuncts = Vec::new();

                    // Must be active
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        slot_conjuncts.push(active.clone());
                    }

                    // Filter must hold
                    let filt = try_encode_slot_expr(&ctx, filter, step)?;
                    slot_conjuncts.push(filt.to_bool()?);

                    // Apply nested ops — detect multi-apply chains and use
                    // intermediate variables for sequential composition.
                    if let Some(ent) = entity_ir {
                        // Collect Apply ops targeting the Choose-bound entity
                        let same_entity_applies: Vec<_> = ops
                            .iter()
                            .filter_map(|op| {
                                if let IRAction::Apply {
                                    target,
                                    transition,
                                    args,
                                    refs: apply_refs,
                                } = op
                                {
                                    if target == var {
                                        return Some((transition, args, apply_refs));
                                    }
                                }
                                None
                            })
                            .collect();

                        if same_entity_applies.len() <= 1 {
                            // Single Apply — use standard encoding
                            for op in ops {
                                match op {
                                    IRAction::Apply {
                                        transition,
                                        args,
                                        refs: apply_refs,
                                        ..
                                    } => {
                                        if let Some(trans) =
                                            ent.transitions.iter().find(|t| t.name == *transition)
                                        {
                                            let action_params = try_build_apply_params(
                                                &ctx, trans, args, apply_refs, step,
                                            )?;
                                            let action_formula = try_encode_action(
                                                pool,
                                                vctx,
                                                ent,
                                                trans,
                                                slot,
                                                step,
                                                &action_params,
                                            )?;
                                            slot_conjuncts.push(action_formula);
                                        }
                                    }
                                    _ => {
                                        if let Some(ent) = entity_ir {
                                            let (nested_f, nested_t) = try_encode_nested_op(
                                                pool,
                                                vctx,
                                                entities,
                                                all_systems,
                                                op,
                                                var,
                                                ent_name,
                                                ent,
                                                slot,
                                                step,
                                                &merged_params,
                                                depth,
                                                &[],
                                            )?;
                                            slot_conjuncts.extend(nested_f);
                                            nested_touched.extend(nested_t);
                                        }
                                    }
                                }
                            }
                        } else {
                            // Multi-apply chain — create intermediate variables.
                            // Chain: step_k → inter_0 → inter_1 →... → step_k+1
                            let n_applies = same_entity_applies.len();

                            // Build variable maps for each stage
                            // Stage 0 reads: step k fields
                            // Stage i writes: intermediate_i (or step k+1 if last)
                            let read_step_k: HashMap<String, SmtValue> = ent
                                .fields
                                .iter()
                                .filter_map(|f| {
                                    pool.field_at(ent_name, slot, &f.name, step)
                                        .map(|v| (f.name.clone(), v.clone()))
                                })
                                .collect();

                            let write_step_k1: HashMap<String, SmtValue> = ent
                                .fields
                                .iter()
                                .filter_map(|f| {
                                    pool.field_at(ent_name, slot, &f.name, step + 1)
                                        .map(|v| (f.name.clone(), v.clone()))
                                })
                                .collect();

                            // Create N-1 intermediate variable maps
                            let intermediates: Vec<HashMap<String, SmtValue>> = (0..n_applies - 1)
                                .map(|i| {
                                    ent.fields
                                        .iter()
                                        .map(|f| {
 // Fully scoped: entity, slot, field, step,
 // chain instance ID, and stage index.
 // Prevents aliasing across steps, events,
 // and multiple Choose blocks with same var name.
                                            let name = format!(
                                                "{}_s{}_{}_t{step}_ch{chain_id}_inter{i}",
                                                ent_name, slot, f.name
                                            );
                                            let var = match &f.ty {
                                                IRType::Bool => smt::bool_var(&name),
                                                IRType::Real | IRType::Float => {
                                                    smt::real_var(&name)
                                                }
                                                IRType::Map { .. } | IRType::Set { .. } => {
                                                    smt::array_var(&name, &f.ty)
                                                        .expect("internal: array sort expected for Map/Set field")
                                                }
                                                IRType::Seq { element } => SmtValue::Dynamic(
                                                    smt::dynamic_const(
                                                        &name,
                                                        &smt::seq_sort(element).sort(),
                                                    ),
                                                ),
                                                _ => smt::int_var(&name),
                                            };
                                            (f.name.clone(), var)
                                        })
                                        .collect()
                                })
                                .collect();

                            for (i, (transition, args, apply_refs)) in
                                same_entity_applies.iter().enumerate()
                            {
                                let Some(trans) =
                                    ent.transitions.iter().find(|t| t.name == **transition)
                                else {
                                    continue;
                                };

                                // Read from: step k (first) or intermediate_{i-1}
                                let read_from = if i == 0 {
                                    &read_step_k
                                } else {
                                    &intermediates[i - 1]
                                };

                                // Build action params from the intermediate state.
                                // First Apply uses standard build_apply_params (step k).
                                // Later Applies evaluate args AND refs from intermediate vars.
                                let action_params = if i == 0 {
                                    try_build_apply_params(&ctx, trans, args, apply_refs, step)?
                                } else {
                                    let mut params = HashMap::new();
                                    // Positional params
                                    for (pi, param) in trans.params.iter().enumerate() {
                                        if let Some(arg_expr) = args.get(pi) {
                                            let val = try_eval_expr_with_vars(
                                                arg_expr,
                                                ent,
                                                read_from,
                                                vctx,
                                                &ctx.params,
                                            )?;
                                            params.insert(param.name.clone(), val);
                                        }
                                    }
                                    // Refs: resolve from intermediate vars
                                    for (ri, tref) in trans.refs.iter().enumerate() {
                                        if let Some(ref_name) = apply_refs.get(ri) {
                                            if let Some(val) = read_from.get(ref_name) {
                                                params.insert(tref.name.clone(), val.clone());
                                            }
                                        }
                                    }
                                    params
                                };

                                // Write to: intermediate_i (middle) or step k+1 (last)
                                let write_to = if i == n_applies - 1 {
                                    &write_step_k1
                                } else {
                                    &intermediates[i]
                                };

                                let formula = try_encode_action_with_vars(
                                    ent,
                                    trans,
                                    slot,
                                    read_from,
                                    write_to,
                                    vctx,
                                    &action_params,
                                )?;
                                slot_conjuncts.push(formula);
                            }

                            // Active flag: must be active at step k AND stays active at step k+1
                            // (matches single-apply semantics in encode_action)
                            if let (
                                Some(SmtValue::Bool(act_curr)),
                                Some(SmtValue::Bool(act_next)),
                            ) = (
                                pool.active_at(ent_name, slot, step),
                                pool.active_at(ent_name, slot, step + 1),
                            ) {
                                slot_conjuncts.push(act_curr.clone());
                                slot_conjuncts.push(act_next.clone());
                            }

                            // Handle non-Apply ops in the Choose (Create, CrossCall, etc.)
                            for op in ops {
                                match op {
                                    IRAction::Apply { target, .. } if target == var => {
                                        // Already handled above
                                    }
                                    IRAction::Apply { target, .. } => {
                                        // Apply targeting a different variable inside a Choose
                                        // is malformed IR — the Apply target should match
                                        // the Choose-bound variable.
                                        panic!(
                                            "Apply target {target} does not match Choose var {var} \
                                             — cross-target Apply in Choose is not supported"
                                        );
                                    }
                                    _ => {
                                        if let Some(ent) = entity_ir {
                                            let (nested_f, nested_t) = try_encode_nested_op(
                                                pool,
                                                vctx,
                                                entities,
                                                all_systems,
                                                op,
                                                var,
                                                ent_name,
                                                ent,
                                                slot,
                                                step,
                                                &merged_params,
                                                depth,
                                                &[],
                                            )?;
                                            slot_conjuncts.extend(nested_f);
                                            nested_touched.extend(nested_t);
                                        }
                                    }
                                }
                            }
                            chain_id += 1; // unique ID per multi-apply chain
                        }
                    }

                    // Constrain shared Choose variable fields to match this slot.
                    // For each field of the chosen entity, assert that the shared
                    // variable equals the slot's field at this step.
                    if let Some(ent) = entity_ir {
                        for field in &ent.fields {
                            let shared_name = format!("choose_{var}_{}_t{step}", field.name);
                            let shared_var = match &field.ty {
                                IRType::Bool => smt::bool_var(&shared_name),
                                IRType::Real | IRType::Float => smt::real_var(&shared_name),
                                _ => smt::int_var(&shared_name),
                            };
                            if let Some(slot_val) = pool.field_at(ent_name, slot, &field.name, step)
                            {
                                match (&shared_var, slot_val) {
                                    (SmtValue::Int(s), SmtValue::Int(f)) => {
                                        slot_conjuncts.push(smt::int_eq(s, f));
                                    }
                                    (SmtValue::Bool(s), SmtValue::Bool(f)) => {
                                        slot_conjuncts.push(smt::bool_eq(s, f));
                                    }
                                    (SmtValue::Real(s), SmtValue::Real(f)) => {
                                        slot_conjuncts.push(smt::real_eq(s, f));
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }

                    // Frame all OTHER slots of this entity within the disjunct.
                    if let Some(ent) = entity_ir {
                        let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
                        slot_conjuncts.extend(slot_frame);
                    }

                    let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                    if !refs.is_empty() {
                        slot_options.push(smt::bool_and(&refs));
                    }
                }

                // At least one slot must satisfy Choose
                let refs: Vec<&Bool> = slot_options.iter().collect();
                if !refs.is_empty() {
                    conjuncts.push(smt::bool_or(&refs));
                    for slot in 0..n_slots {
                        touched.insert((ent_name.clone(), slot));
                    }
                }
                // Mark entities touched by nested ops (Create, CrossCall, etc.)
                touched.extend(nested_touched);

                // Register shared Choose variable fields as params for
                // subsequent actions to resolve `var.field` references.
                if let Some(ent) = entity_ir {
                    for field in &ent.fields {
                        let shared_name = format!("choose_{var}_{}_t{step}", field.name);
                        let shared_var = match &field.ty {
                            IRType::Bool => smt::bool_var(&shared_name),
                            IRType::Real | IRType::Float => smt::real_var(&shared_name),
                            _ => smt::int_var(&shared_name),
                        };
                        // Register as `var.field` for Field resolution
                        choose_var_params
                            .insert(format!("{var}.{}", field.name), shared_var.clone());
                        // Also register as bare `field` if the var itself is referenced
                        // (some filters use bare field names from Choose context)
                    }
                }
            }

            // Bare Apply (top-level in event body).
            // Target may be a variable name (e.g., "o") or entity type name.
            // IR lowering stores the variable name from the source expression.
            // We try entity type first; if not found, it's a variable reference
            // that should have been scoped by an enclosing Choose (which is the
            // normal pattern — bare Apply without Choose is unusual).
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                // Resolve target: entity type name → Choose-bound variable → transition-based fallback
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    // Target is a variable name — check Choose bindings first
                    if let Some(entity_name) = var_to_entity.get(target.as_str()) {
                        return entities.iter().find(|e| e.name == *entity_name);
                    }
                    // Last resort: find entity with this transition (only if unambiguous)
                    let matches: Vec<_> = entities
                        .iter()
                        .filter(|e| e.transitions.iter().any(|t| t.name == *transition))
                        .collect();
                    if matches.len() == 1 {
                        Some(matches[0])
                    } else {
                        None // ambiguous or not found — skip
                    }
                });
                let Some(ent) = resolved_entity else {
                    panic!(
                        "Apply target resolution failed: target={target:?}, transition={transition:?} \
                         — could not resolve entity (var_to_entity keys: {:?}, entity names: {:?})",
                        var_to_entity.keys().collect::<Vec<_>>(),
                        entities.iter().map(|e| &e.name).collect::<Vec<_>>()
                    );
                };
                let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) else {
                    panic!(
                        "Apply transition not found: entity={}, transition={transition:?} \
                         — available transitions: {:?}",
                        ent.name,
                        ent.transitions.iter().map(|t| &t.name).collect::<Vec<_>>()
                    );
                };
                // Use resolved entity name, not the target variable name
                let ent_name = &ent.name;
                let n_slots = pool.slots_for(ent_name);

                // If `target` is an entity-typed event parameter, the per-step
                // `param_<target>_<step>` Z3 var represents the slot index the
                // event was called with. We tie each slot disjunct to that
                // value so the SAT solver picks a single slot per fire AND
                // so per-tuple fairness () can read the param var
                // to identify which tuple actually fired. Without this tie,
                // the param var is unconstrained relative to the body's slot
                // pick — `param_<target>_<step> == k` would not actually mean
                // "the event acted on slot k", and per-tuple obligations
                // would be decoupled from real slot mutations.
                let target_param_eq: Option<&SmtValue> = if event
                    .params
                    .iter()
                    .any(|p| p.name == *target && matches!(p.ty, IRType::Entity { .. }))
                {
                    step_params.get(target.as_str())
                } else {
                    None
                };

                let mut slot_options = Vec::new();
                for slot in 0..n_slots {
                    let apply_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: {
                            let mut p = step_params.clone();
                            p.extend(choose_var_params.clone());
                            p
                        },
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &entity_param_types,
                        store_param_types: &store_param_types,
                    };
                    let action_params =
                        try_build_apply_params(&apply_ctx, trans, args, apply_refs, step)?;
                    let mut slot_conjuncts = Vec::new();
                    let formula =
                        try_encode_action(pool, vctx, ent, trans, slot, step, &action_params)?;
                    slot_conjuncts.push(formula);
                    // Tie the param var to this slot index when applicable.
                    if let Some(param_val) = target_param_eq {
                        #[allow(clippy::cast_possible_wrap)]
                        let slot_val = smt::int_val(slot as i64);
                        if let Ok(eq) = smt::smt_eq(param_val, &slot_val) {
                            slot_conjuncts.push(eq);
                        }
                    }
                    // Frame all OTHER slots of this entity
                    let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
                    slot_conjuncts.extend(slot_frame);
                    let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                    slot_options.push(smt::bool_and(&refs));
                }
                let refs: Vec<&Bool> = slot_options.iter().collect();
                if !refs.is_empty() {
                    conjuncts.push(smt::bool_or(&refs));
                }
                // Mark all slots as touched — per-slot framing handled above
                for slot in 0..n_slots {
                    touched.insert((ent_name.clone(), slot));
                }
            }

            IRAction::Create {
                entity: ent_name,
                fields,
            } => {
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let create_fields: Vec<(String, IRExpr)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), f.value.clone()))
                    .collect();
                let create = try_encode_create(
                    pool,
                    vctx,
                    ent_name,
                    entity_ir,
                    &create_fields,
                    step,
                    &step_params,
                )?;
                conjuncts.push(create);
                // Mark all slots of this entity as potentially touched
                let n_slots = pool.slots_for(ent_name);
                for slot in 0..n_slots {
                    touched.insert((ent_name.clone(), slot));
                }
            }

            // Issue 2: ForAll encoding — conjunction over all active slots.
            // For each slot:
            // (active AND ops AND active_next) OR (!active AND frame_this_slot)
            // This ensures inactive slots are explicitly framed (not left unconstrained).
            IRAction::ForAll {
                var,
                entity: ent_name,
                ops,
            } => {
                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);
                let mut nested_touched: HashSet<(String, usize)> = HashSet::new();
                let forall_base_params = {
                    let mut p = step_params.clone();
                    p.extend(choose_var_params.clone());
                    p
                };

                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: forall_base_params.clone(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &entity_param_types,
                        store_param_types: &store_param_types,
                    };

                    let mut op_conjuncts = Vec::new();

                    for op in ops {
                        match op {
                            IRAction::Apply {
                                target: _,
                                transition,
                                args,
                                refs: apply_refs,
                            } => {
                                if let Some(ent) = entity_ir {
                                    if let Some(trans) =
                                        ent.transitions.iter().find(|t| t.name == *transition)
                                    {
                                        let action_params = try_build_apply_params(
                                            &ctx, trans, args, apply_refs, step,
                                        )?;
                                        let action_formula = try_encode_action(
                                            pool,
                                            vctx,
                                            ent,
                                            trans,
                                            slot,
                                            step,
                                            &action_params,
                                        )?;
                                        op_conjuncts.push(action_formula);
                                    }
                                }
                            }
                            _ => {
                                if let Some(ent) = entity_ir {
                                    let (nested_f, nested_t) = try_encode_nested_op(
                                        pool,
                                        vctx,
                                        entities,
                                        all_systems,
                                        op,
                                        var,
                                        ent_name,
                                        ent,
                                        slot,
                                        step,
                                        &forall_base_params,
                                        depth,
                                        &[],
                                    )?;
                                    op_conjuncts.extend(nested_f);
                                    nested_touched.extend(nested_t);
                                }
                            }
                        }
                    }

                    // For each slot: (active AND ops) OR (!active AND frame)
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        // Active branch: active AND ops
                        let active_branch = if op_conjuncts.is_empty() {
                            active.clone()
                        } else {
                            let mut active_parts = vec![active.clone()];
                            active_parts.extend(op_conjuncts);
                            let refs: Vec<&Bool> = active_parts.iter().collect();
                            smt::bool_and(&refs)
                        };

                        // Inactive branch: !active AND frame (all fields + active flag unchanged)
                        let mut frame_parts = vec![smt::bool_not(active)];
                        // Active flag unchanged
                        if let Some(SmtValue::Bool(act_next)) =
                            pool.active_at(ent_name, slot, step + 1)
                        {
                            frame_parts.push(smt::bool_eq(act_next, active));
                        }
                        // All fields unchanged
                        if let Some(ent) = entity_ir {
                            for field in &ent.fields {
                                if let (Some(curr), Some(next)) = (
                                    pool.field_at(ent_name, slot, &field.name, step),
                                    pool.field_at(ent_name, slot, &field.name, step + 1),
                                ) {
                                    frame_parts.push(
                                        smt::smt_eq(curr, next)
                                            .expect("internal: forall frame smt_eq"),
                                    );
                                }
                            }
                        }

                        let frame_refs: Vec<&Bool> = frame_parts.iter().collect();
                        let inactive_branch = smt::bool_and(&frame_refs);

                        conjuncts.push(smt::bool_or(&[&active_branch, &inactive_branch]));
                    }

                    touched.insert((ent_name.clone(), slot));
                }
                // Mark entities touched by nested ops (Create, CrossCall, etc.)
                touched.extend(nested_touched);
            }

            IRAction::CrossCall {
                system: target_system,
                command: command_name,
                args: cross_args,
            } => {
                // Find the target system and ALL matching steps, then encode
                // a disjunction with per-branch framing. Multi-clause commands
                // have multiple steps with the same name but different guards;
                // each branch may touch different slots, so each disjunct must
                // frame the slots in the union that it didn't individually touch.
                if let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) {
                    let matching_steps: Vec<_> = target_sys
                        .steps
                        .iter()
                        .filter(|s| s.name == *command_name)
                        .collect();
                    // Collect (formula, touched) pairs per branch
                    let mut branch_results: Vec<(Bool, HashSet<(String, usize)>)> = Vec::new();
                    for target_step in &matching_steps {
                        if target_step.params.len() != cross_args.len() {
                            // Arity mismatches are validated in scene checking,
                            // but keep harness encoding total so verify checks
                            // never panic during recursive CrossCall expansion.
                            branch_results.push((smt::bool_const(false), HashSet::new()));
                            continue;
                        }
                        // Build override params: evaluate each CrossCall arg in
                        // the current step's context (using step_params) and
                        // bind it to the corresponding target step param name.
                        let mut cross_params: HashMap<String, SmtValue> = HashMap::new();
                        let arg_ctx = SlotEncodeCtx {
                            pool,
                            vctx,
                            entity: "",
                            slot: 0,
                            params: {
                                let mut p = step_params.clone();
                                p.extend(choose_var_params.clone());
                                p
                            },
                            bindings: HashMap::new(),
                            system_name: "",
                            entity_param_types: &entity_param_types,
                            store_param_types: &store_param_types,
                        };
                        for (target_param, arg_expr) in
                            target_step.params.iter().zip(cross_args.iter())
                        {
                            let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
                            cross_params.insert(target_param.name.clone(), val);
                        }

                        // Recursively encode the target step with wired params.
                        // The callee does NOT apply its own global frame, so
                        // per-branch framing is handled below.
                        let (cross_formula, cross_touched) = try_encode_step_inner(
                            pool,
                            vctx,
                            entities,
                            all_systems,
                            target_step,
                            step,
                            depth + 1,
                            Some(cross_params),
                        )?;
                        branch_results.push((cross_formula, cross_touched));
                    }
                    if !branch_results.is_empty() {
                        // Compute the union of all touched sets
                        let all_touched: HashSet<(String, usize)> = branch_results
                            .iter()
                            .flat_map(|(_, t)| t.iter().cloned())
                            .collect();
                        // Apply per-branch framing: each branch frames slots it didn't touch
                        let framed_disjuncts: Vec<Bool> = branch_results
                            .into_iter()
                            .map(|(formula, branch_touched)| {
                                let untouched_by_branch: HashSet<(String, usize)> =
                                    all_touched.difference(&branch_touched).cloned().collect();
                                if untouched_by_branch.is_empty() {
                                    formula
                                } else {
                                    let frame = frame_specific_slots(
                                        pool,
                                        entities,
                                        &untouched_by_branch,
                                        step,
                                    );
                                    let mut parts = vec![formula];
                                    parts.extend(frame);
                                    let refs: Vec<&Bool> = parts.iter().collect();
                                    smt::bool_and(&refs)
                                }
                            })
                            .collect();
                        let refs: Vec<&Bool> = framed_disjuncts.iter().collect();
                        conjuncts.push(smt::bool_or(&refs));
                        touched.extend(all_touched);
                    }
                }
            }

            IRAction::ExprStmt { expr } => {
                // Encode the expression and assert it as a boolean constraint
                let expr_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: "",
                    slot: 0,
                    params: {
                        let mut p = step_params.clone();
                        p.extend(choose_var_params.clone());
                        p
                    },
                    bindings: HashMap::new(),
                    system_name: &owning_system_name,
                    entity_param_types: &entity_param_types,
                    store_param_types: &store_param_types,
                };
                let val = try_encode_slot_expr(&expr_ctx, expr, step)?;
                conjuncts.push(val.to_bool()?);
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
                return Err("internal: macro-step actions reached legacy step encoder".to_owned());
            }
        }
    }

    // Return action formula + touched set. Global framing is applied by the
    // top-level caller, NOT here — this allows CrossCall to compose without
    // conflicting frame constraints.
    let formula = {
        let refs: Vec<&Bool> = conjuncts.iter().collect();
        if refs.is_empty() {
            smt::bool_const(true)
        } else {
            smt::bool_and(&refs)
        }
    };
    Ok((formula, touched))
}

#[allow(clippy::too_many_arguments)]
fn try_encode_step_inner_macro(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<(Bool, HashSet<(String, usize)>), String> {
    let branches = try_encode_step_branches_dispatch(
        pool,
        vctx,
        entities,
        all_systems,
        event,
        step,
        depth,
        override_params,
    )?;
    let all_touched: HashSet<(String, usize)> = branches
        .iter()
        .flat_map(|b| b.touched.iter().cloned())
        .collect();
    let disjuncts: Vec<Bool> = branches
        .into_iter()
        .map(|branch| {
            let untouched_by_branch: HashSet<(String, usize)> =
                all_touched.difference(&branch.touched).cloned().collect();
            if untouched_by_branch.is_empty() {
                branch.formula
            } else {
                let frame = frame_specific_slots(pool, entities, &untouched_by_branch, step);
                let mut parts = vec![branch.formula];
                parts.extend(frame);
                let refs: Vec<&Bool> = parts.iter().collect();
                smt::bool_and(&refs)
            }
        })
        .collect();
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Ok((
        if refs.is_empty() {
            smt::bool_const(false)
        } else {
            smt::bool_or(&refs)
        },
        all_touched,
    ))
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
fn try_encode_step_branches_dispatch(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> Result<Vec<MacroBranch>, String> {
    if !contains_macro_actions(&event.body) {
        let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
        let (formula, touched) = try_encode_step_inner_legacy(
            pool,
            vctx,
            entities,
            all_systems,
            event,
            step,
            depth,
            Some(step_params.clone()),
        )?;
        let (owning_system_name, entity_param_types, store_param_types) =
            step_scope_metadata(all_systems, event);
        let mut branch = MacroBranch {
            formula,
            touched,
            locals: HashMap::new(),
            return_value: None,
        };
        if let Some(ret) = &event.return_expr {
            let ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: step_params,
                bindings: HashMap::new(),
                system_name: &owning_system_name,
                entity_param_types: &entity_param_types,
                store_param_types: &store_param_types,
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
        return Ok(vec![branch]);
    }

    let step_params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
    let (owning_system_name, entity_param_types, store_param_types) =
        step_scope_metadata(all_systems, event);

    let mut initial_parts = Vec::new();
    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        initial_parts.push(try_encode_guard_expr_for_system(
            pool,
            vctx,
            &event.guard,
            &step_params,
            step,
            &owning_system_name,
            &entity_param_types,
            &store_param_types,
        )?);
    }
    let initial_formula = if initial_parts.is_empty() {
        smt::bool_const(true)
    } else {
        let refs: Vec<&Bool> = initial_parts.iter().collect();
        smt::bool_and(&refs)
    };

    let mut branches = vec![MacroBranch {
        formula: initial_formula,
        touched: HashSet::new(),
        locals: HashMap::new(),
        return_value: None,
    }];
    let var_to_entity: HashMap<String, String> = event
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();

    for action in &event.body {
        branches = try_apply_macro_action(
            pool,
            vctx,
            entities,
            all_systems,
            action,
            step,
            depth,
            &step_params,
            &owning_system_name,
            &entity_param_types,
            &store_param_types,
            &var_to_entity,
            branches,
        )?;
    }

    if let Some(ret) = &event.return_expr {
        for branch in &mut branches {
            let ctx = SlotEncodeCtx {
                pool,
                vctx,
                entity: "",
                slot: 0,
                params: merged_branch_params(&step_params, &branch.locals),
                bindings: HashMap::new(),
                system_name: &owning_system_name,
                entity_param_types: &entity_param_types,
                store_param_types: &store_param_types,
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

fn step_scope_metadata(
    all_systems: &[IRSystem],
    event: &IRStep,
) -> (String, HashMap<String, String>, HashMap<String, String>) {
    let owning_system = all_systems.iter().find(|s| {
        s.steps
            .iter()
            .any(|st| std::ptr::eq(st, event) || st.name == event.name)
    });
    let owning_system_name = owning_system.map(|s| s.name.clone()).unwrap_or_default();
    let entity_param_types: HashMap<String, String> = event
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            IRType::Entity { name } => Some((p.name.clone(), name.clone())),
            _ => None,
        })
        .collect();
    let store_param_types: HashMap<String, String> = owning_system
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        .unwrap_or_default();
    (owning_system_name, entity_param_types, store_param_types)
}

fn merged_branch_params(
    step_params: &HashMap<String, SmtValue>,
    locals: &HashMap<String, SmtValue>,
) -> HashMap<String, SmtValue> {
    let mut params = step_params.clone();
    params.extend(locals.clone());
    params
}

fn fresh_smt_value(prefix: &str, ty: &IRType) -> SmtValue {
    match ty {
        IRType::Bool => smt::bool_var(prefix),
        IRType::Real | IRType::Float => smt::real_var(prefix),
        IRType::Int | IRType::Identity => smt::int_var(prefix),
        _ => super::walkers::dynamic_to_smt_value(smt::dynamic_fresh(
            prefix,
            &smt::ir_type_to_sort(ty),
        )),
    }
}

fn try_encode_macro_value_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<(SmtValue, Vec<Bool>), String> {
    match expr {
        IRExpr::Choose {
            var, predicate, ty, ..
        } => {
            let fresh = fresh_smt_value(&format!("choose_{var}_t{step}"), ty);
            let mut constraints = Vec::new();
            if let Some(pred) = predicate {
                let mut pred_params = ctx.params.clone();
                pred_params.insert(var.clone(), fresh.clone());
                let pred_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: pred_params,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                constraints.push(try_encode_slot_expr(&pred_ctx, pred, step)?.to_bool()?);
            }
            Ok((fresh, constraints))
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut params = ctx.params.clone();
            let mut constraints = Vec::new();
            for binding in bindings {
                let bind_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: params.clone(),
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                let (value, cs) = try_encode_macro_value_expr(&bind_ctx, &binding.expr, step)?;
                constraints.extend(cs);
                params.insert(binding.name.clone(), value);
            }
            let body_ctx = SlotEncodeCtx {
                pool: ctx.pool,
                vctx: ctx.vctx,
                entity: ctx.entity,
                slot: ctx.slot,
                params,
                bindings: ctx.bindings.clone(),
                system_name: ctx.system_name,
                entity_param_types: ctx.entity_param_types,
                store_param_types: ctx.store_param_types,
            };
            let (value, mut body_constraints) = try_encode_macro_value_expr(&body_ctx, body, step)?;
            constraints.append(&mut body_constraints);
            Ok((value, constraints))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_bool = try_encode_slot_expr(ctx, cond, step)?.to_bool()?;
            let (then_val, then_constraints) = try_encode_macro_value_expr(ctx, then_body, step)?;
            let else_expr = else_body
                .as_ref()
                .ok_or_else(|| "macro-step return if/else requires an else branch".to_owned())?;
            let (else_val, else_constraints) = try_encode_macro_value_expr(ctx, else_expr, step)?;
            let result = smt::smt_ite(&cond_bool, &then_val, &else_val);
            let mut constraints = Vec::new();
            for c in then_constraints {
                constraints.push(smt::bool_implies(&cond_bool, &c));
            }
            let not_cond = smt::bool_not(&cond_bool);
            for c in else_constraints {
                constraints.push(smt::bool_implies(&not_cond, &c));
            }
            Ok((result, constraints))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let (scrut, mut constraints) = try_encode_macro_value_expr(ctx, scrutinee, step)?;
            let mut arm_conds = Vec::new();
            let mut result: Option<SmtValue> = None;
            for arm in arms.iter().rev() {
                let mut arm_env = ctx.params.clone();
                super::encode::bind_pattern_vars(&arm.pattern, &scrut, &mut arm_env, ctx.vctx)?;
                let arm_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params: arm_env,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: ctx.entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                let mut arm_cond = super::encode::encode_pattern_cond(
                    &scrut,
                    &arm.pattern,
                    &HashMap::new(),
                    ctx.vctx,
                )?;
                if let Some(guard) = &arm.guard {
                    let guard_bool = try_encode_slot_expr(&arm_ctx, guard, step)?.to_bool()?;
                    arm_cond = smt::bool_and(&[&arm_cond, &guard_bool]);
                }
                arm_conds.push(arm_cond.clone());
                let (arm_val, arm_constraints) =
                    try_encode_macro_value_expr(&arm_ctx, &arm.body, step)?;
                if let Some(current) = result.take() {
                    result = Some(smt::smt_ite(&arm_cond, &arm_val, &current));
                } else {
                    result = Some(arm_val);
                }
                for c in arm_constraints {
                    constraints.push(smt::bool_implies(&arm_cond, &c));
                }
            }
            if arm_conds.is_empty() {
                return Err("macro-step return match has no arms".to_owned());
            }
            let cond_refs: Vec<&Bool> = arm_conds.iter().collect();
            constraints.push(smt::bool_or(&cond_refs));
            Ok((result.expect("non-empty arms"), constraints))
        }
        _ => Ok((try_encode_slot_expr(ctx, expr, step)?, Vec::new())),
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn try_apply_macro_action(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    action: &IRAction,
    step: usize,
    depth: usize,
    step_params: &HashMap<String, SmtValue>,
    owning_system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
    var_to_entity: &HashMap<String, String>,
    branches: Vec<MacroBranch>,
) -> Result<Vec<MacroBranch>, String> {
    let mut next = Vec::new();
    for branch in branches {
        let params = merged_branch_params(step_params, &branch.locals);
        match action {
            IRAction::Choose {
                var,
                entity,
                filter,
                ops,
            } => {
                let n_slots = pool.slots_for(entity);
                let entity_ir = entities.iter().find(|e| e.name == *entity);
                let mut choose_branches = Vec::new();
                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: owning_system_name,
                        entity_param_types,
                        store_param_types,
                    };
                    let mut conjuncts = vec![branch.formula.clone()];
                    if let Some(SmtValue::Bool(active)) = pool.active_at(entity, slot, step) {
                        conjuncts.push(active.clone());
                    }
                    conjuncts.push(try_encode_slot_expr(&ctx, filter, step)?.to_bool()?);

                    let mut touched = branch.touched.clone();
                    let mut slot_has_action = false;
                    let mut nested_touched = HashSet::new();

                    if let Some(ent_ir) = entity_ir {
                        for op in ops {
                            match op {
                                IRAction::Apply {
                                    target,
                                    transition,
                                    args,
                                    refs: apply_refs,
                                } if target == var => {
                                    if let Some(trans) =
                                        ent_ir.transitions.iter().find(|t| t.name == *transition)
                                    {
                                        let action_params = try_build_apply_params(
                                            &ctx, trans, args, apply_refs, step,
                                        )?;
                                        conjuncts.push(try_encode_action(
                                            pool,
                                            vctx,
                                            ent_ir,
                                            trans,
                                            slot,
                                            step,
                                            &action_params,
                                        )?);
                                        slot_has_action = true;
                                        touched.insert((entity.clone(), slot));
                                    }
                                }
                                _ => {
                                    let (nested_f, nested_slots) = try_encode_nested_op(
                                        pool,
                                        vctx,
                                        entities,
                                        all_systems,
                                        op,
                                        var,
                                        entity,
                                        ent_ir,
                                        slot,
                                        step,
                                        &params,
                                        depth,
                                        &[],
                                    )?;
                                    conjuncts.extend(nested_f);
                                    nested_touched.extend(nested_slots);
                                }
                            }
                        }

                        if !slot_has_action {
                            for field in &ent_ir.fields {
                                if let (Some(curr), Some(next_val)) = (
                                    pool.field_at(entity, slot, &field.name, step),
                                    pool.field_at(entity, slot, &field.name, step + 1),
                                ) {
                                    conjuncts.push(smt::smt_eq(curr, next_val)?);
                                }
                            }
                            if let (
                                Some(SmtValue::Bool(act_curr)),
                                Some(SmtValue::Bool(act_next)),
                            ) = (
                                pool.active_at(entity, slot, step),
                                pool.active_at(entity, slot, step + 1),
                            ) {
                                conjuncts.push(smt::bool_eq(act_next, act_curr));
                            }
                        }

                        conjuncts.extend(frame_entity_slots_except(pool, ent_ir, slot, step));
                    }

                    touched.extend(nested_touched);
                    for s in 0..n_slots {
                        touched.insert((entity.clone(), s));
                    }
                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    choose_branches.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals: branch.locals.clone(),
                        return_value: branch.return_value.clone(),
                    });
                }
                next.extend(choose_branches);
                continue;
            }
            IRAction::ForAll { .. } => {
                return Err(
                    "macro-step commands do not yet support for blocks in command bodies"
                        .to_owned(),
                );
            }
            IRAction::Create { entity, fields } => {
                let entity_ir = entities.iter().find(|e| e.name == *entity);
                let create_fields: Vec<(String, IRExpr)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), f.value.clone()))
                    .collect();
                let create = try_encode_create(
                    pool,
                    vctx,
                    entity,
                    entity_ir,
                    &create_fields,
                    step,
                    &params,
                )?;
                let parts = [branch.formula.clone(), create];
                let refs: Vec<&Bool> = parts.iter().collect();
                let mut touched = branch.touched.clone();
                for slot in 0..pool.slots_for(entity) {
                    touched.insert((entity.clone(), slot));
                }
                next.push(MacroBranch {
                    formula: smt::bool_and(&refs),
                    touched,
                    locals: branch.locals.clone(),
                    return_value: branch.return_value.clone(),
                });
            }
            IRAction::ExprStmt { expr } => {
                let expr_ctx = SlotEncodeCtx {
                    pool,
                    vctx,
                    entity: "",
                    slot: 0,
                    params,
                    bindings: HashMap::new(),
                    system_name: owning_system_name,
                    entity_param_types,
                    store_param_types,
                };
                let expr_bool = try_encode_slot_expr(&expr_ctx, expr, step)?.to_bool()?;
                let parts = [branch.formula.clone(), expr_bool];
                let refs: Vec<&Bool> = parts.iter().collect();
                next.push(MacroBranch {
                    formula: smt::bool_and(&refs),
                    touched: branch.touched.clone(),
                    locals: branch.locals.clone(),
                    return_value: branch.return_value.clone(),
                });
            }
            IRAction::Apply {
                target,
                transition,
                args,
                refs: apply_refs,
            } => {
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    if let Some(entity_name) = var_to_entity.get(target.as_str()) {
                        return entities.iter().find(|e| e.name == *entity_name);
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
                    return Err(format!(
                        "Apply target resolution failed in macro-step: target={target}, transition={transition}"
                    ));
                };
                let Some(trans) = ent.transitions.iter().find(|t| t.name == *transition) else {
                    return Err(format!(
                        "Apply transition not found in macro-step: entity={}, transition={transition}",
                        ent.name
                    ));
                };
                let ent_name = &ent.name;
                let target_param_eq: Option<&SmtValue> =
                    if event_param_is_entity(target, entity_param_types) {
                        params.get(target.as_str())
                    } else {
                        None
                    };
                for slot in 0..pool.slots_for(ent_name) {
                    let apply_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: owning_system_name,
                        entity_param_types,
                        store_param_types,
                    };
                    let action_params =
                        try_build_apply_params(&apply_ctx, trans, args, apply_refs, step)?;
                    let mut parts = vec![
                        branch.formula.clone(),
                        try_encode_action(pool, vctx, ent, trans, slot, step, &action_params)?,
                    ];
                    if let Some(param_val) = target_param_eq {
                        let slot_val = smt::int_val(slot as i64);
                        parts.push(smt::smt_eq(param_val, &slot_val)?);
                    }
                    let refs: Vec<&Bool> = parts.iter().collect();
                    let mut touched = branch.touched.clone();
                    for s in 0..pool.slots_for(ent_name) {
                        touched.insert((ent_name.clone(), s));
                    }
                    next.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals: branch.locals.clone(),
                        return_value: branch.return_value.clone(),
                    });
                }
            }
            IRAction::CrossCall {
                system,
                command,
                args,
            } => {
                let call_branches = try_encode_macro_call(
                    pool,
                    vctx,
                    entities,
                    all_systems,
                    system,
                    command,
                    args,
                    step,
                    depth,
                    &params,
                    owning_system_name,
                    entity_param_types,
                    store_param_types,
                )?;
                for call_branch in call_branches {
                    let mut touched = branch.touched.clone();
                    touched.extend(call_branch.touched);
                    let refs: Vec<&Bool> = [&branch.formula, &call_branch.formula]
                        .into_iter()
                        .collect();
                    next.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals: branch.locals.clone(),
                        return_value: branch.return_value.clone(),
                    });
                }
            }
            IRAction::LetCrossCall {
                name,
                system,
                command,
                args,
            } => {
                let call_branches = try_encode_macro_call(
                    pool,
                    vctx,
                    entities,
                    all_systems,
                    system,
                    command,
                    args,
                    step,
                    depth,
                    &params,
                    owning_system_name,
                    entity_param_types,
                    store_param_types,
                )?;
                for call_branch in call_branches {
                    let Some(value) = call_branch.return_value.clone() else {
                        return Err(format!(
                            "macro-step binding requires `{system}::{command}` to return a value"
                        ));
                    };
                    let mut touched = branch.touched.clone();
                    touched.extend(call_branch.touched);
                    let mut locals = branch.locals.clone();
                    locals.insert(name.clone(), value);
                    let refs: Vec<&Bool> = [&branch.formula, &call_branch.formula]
                        .into_iter()
                        .collect();
                    next.push(MacroBranch {
                        formula: smt::bool_and(&refs),
                        touched,
                        locals,
                        return_value: branch.return_value.clone(),
                    });
                }
            }
            IRAction::Match { scrutinee, arms } => {
                let call_branches = match scrutinee {
                    crate::ir::types::IRActionMatchScrutinee::Var { name } => vec![MacroBranch {
                        formula: smt::bool_const(true),
                        touched: HashSet::new(),
                        locals: {
                            let mut m = HashMap::new();
                            let Some(val) = branch.locals.get(name).cloned() else {
                                return Err(format!(
                                    "macro-step match references unknown local `{name}`"
                                ));
                            };
                            m.insert(name.clone(), val);
                            m
                        },
                        return_value: branch.locals.get(name).cloned(),
                    }],
                    crate::ir::types::IRActionMatchScrutinee::CrossCall {
                        system,
                        command,
                        args,
                    } => try_encode_macro_call(
                        pool,
                        vctx,
                        entities,
                        all_systems,
                        system,
                        command,
                        args,
                        step,
                        depth,
                        &params,
                        owning_system_name,
                        entity_param_types,
                        store_param_types,
                    )?,
                };
                for call_branch in call_branches {
                    let Some(scrut) = call_branch.return_value.clone() else {
                        return Err(
                            "macro-step match requires a returned command outcome".to_owned()
                        );
                    };
                    for arm in arms {
                        let mut arm_cond = super::encode::encode_pattern_cond(
                            &scrut,
                            &arm.pattern,
                            &HashMap::new(),
                            vctx,
                        )?;
                        let mut arm_locals = branch.locals.clone();
                        super::encode::bind_pattern_vars(
                            &arm.pattern,
                            &scrut,
                            &mut arm_locals,
                            vctx,
                        )?;
                        if let Some(guard) = &arm.guard {
                            let guard_ctx = SlotEncodeCtx {
                                pool,
                                vctx,
                                entity: "",
                                slot: 0,
                                params: merged_branch_params(&params, &arm_locals),
                                bindings: HashMap::new(),
                                system_name: owning_system_name,
                                entity_param_types,
                                store_param_types,
                            };
                            let guard_bool =
                                try_encode_slot_expr(&guard_ctx, guard, step)?.to_bool()?;
                            arm_cond = smt::bool_and(&[&arm_cond, &guard_bool]);
                        }
                        let arm_start = MacroBranch {
                            formula: {
                                let refs: Vec<&Bool> =
                                    [&branch.formula, &call_branch.formula, &arm_cond]
                                        .into_iter()
                                        .collect();
                                smt::bool_and(&refs)
                            },
                            touched: {
                                let mut touched = branch.touched.clone();
                                touched.extend(call_branch.touched.clone());
                                touched
                            },
                            locals: arm_locals,
                            return_value: branch.return_value.clone(),
                        };
                        let mut arm_branches = vec![arm_start];
                        for nested in &arm.body {
                            arm_branches = try_apply_macro_action(
                                pool,
                                vctx,
                                entities,
                                all_systems,
                                nested,
                                step,
                                depth,
                                step_params,
                                owning_system_name,
                                entity_param_types,
                                store_param_types,
                                var_to_entity,
                                arm_branches,
                            )?;
                        }
                        next.extend(arm_branches);
                    }
                }
            }
        }
    }
    Ok(next)
}

fn event_param_is_entity(target: &str, entity_param_types: &HashMap<String, String>) -> bool {
    entity_param_types.contains_key(target)
}

#[allow(clippy::too_many_arguments)]
fn try_encode_macro_call(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    target_system: &str,
    command_name: &str,
    cross_args: &[IRExpr],
    step: usize,
    depth: usize,
    params: &HashMap<String, SmtValue>,
    owning_system_name: &str,
    entity_param_types: &HashMap<String, String>,
    store_param_types: &HashMap<String, String>,
) -> Result<Vec<MacroBranch>, String> {
    let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) else {
        return Ok(vec![]);
    };
    let matching_steps: Vec<_> = target_sys
        .steps
        .iter()
        .filter(|s| s.name == *command_name)
        .collect();
    let arg_ctx = SlotEncodeCtx {
        pool,
        vctx,
        entity: "",
        slot: 0,
        params: params.clone(),
        bindings: HashMap::new(),
        system_name: owning_system_name,
        entity_param_types,
        store_param_types,
    };
    let mut branches = Vec::new();
    for target_step in &matching_steps {
        if target_step.params.len() != cross_args.len() {
            continue;
        }
        let mut cross_params = HashMap::new();
        for (target_param, arg_expr) in target_step.params.iter().zip(cross_args.iter()) {
            let val = try_encode_slot_expr(&arg_ctx, arg_expr, step)?;
            cross_params.insert(target_param.name.clone(), val);
        }
        branches.extend(try_encode_step_branches_dispatch(
            pool,
            vctx,
            entities,
            all_systems,
            target_step,
            step,
            depth + 1,
            Some(cross_params),
        )?);
    }
    Ok(branches)
}

// ── Transition relation ─────────────────────────────────────────────

/// Generate the full transition relation at a given step.
///
/// At each step, exactly one of the following happens:
/// - One of the system events fires (disjunction over all events)
/// - Stutter (idle — nothing changes), only if `assumption_set.stutter` is on
///
/// Returns: `event_1(step) OR event_2(step) OR... [OR stutter(step)]`
///
/// Stutter is **conditional** on the verification site's
/// `assume { stutter }` block.
/// The construct defaults are:
/// * `verify` → stutter off (closed-system, deadlock-detecting)
/// * `theorem`/`lemma` → stutter on (refinement-friendly, TLA+-style)
///   The caller passes the verification site's `IRAssumptionSet` so each
///   site sees the trace model it actually opted into.
pub fn transition_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    step: usize,
    assumption_set: &IRAssumptionSet,
) -> Bool {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut disjuncts = Vec::new();

    // Each system event is a possible transition
    for system in systems {
        for event in &system.steps {
            let event_formula = encode_step(pool, vctx, entities, systems, event, step);
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

    // Stutter: nothing changes. Only available when the verification
    // site opted into `assume { stutter }`.
    if assumption_set.stutter {
        let mut stutter_parts = vec![stutter_constraint(pool, entities, step)];
        // frame all system fields during stutter
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
    smt::bool_or(&refs)
}

fn system_field_name_sets(systems: &[IRSystem]) -> HashMap<String, HashSet<String>> {
    systems
        .iter()
        .filter(|s| !s.fields.is_empty())
        .map(|s| {
            let names: HashSet<String> = s.fields.iter().map(|f| f.name.clone()).collect();
            (s.name.clone(), names)
        })
        .collect()
}

fn system_field_frame_conjuncts(
    pool: &SlotPool,
    vctx: &VerifyContext,
    systems: &[IRSystem],
    owner: &IRSystem,
    body: &[IRAction],
    step: usize,
) -> Vec<Bool> {
    let system_field_sets = system_field_name_sets(systems);
    let mut sys_frames = Vec::new();
    if let Some(field_set) = system_field_sets.get(&owner.name) {
        let touched = extract_primed_system_fields(body, field_set);
        sys_frames.extend(frame_system_fields(pool, owner, &touched, step));
        sys_frames.extend(system_field_fsm_conjuncts(
            pool, vctx, owner, &touched, step,
        ));
    }
    for other_sys in systems {
        if other_sys.name != owner.name && !other_sys.fields.is_empty() {
            let empty = HashSet::new();
            sys_frames.extend(frame_system_fields(pool, other_sys, &empty, step));
        }
    }
    sys_frames
}

fn system_field_fsm_conjuncts(
    pool: &SlotPool,
    vctx: &VerifyContext,
    system: &IRSystem,
    touched_fields: &HashSet<String>,
    step: usize,
) -> Vec<Bool> {
    let mut conjuncts = Vec::new();
    for fsm in &system.fsm_decls {
        if !touched_fields.contains(&fsm.field) {
            continue;
        }
        let Some(old_val) = pool.system_field_at(&system.name, &fsm.field, step) else {
            continue;
        };
        let Some(new_val) = pool.system_field_at(&system.name, &fsm.field, step + 1) else {
            continue;
        };
        let mut allowed = Vec::new();
        if let Ok(eq) = smt::smt_eq(old_val, new_val) {
            allowed.push(eq);
        }
        for trans in &fsm.transitions {
            let from_id = match vctx.variants.try_id_of(&fsm.enum_name, &trans.from) {
                Ok(id) => id,
                Err(_) => continue,
            };
            let to_id = match vctx.variants.try_id_of(&fsm.enum_name, &trans.to) {
                Ok(id) => id,
                Err(_) => continue,
            };
            let from_val = smt::int_val(from_id);
            let to_val = smt::int_val(to_id);
            if let (Ok(pre_eq), Ok(post_eq)) = (
                smt::smt_eq(old_val, &from_val),
                smt::smt_eq(new_val, &to_val),
            ) {
                allowed.push(smt::bool_and(&[&pre_eq, &post_eq]));
            }
        }
        if !allowed.is_empty() {
            let refs: Vec<&Bool> = allowed.iter().collect();
            conjuncts.push(smt::bool_or(&refs));
        }
    }
    conjuncts
}

// ── Lasso BMC infrastructure ────────────────────────────────────────

/// Per-event fire tracking for lasso fairness.
///
/// Creates Boolean indicator variables for each event at each step,
/// plus stutter indicators. Asserts implications (fire → event formula)
/// and exactly-one constraints per step.
pub struct FireTracking {
    /// `(system_name, command_name)` → vec of Bool per step (command fire indicators)
    pub fire_vars: HashMap<(String, String), Vec<Bool>>,
    /// `(system_name, command_name, clause_index)` → vec of Bool per step
    /// (concrete step-clause fire indicators). This is the witness-facing
    /// clause provenance surface.
    pub clause_fire_vars: HashMap<(String, String, usize), Vec<Bool>>,
    /// Per-step stutter indicators
    pub stutter_vars: Vec<Bool>,
    /// All constraints to assert on the solver
    pub constraints: Vec<Bool>,
}

/// Build transition constraints with per-event fire tracking.
///
/// Like `transition_constraints` but instead of a monolithic disjunction,
/// creates individual fire variables for each event at each step. This
/// enables fairness constraints on the lasso loop.
///
/// Stutter is **conditional** on the verification site's
/// `assume { stutter }` block.
/// The caller passes the verification site's `IRAssumptionSet`; when
/// `assumption_set.stutter` is false, no stutter indicator is emitted and
/// the at-least-one disjunction reduces to "some event must fire". The
/// per-step exactly-one constraint then forces a real event at every
/// step, exposing deadlocks via UNSAT (direct deadlock detection in the
/// caller, not in this function).
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

    // Collect all unique (system, command) pairs.
    for system in systems {
        for (clause_idx, event) in system.steps.iter().enumerate() {
            let key = (system.name.clone(), event.name.clone());
            fire_vars.entry(key).or_default();
            clause_fire_vars
                .entry((system.name.clone(), event.name.clone(), clause_idx))
                .or_default();
        }
    }

    for step in 0..bound {
        // Create clause fire indicators for each step clause at this step.
        // These remain clause-scoped so the transition relation still chooses
        // exactly one concrete clause (or stutter), even when multiple clauses
        // implement the same command. We separately aggregate them into stable
        // command-level fire indicators for witness extraction and fairness.
        let mut step_indicators: Vec<Bool> = Vec::new();
        let mut command_clauses: HashMap<(String, String), Vec<Bool>> = HashMap::new();

        for system in systems {
            for (clause_idx, event) in system.steps.iter().enumerate() {
                let key = (system.name.clone(), event.name.clone());
                let clause_fire_var = smt::bool_var(&format!(
                    "fire_{}_{}_c{}_t{step}",
                    system.name, event.name, clause_idx
                ));
                let clause_fire_bool = clause_fire_var
                    .to_bool()
                    .expect("internal: clause fire var");

                // clause_fire → event_formula
                let event_formula = try_encode_step(pool, vctx, entities, systems, event, step)?;
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

        // Aggregate clause-level fire into one stable command-level indicator
        // per step. This is the witness/fairness-facing provenance surface.
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

        // Create stutter indicator only when stutter is opted in.
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

        // Exactly one fires at this step (at-least-one + at-most-one)
        let indicator_refs: Vec<&Bool> = step_indicators.iter().collect();
        constraints.push(smt::bool_or(&indicator_refs));
        // At-most-one via pairwise exclusion
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

/// Lasso loop-back variables and constraints.
pub struct LassoLoop {
    /// `loop_indicators[l]` is true iff the loop starts at step l.
    pub loop_indicators: Vec<Bool>,
    /// All constraints (exactly-one + conditional loop-back equalities).
    pub constraints: Vec<Bool>,
}

/// Create lasso loop-back constraints.
///
/// Creates Boolean indicators for each possible loop start l ∈ [0, bound-1].
/// (Not bound itself — a zero-length loop has no transitions and would allow
/// degenerate infinite stutter that violates fairness.)
/// For each l, asserts `loop_l → (state(bound) = state(l))`, meaning all
/// entity fields and active flags at the last step equal those at step l.
pub fn lasso_loopback(pool: &SlotPool, entities: &[IREntity], systems: &[IRSystem]) -> LassoLoop {
    let bound = pool.bound;
    let mut loop_indicators = Vec::new();
    let mut constraints = Vec::new();

    for l in 0..bound {
        let indicator = smt::bool_var(&format!("loop_l_{l}"));
        let indicator_bool = indicator.to_bool().expect("internal: loop indicator");

        // Loop-back: state(bound) = state(l)
        let mut equalities = Vec::new();
        for entity in entities {
            let n_slots = pool.slots_for(&entity.name);
            for slot in 0..n_slots {
                // Active flag equality
                if let (Some(SmtValue::Bool(at_bound)), Some(SmtValue::Bool(at_l))) = (
                    pool.active_at(&entity.name, slot, bound),
                    pool.active_at(&entity.name, slot, l),
                ) {
                    equalities.push(smt::bool_eq(at_bound, at_l));
                }
                // Field equalities
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
            // No state to equate — loop-back is trivially true
            loop_indicators.push(indicator_bool);
            continue;
        }

        let eq_refs: Vec<&Bool> = equalities.iter().collect();
        let loopback_eq = smt::bool_and(&eq_refs);
        constraints.push(smt::bool_implies(&indicator_bool, &loopback_eq));
        loop_indicators.push(indicator_bool);
    }

    // Exactly one loop start
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

/// Encode an event's full enabledness predicate at a given step.
///
/// An event is "enabled" (in the TLA+ ENABLED sense) if:
/// 1. Its guard (requires clause) holds at this step
/// 2. Its body can execute — for Choose, there exists an active entity
///    matching the filter; for Create, there exists an inactive slot
///
/// This is more precise than just checking the guard, which would
/// incorrectly consider events enabled even when no matching entity exists.
pub fn encode_step_enabled(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
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
    event: &IRStep,
    step: usize,
) -> Result<Bool, String> {
    try_encode_step_enabled_inner(pool, vctx, entities, systems, event, step, None, 0)
}

/// Like `encode_step_enabled` but with a caller-supplied parameter
/// overlay. Used by per-tuple fairness encoding () to ask
/// "is the event enabled WITH these specific param values?".
///
/// The overlay replaces the fresh per-step `param_*` Z3 vars that
/// `encode_step_enabled` would otherwise build. Concrete `SmtValue`s
/// in the overlay propagate into the guard / filter encoding.
#[allow(clippy::implicit_hasher)]
pub fn encode_step_enabled_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
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
    event: &IRStep,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Result<Bool, String> {
    try_encode_step_enabled_inner(pool, vctx, entities, systems, event, step, Some(params), 0)
}

#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
fn encode_step_enabled_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    override_params: Option<HashMap<String, SmtValue>>,
    depth: usize,
) -> Bool {
    try_encode_step_enabled_inner(
        pool,
        vctx,
        entities,
        systems,
        event,
        step,
        override_params,
        depth,
    )
    .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_arguments)]
fn try_encode_step_enabled_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    override_params: Option<HashMap<String, SmtValue>>,
    depth: usize,
) -> Result<Bool, String> {
    let empty_ept: HashMap<String, String> = HashMap::new();
    let mut conditions = Vec::new();

    let params = override_params.unwrap_or_else(|| build_step_params(&event.params, step));
    let store_param_types: HashMap<String, String> = systems
        .iter()
        .find(|s| {
            s.steps
                .iter()
                .any(|st| std::ptr::eq(st, event) || st.name == event.name)
        })
        .map(|s| {
            s.store_params
                .iter()
                .map(|p| (p.name.clone(), p.entity_type.clone()))
                .collect()
        })
        .unwrap_or_default();

    // Top-level guard (requires clause)
    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        conditions.push(try_encode_guard_expr(
            pool,
            vctx,
            &event.guard,
            &params,
            &store_param_types,
            step,
        )?);
    }

    // Body preconditions: check that Choose/Create can execute
    for action in &event.body {
        match action {
            IRAction::Choose {
                entity: ent_name,
                filter,
                ..
            } => {
                // Event is enabled only if ∃ active slot matching the filter
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
                                system_name: "",
                                entity_param_types: &empty_ept,
                                store_param_types: &empty_ept,
                            };
                            let filt = try_encode_slot_expr(&ctx, filter, step)?;
                            let filt_bool = filt.to_bool()?;
                            slot_disjuncts.push(smt::bool_and(&[active, &filt_bool]));
                        }
                    }
                }
                if slot_disjuncts.is_empty() {
                    // No slots at all → event is never enabled
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
                conditions.push(smt::bool_or(&refs));
            }
            IRAction::LetCrossCall { .. } | IRAction::Match { .. } => {
                return Err(
                    "macro-step let/match is not yet supported in step-enabled checks".to_owned(),
                );
            }
            IRAction::Create {
                entity: ent_name, ..
            } => {
                // Event is enabled only if ∃ inactive slot
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
                // Mirrors the target resolution in `encode_step_inner`'s
                // top-level Apply branch. The event is enabled only if some
                // active slot of the resolved entity satisfies the
                // transition's guard at this step. When the target is an
                // entity-typed event parameter (per-tuple case), the
                // candidate slot is constrained to equal the param value
                // — this matches the param-slot tie added to the body
                // encoding for the same Apply.
                //
                // Resolution order, mirroring `encode_step_inner`:
                // 1. Direct entity-name match (e.g. `Order::confirm()`).
                // 2. Entity-typed event param (e.g. `j: Job` → Job).
                // The body encoder uses `var_to_entity` for this;
                // since this branch only sees top-level Apply, the
                // only var bindings in scope come from event params.
                // 3. Last resort: unique-transition-name match.
                let resolved_entity = entities.iter().find(|e| e.name == *target).or_else(|| {
                    // Entity-typed event param → resolve via param's type
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
                    // Last resort: find an entity that has this transition.
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
                    // Cannot resolve target — be conservative and skip the
                    // body precondition. The action encoding will surface
                    // any issue when the body is encoded for real.
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

                    // Build the action's parameter map exactly as the body
                    // encoder does (positional args + refs), so the guard
                    // sees the same parameter bindings.
                    let slot_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: &ent.name,
                        slot,
                        params: params.clone(),
                        bindings: HashMap::new(),
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
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
                        system_name: "",
                        entity_param_types: &empty_ept,
                        store_param_types: &empty_ept,
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
            IRAction::ForAll { .. } => {
                // ForAll iterates over every active slot of the entity.
                // Zero-iteration (no active slots) is vacuously fine.
                // Nested Apply guards determine per-slot transition
                // outcomes but don't prevent the event from executing.
                // No enabledness condition needed.
            }
            IRAction::CrossCall {
                system: sys_name,
                command: cmd_name,
                args: cross_args,
            } => {
                // CrossCall invokes a command in another system. The
                // event is enabled only if the target command is enabled
                // with the actual cross-call arguments.
                // Depth limit prevents infinite recursion on cyclic calls.
                if depth < 5 {
                    if let Some(target_sys) = systems.iter().find(|s| s.name == *sys_name) {
                        let matching: Vec<&IRStep> = target_sys
                            .steps
                            .iter()
                            .filter(|s| s.name == *cmd_name)
                            .collect();
                        if !matching.is_empty() {
                            let empty_ept: HashMap<String, String> = HashMap::new();
                            let clause_bools: Vec<Bool> = matching
                                .iter()
                                .filter(|target_step| target_step.params.len() == cross_args.len())
                                .map(|target_step| {
                                    // Build cross_params from the source
                                    // arguments, mirroring the execution
                                    // path in encode_step_inner.
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
                                        Some(cross_params),
                                        depth + 1,
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
                // An expression statement constrains the next state.
                // If the constraint is unsatisfiable at this step, the
                // event cannot produce a valid successor state.
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

/// Build fairness constraints on a lasso loop.
///
/// Reads the verification site's `IRAssumptionSet` (populated by )
/// to decide which `(system, event)` pairs are weakly or strongly fair.
/// Events not present in `assumption_set.weak_fair` or `strong_fair` get
/// no fairness constraints (default = unfair, per ).
///
/// Supports both weak and strong fairness per event:
///
/// **Weak fairness** (TLA+ WF): if action A is enabled at EVERY step in
/// the loop, then A must fire at SOME step in the loop.
/// `loop_l → ( (∀ step∈[l,bound-1]. enabled(e,step)) → (∃ step∈[l,bound-1]. fire_e(step)) )`
///
/// **Strong fairness** (TLA+ SF): if action A is enabled at SOME step in
/// the loop, then A must fire at SOME step in the loop.
/// `loop_l → ( (∃ step∈[l,bound-1]. enabled(e,step)) → (∃ step∈[l,bound-1]. fire_e(step)) )`
///
/// Strong fairness is strictly stronger than weak: it constrains actions that
/// are even intermittently enabled, not just continuously enabled.
///
/// **Per-tuple fairness ().** For events listed in
/// `assumption_set.per_tuple` (i.e. parameterized fair events), the
/// obligation is split per parameter tuple over the entity slot space:
/// "for each tuple t, if event(t) is enabled in the loop, event must
/// fire with params=t in the loop." This catches starvation
/// counterexamples where one slot is never serviced even though the
/// per-event obligation is technically satisfied. Per-tuple expansion
/// is supported only when all event params are entity-typed; events
/// with non-entity params (Int/String/etc.) fall back to per-event.
pub fn fairness_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire: &FireTracking,
    lasso: &LassoLoop,
    assumption_set: &IRAssumptionSet,
) -> Vec<Bool> {
    try_fairness_constraints(pool, vctx, entities, systems, fire, lasso, assumption_set)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

pub fn try_fairness_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    fire: &FireTracking,
    lasso: &LassoLoop,
    assumption_set: &IRAssumptionSet,
) -> Result<Vec<Bool>, String> {
    let bound = pool.bound;
    let mut constraints = Vec::new();

    // Build O(1) lookup tables for fairness membership keyed by
    // (system, event). The assumption set is normalized in so
    // an event is in at most one of weak_fair / strong_fair.
    let weak_set: HashSet<(&str, &str)> = assumption_set
        .weak_fair
        .iter()
        .map(|r| (r.system.as_str(), r.command.as_str()))
        .collect();
    let strong_set: HashSet<(&str, &str)> = assumption_set
        .strong_fair
        .iter()
        .map(|r| (r.system.as_str(), r.command.as_str()))
        .collect();
    let per_tuple_set: HashSet<(&str, &str)> = assumption_set
        .per_tuple
        .iter()
        .map(|r| (r.system.as_str(), r.command.as_str()))
        .collect();

    for system in systems {
        for event in &system.steps {
            let pair = (system.name.as_str(), event.name.as_str());
            let is_strong = strong_set.contains(&pair);
            let is_fair = is_strong || weak_set.contains(&pair);
            if !is_fair {
                continue;
            }
            let key = (system.name.clone(), event.name.clone());
            let Some(fire_vec) = fire.fire_vars.get(&key) else {
                continue;
            };

            // per-tuple fairness for parameterized events.
            // We try per-tuple first. If all params are entity-typed,
            // expand into per-tuple obligations and skip the per-event
            // obligation (per-tuple is strictly stronger). Otherwise
            // fall through to per-event.
            let per_tuple_tuples = if per_tuple_set.contains(&pair) {
                enumerate_entity_param_tuples(event, pool)
            } else {
                None
            };

            if let Some(tuples) = per_tuple_tuples {
                for tuple in &tuples {
                    for l in 0..bound {
                        let loop_ind = &lasso.loop_indicators[l];

                        // Per-tuple enabledness at each step
                        let mut enabled_per_step = Vec::new();
                        for step in l..bound {
                            let enabled = try_encode_step_enabled_with_params(
                                pool,
                                vctx,
                                entities,
                                systems,
                                event,
                                step,
                                tuple.clone(),
                            )?;
                            enabled_per_step.push(enabled);
                        }
                        let enabled_condition = if is_strong {
                            let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                            smt::bool_or(&refs)
                        } else {
                            let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                            smt::bool_and(&refs)
                        };

                        // Per-tuple fired: at some step, fire_e is true AND
                        // its per-step params equal this tuple. The per-step
                        // `param_<name>_<step>` Z3 vars are shared with the
                        // body encoding, so constraining them to a tuple is
                        // equivalent to "fired with these args".
                        let mut fired_per_step = Vec::new();
                        for (step, fire_at_step) in fire_vec.iter().enumerate().take(bound).skip(l)
                        {
                            let step_params = build_step_params(&event.params, step);
                            let mut param_eqs = Vec::new();
                            for (name, target) in tuple {
                                if let Some(actual) = step_params.get(name) {
                                    if let Ok(eq) = smt::smt_eq(actual, target) {
                                        param_eqs.push(eq);
                                    }
                                }
                            }
                            let params_match = if param_eqs.is_empty() {
                                smt::bool_const(true)
                            } else {
                                let refs: Vec<&Bool> = param_eqs.iter().collect();
                                smt::bool_and(&refs)
                            };
                            fired_per_step.push(smt::bool_and(&[fire_at_step, &params_match]));
                        }
                        let fire_refs: Vec<&Bool> = fired_per_step.iter().collect();
                        let fires_somewhere = smt::bool_or(&fire_refs);

                        let fairness = smt::bool_implies(&enabled_condition, &fires_somewhere);
                        constraints.push(smt::bool_implies(loop_ind, &fairness));
                    }
                }
                continue; // per-tuple subsumes per-event for this event
            }

            // Per-event encoding (default for non-parameterized events,
            // or fallback for events with non-entity params).
            for l in 0..bound {
                let loop_ind = &lasso.loop_indicators[l];

                // Collect enabledness at each loop step
                let mut enabled_per_step = Vec::new();
                for step in l..bound {
                    let enabled =
                        try_encode_step_enabled(pool, vctx, entities, systems, event, step)?;
                    enabled_per_step.push(enabled);
                }

                let enabled_condition = if is_strong {
                    // Strong fairness: enabled at SOME step (disjunction)
                    let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                    smt::bool_or(&refs)
                } else {
                    // Weak fairness: enabled at EVERY step (conjunction)
                    let refs: Vec<&Bool> = enabled_per_step.iter().collect();
                    smt::bool_and(&refs)
                };

                // Fires somewhere in loop
                let fire_disj: Vec<_> = fire_vec[l..bound].to_vec();
                let fire_refs: Vec<&Bool> = fire_disj.iter().collect();
                let fires_somewhere = smt::bool_or(&fire_refs);

                // Fairness: enabled_condition → fires somewhere
                let fairness = smt::bool_implies(&enabled_condition, &fires_somewhere);
                constraints.push(smt::bool_implies(loop_ind, &fairness));
            }
        }
    }

    Ok(constraints)
}

/// Enumerate the per-tuple parameter domain for a fair event ().
///
/// Supported only when every parameter has an entity type — the slot
/// space for an entity is bounded (`pool.slots_for(name)`), so the
/// cartesian product is finite. Events with `Int`/`String`/etc. params
/// return `None`, signalling the caller to fall back to per-event
/// fairness. (Per-tuple semantics for unbounded parameter domains
/// requires k-liveness, deferred per.)
///
/// Each returned `HashMap` maps a param name to its slot-index Z3 value.
fn enumerate_entity_param_tuples(
    event: &IRStep,
    pool: &SlotPool,
) -> Option<Vec<HashMap<String, SmtValue>>> {
    // Collect (param_name, entity_name) for each entity-typed param.
    // Bail out if any param is non-entity.
    let mut entity_params: Vec<(&str, &str)> = Vec::new();
    for p in &event.params {
        match &p.ty {
            IRType::Entity { name } => entity_params.push((p.name.as_str(), name.as_str())),
            _ => return None,
        }
    }

    // Zero-param events shouldn't be in per_tuple (per ),
    // but be defensive: an empty param list means a single empty tuple.
    if entity_params.is_empty() {
        return Some(vec![HashMap::new()]);
    }

    // Cartesian product over slot indices for each entity-typed param.
    let mut tuples: Vec<HashMap<String, SmtValue>> = vec![HashMap::new()];
    for (param_name, ent_name) in &entity_params {
        let n_slots = pool.slots_for(ent_name);
        if n_slots == 0 {
            // No slots for this entity → no tuples → no per-tuple
            // obligations. Caller falls back to per-event (which will
            // also be vacuous for this event).
            return None;
        }
        let mut next_tuples = Vec::with_capacity(tuples.len() * n_slots);
        for tup in &tuples {
            for slot_idx in 0..n_slots {
                let mut new_tup = tup.clone();
                #[allow(clippy::cast_possible_wrap)]
                new_tup.insert((*param_name).to_string(), smt::int_val(slot_idx as i64));
                next_tuples.push(new_tup);
            }
        }
        tuples = next_tuples;
    }
    Some(tuples)
}

// ── Slot-scoped expression encoding ─────────────────────────────────

/// Encode an IR expression with a specific entity slot in scope.
///
/// Variable and field references resolve to `entity_s{slot}_{field}_t{step}`.
/// Parameters (from action/event signatures) are checked first, then slot fields.
#[allow(clippy::too_many_lines)]
pub fn encode_slot_expr(ctx: &SlotEncodeCtx<'_>, expr: &IRExpr, step: usize) -> SmtValue {
    try_encode_slot_expr(ctx, expr, step).unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_lines)]
pub fn try_encode_slot_expr(
    ctx: &SlotEncodeCtx<'_>,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Lit { value, .. } => Ok(encode_slot_literal(value)),

        IRExpr::Var { name, .. } => {
            // Check action/event parameters first
            if let Some(val) = ctx.params.get(name) {
                return Ok(val.clone());
            }
            // Bound entity variables may need their slot index directly,
            // e.g. for membership tests like `users[u]`.
            if let Some((_, slot)) = ctx.bindings.get(name.as_str()) {
                return Ok(smt::int_val(*slot as i64));
            }
            // Resolve to this slot's field variable
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, name, step) {
                return Ok(val.clone());
            }
            // Try cross-entity bindings (from prior Choose blocks)
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = ctx.pool.field_at(entity, *slot, name, step) {
                    return Ok(val.clone());
                }
            }
            // try system flat state field
            if !ctx.system_name.is_empty() {
                if let Some(val) = ctx.pool.system_field_at(ctx.system_name, name, step) {
                    return Ok(val.clone());
                }
            }
            Err(format!(
                "slot variable not found: {}.{name} slot={} step={step}",
                ctx.entity, ctx.slot
            ))
        }

        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = ctx.vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }

        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = try_encode_slot_expr(ctx, left, step)?;
            let r = try_encode_slot_expr(ctx, right, step)?;
            if op == "OpSeqConcat" {
                let Some(IRType::Seq { element }) = expr_type(left) else {
                    return Err("Seq::concat requires sequence operands".to_owned());
                };
                return smt::seq_concat(&l, &r, element);
            }
            if op == "OpMapHas" {
                let Some(IRType::Map { value, .. }) = expr_type(left) else {
                    return Err("Map::has requires a map-typed left operand".to_owned());
                };
                return smt::map_has(&l, &r, value);
            }
            if op == "OpMapMerge" {
                let Some(IRType::Map { key, value }) = expr_type(left) else {
                    return Err("Map::merge requires map operands".to_owned());
                };
                return smt::map_merge(&l, &r, key, value);
            }
            Ok(smt::binop(op, &l, &r)?)
        }

        IRExpr::UnOp { op, operand, .. } => {
            let v = try_encode_slot_expr(ctx, operand, step)?;
            if op == "OpSeqHead" {
                let Some(IRType::Seq { element }) = expr_type(operand) else {
                    return smt::unop(op, &v);
                };
                return smt::seq_head(&v, element);
            }
            if op == "OpSeqTail" {
                if let IRExpr::SeqLit { elements, ty, .. } = operand.as_ref() {
                    let tail = IRExpr::SeqLit {
                        elements: elements.iter().skip(1).cloned().collect(),
                        ty: ty.clone(),
                        span: None,
                    };
                    return try_encode_slot_expr(ctx, &tail, step);
                }
                let Some(IRType::Seq { element }) = expr_type(operand) else {
                    return smt::unop(op, &v);
                };
                return smt::seq_tail(&v, element);
            }
            if op == "OpSeqLength" {
                let Some(IRType::Seq { element }) = expr_type(operand) else {
                    return smt::unop(op, &v);
                };
                return smt::seq_length(&v, element);
            }
            if op == "OpSeqEmpty" {
                let Some(IRType::Seq { element }) = expr_type(operand) else {
                    return smt::unop(op, &v);
                };
                let len = smt::seq_length(&v, element)?;
                return Ok(SmtValue::Bool(smt::smt_eq(&len, &smt::int_val(0))?));
            }
            if op == "OpMapDomain" {
                if let IRExpr::MapLit { entries, .. } = operand.as_ref() {
                    let set_lit = IRExpr::SetLit {
                        elements: entries.iter().map(|(k, _)| k.clone()).collect(),
                        ty: IRType::Set {
                            element: Box::new(match expr_type(operand) {
                                Some(IRType::Map { key, .. }) => key.as_ref().clone(),
                                _ => IRType::Int,
                            }),
                        },
                        span: None,
                    };
                    return try_encode_slot_expr(ctx, &set_lit, step);
                }
                let Some(IRType::Map { key, value }) = expr_type(operand) else {
                    return Err("Map::domain requires a map operand".to_owned());
                };
                return smt::map_domain(&v, key, value);
            }
            if op == "OpMapRange" {
                if let IRExpr::MapLit { entries, .. } = operand.as_ref() {
                    let set_lit = IRExpr::SetLit {
                        elements: entries.iter().map(|(_, value)| value.clone()).collect(),
                        ty: IRType::Set {
                            element: Box::new(match expr_type(operand) {
                                Some(IRType::Map { value, .. }) => value.as_ref().clone(),
                                _ => IRType::Int,
                            }),
                        },
                        span: None,
                    };
                    return try_encode_slot_expr(ctx, &set_lit, step);
                }
                let Some(IRType::Map { key, value }) = expr_type(operand) else {
                    return Err("Map::range requires a map operand".to_owned());
                };
                return smt::map_range(&v, key, value);
            }
            Ok(smt::unop(op, &v)?)
        }

        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                // Check shared Choose variable params: `var.field` → shared Z3 var
                let qualified = format!("{name}.{field}");
                if let Some(val) = ctx.params.get(&qualified) {
                    return Ok(val.clone());
                }
                // Check cross-entity bindings (e.g., r.product_id where
                // r is from a prior Choose over Reservation)
                if let Some((entity, slot)) = ctx.bindings.get(name.as_str()) {
                    if let Some(val) = ctx.pool.field_at(entity, *slot, field, step) {
                        return Ok(val.clone());
                    }
                }
                // struct-typed system field access (e.g., ui.screen)
                if !ctx.system_name.is_empty()
                    && ctx.pool.is_system_struct_field(ctx.system_name, name)
                {
                    if let Some(val) = ctx.pool.system_field_at(ctx.system_name, &qualified, step) {
                        return Ok(val.clone());
                    }
                }
                // entity-typed step parameter field access.
                // `item.status` where item is an entity-typed param: resolve
                // by looking up the param slot value and the entity's field.
                if let Some(ent_name) = ctx.entity_param_types.get(name.as_str()) {
                    if let Some(param_val) = ctx.params.get(name.as_str()) {
                        let n_slots = ctx.pool.slots_for(ent_name);
                        // Build ITE chain: if param==0 then field_0
                        // elif param==1 then field_1...
                        let mut result: Option<SmtValue> = None;
                        for slot in (0..n_slots).rev() {
                            if let Some(field_val) = ctx.pool.field_at(ent_name, slot, field, step)
                            {
                                let slot_id = smt::int_val(slot as i64);
                                let cond = smt::smt_eq(param_val, &slot_id)?;
                                result = Some(match result {
                                    None => field_val.clone(),
                                    Some(else_val) => smt::smt_ite(&cond, field_val, &else_val),
                                });
                            }
                        }
                        if let Some(val) = result {
                            return Ok(val);
                        }
                    }
                }
            }
            // Fall back to current entity context
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, field, step) {
                return Ok(val.clone());
            }
            Err(format!(
                "slot field not found: {}.{field} slot={} step={step}",
                ctx.entity, ctx.slot
            ))
        }

        IRExpr::App { .. } => {
            let Some((kind, full_name, args)) = defenv::classify_app_chain_public(
                &ctx.vctx.defs,
                expr,
                Some(ctx.system_name),
                &ctx.vctx.system_queries,
            ) else {
                return Err(format!(
                    "slot expression encoding not yet supported: {expr:?}"
                ));
            };

            if kind != AppHeadKind::Query {
                return Err(format!(
                    "slot expression reached pure application `{full_name}` \
                     without expansion; App in slot encoding is reserved for \
                     query evaluation"
                ));
            }

            let (query_system, query_name) = full_name
                .split_once("::")
                .map(|(system, query)| (system.to_owned(), query.to_owned()))
                .expect("query classification should always produce a qualified name");

            let Some(query) = ctx
                .vctx
                .system_queries
                .get(&(query_system.clone(), query_name.clone()))
            else {
                return Err(format!(
                    "slot expression encoding not yet supported: {expr:?}"
                ));
            };

            assert_eq!(
                query.params.len(),
                args.len(),
                "query arity mismatch in slot expression: expected {} args for {}::{}, got {}",
                query.params.len(),
                query_system,
                query_name,
                args.len()
            );

            let mut params = ctx.params.clone();
            let mut entity_param_types = ctx.entity_param_types.clone();
            for (param, arg_expr) in query.params.iter().zip(args.iter()) {
                let value = try_encode_slot_expr(ctx, arg_expr, step)?;
                params.insert(param.name.clone(), value);
                if let IRType::Entity { name } = &param.ty {
                    entity_param_types.insert(param.name.clone(), name.clone());
                }
            }

            let inner_ctx = SlotEncodeCtx {
                pool: ctx.pool,
                vctx: ctx.vctx,
                entity: ctx.entity,
                slot: ctx.slot,
                params,
                bindings: ctx.bindings.clone(),
                system_name: query_system.as_str(),
                entity_param_types: &entity_param_types,
                store_param_types: ctx.store_param_types,
            };
            try_encode_slot_expr(&inner_ctx, &query.body, step)
        }

        IRExpr::Prime { expr, .. } => try_encode_slot_expr(ctx, expr, step + 1),

        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = try_encode_slot_expr(ctx, map, step)?;
            let k = try_encode_slot_expr(ctx, key, step)?;
            let v = try_encode_slot_expr(ctx, value, step)?;
            if let Some(IRType::Map {
                value: value_ty, ..
            }) = expr_type(map)
            {
                return smt::map_store(&arr, &k, &v, value_ty);
            }
            Ok(SmtValue::Array(
                arr.as_array()
                    .map_err(|e| format!("slot map update array encoding failed: {e}"))?
                    .store(&k.to_dynamic(), &v.to_dynamic()),
            ))
        }

        IRExpr::Index { map, key, ty, .. } => {
            if let IRExpr::Var {
                name: store_name, ..
            } = map.as_ref()
            {
                if let Some(entity_name) = ctx.store_param_types.get(store_name.as_str()) {
                    let k = try_encode_slot_expr(ctx, key, step)?;
                    return Ok(encode_store_membership(ctx.pool, entity_name, &k, step));
                }
            }
            let arr = try_encode_slot_expr(ctx, map, step)?;
            let k = try_encode_slot_expr(ctx, key, step)?;
            if let Some(IRType::Map { value, .. }) = expr_type(map) {
                return smt::map_lookup(&arr, &k, value);
            }
            if let Some(IRType::Seq { element }) = expr_type(map) {
                return smt::seq_index(&arr, &k, element);
            }
            Ok(smt::dynamic_to_typed_value(
                arr.as_array()
                    .map_err(|e| format!("slot index array encoding failed: {e}"))?
                    .select(&k.to_dynamic()),
                ty,
            ))
        }

        IRExpr::MapLit { entries, ty, .. } => {
            // Build constant array with default value, then store each entry
            let (key_ty, val_ty) = match ty {
                IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
                _ => return Err(format!("MapLit with non-Map type: {ty:?}")),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default_val = smt::map_none_dynamic(val_ty);
            let mut arr = smt::const_array(&key_sort, &default_val);
            for entry in entries {
                let k = try_encode_slot_expr(ctx, &entry.0, step)?;
                let v = try_encode_slot_expr(ctx, &entry.1, step)?;
                arr = arr.store(&k.to_dynamic(), &smt::map_some_dynamic(val_ty, &v));
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::SetLit { elements, ty, .. } => {
            // Set as characteristic function: Array<T, Bool>
            let elem_ty = match ty {
                IRType::Set { element } => element.as_ref(),
                _ => return Err(format!("SetLit with non-Set type: {ty:?}")),
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_val = smt::bool_val(false).to_dynamic();
            let mut arr = smt::const_array(&elem_sort, &false_val);
            let true_val = smt::bool_val(true).to_dynamic();
            for elem in elements {
                let e = try_encode_slot_expr(ctx, elem, step)?;
                arr = arr.store(&e.to_dynamic(), &true_val);
            }
            Ok(SmtValue::Array(arr))
        }

        IRExpr::SeqLit { elements, ty, .. } => {
            let elem_ty = match ty {
                IRType::Seq { element } => element.as_ref(),
                _ => return Err(format!("SeqLit with non-Seq type: {ty:?}")),
            };
            let elems = elements
                .iter()
                .map(|elem| try_encode_slot_expr(ctx, elem, step))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(smt::seq_literal(elem_ty, &elems))
        }

        IRExpr::Card { expr: inner, .. } => Ok(match inner.as_ref() {
            IRExpr::SetLit { elements, .. } => {
                let unique: std::collections::HashSet<String> =
                    elements.iter().map(|e| format!("{e:?}")).collect();
                smt::int_val(i64::try_from(unique.len()).unwrap_or(0))
            }
            IRExpr::SeqLit { elements, .. } => {
                smt::int_val(i64::try_from(elements.len()).unwrap_or(0))
            }
            IRExpr::MapLit { entries, .. } => {
                let unique_keys: std::collections::HashSet<String> =
                    entries.iter().map(|(k, _)| format!("{k:?}")).collect();
                smt::int_val(i64::try_from(unique_keys.len()).unwrap_or(0))
            }
            _ => {
                if let Some(IRType::Seq { element }) = expr_type(inner) {
                    let seq = try_encode_slot_expr(ctx, inner, step)?;
                    return smt::seq_length(&seq, element);
                }
                return Err(format!(
                    "unsupported cardinality in action context: {inner:?}"
                ));
            }
        }),

        IRExpr::Exists {
            var,
            domain: IRType::Int,
            body,
            ..
        } => {
            let Some(entity_name) = infer_store_quant_entity(var, body, ctx.store_param_types)
            else {
                return Err(format!(
                    "slot expression encoding not yet supported: {expr:?}"
                ));
            };
            let n_slots = ctx.pool.slots_for(&entity_name);
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let mut params = ctx.params.clone();
                params.insert(var.clone(), smt::int_val(slot as i64));
                let mut entity_param_types = ctx.entity_param_types.clone();
                entity_param_types.insert(var.clone(), entity_name.clone());
                let inner_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: &entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                disjuncts.push(try_encode_slot_expr(&inner_ctx, body, step)?.to_bool()?);
            }
            if disjuncts.is_empty() {
                return Ok(SmtValue::Bool(smt::bool_const(false)));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(SmtValue::Bool(smt::bool_or(&refs)))
        }

        IRExpr::Forall {
            var,
            domain: IRType::Int,
            body,
            ..
        } => {
            let Some(entity_name) = infer_store_quant_entity(var, body, ctx.store_param_types)
            else {
                return Err(format!(
                    "slot expression encoding not yet supported: {expr:?}"
                ));
            };
            let n_slots = ctx.pool.slots_for(&entity_name);
            let mut conjuncts = Vec::new();
            for slot in 0..n_slots {
                let mut params = ctx.params.clone();
                params.insert(var.clone(), smt::int_val(slot as i64));
                let mut entity_param_types = ctx.entity_param_types.clone();
                entity_param_types.insert(var.clone(), entity_name.clone());
                let inner_ctx = SlotEncodeCtx {
                    pool: ctx.pool,
                    vctx: ctx.vctx,
                    entity: ctx.entity,
                    slot: ctx.slot,
                    params,
                    bindings: ctx.bindings.clone(),
                    system_name: ctx.system_name,
                    entity_param_types: &entity_param_types,
                    store_param_types: ctx.store_param_types,
                };
                conjuncts.push(try_encode_slot_expr(&inner_ctx, body, step)?.to_bool()?);
            }
            if conjuncts.is_empty() {
                return Ok(SmtValue::Bool(smt::bool_const(true)));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(SmtValue::Bool(smt::bool_and(&refs)))
        }

        other => Err(format!(
            "slot expression encoding not yet supported: {other:?}"
        )),
    }
}

fn encode_slot_literal(lit: &LitVal) -> SmtValue {
    match lit {
        LitVal::Int { value } => smt::int_val(*value),
        LitVal::Bool { value } => smt::bool_val(*value),
        LitVal::Real { value } | LitVal::Float { value } => {
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            smt::real_val(scaled, 1_000_000)
        }
        LitVal::Str { .. } => smt::int_val(0),
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
#[allow(clippy::cloned_ref_to_slice_refs, clippy::needless_borrow)]
mod tests {
    use super::super::smt::{AbideSolver, SatResult};
    use super::*;
    use crate::ir::types::{
        IRAction, IRAssumptionSet, IRCommand, IRField, IRFsm, IRFsmTransition, IRStep, IRSystem,
        IRUpdate, IRVariant, LitVal,
    };

    fn make_order_entity() -> IREntity {
        IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Identity,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        variants: vec![
                            IRVariant::simple("Pending"),
                            IRVariant::simple("Confirmed"),
                            IRVariant::simple("Shipped"),
                        ],
                    },
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: None,
                    initial_constraint: None,
                },
            ],
            transitions: vec![IRTransition {
                name: "confirm".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        }
    }

    fn make_vctx() -> VerifyContext {
        let mut vctx = VerifyContext {
            variants: super::super::context::VariantMap::new(),
            enum_ranges: HashMap::new(),
            entities: HashMap::new(),
            adt_sorts: HashMap::new(),
            command_params: HashMap::new(),
            system_queries: HashMap::new(),
            defs: super::defenv::DefEnv::from_ir(&crate::ir::types::IRProgram {
                types: vec![],
                constants: vec![],
                functions: vec![],
                entities: vec![],
                systems: vec![],
                verifies: vec![],
                theorems: vec![],
                axioms: vec![],
                lemmas: vec![],
                scenes: vec![],
            }),
        };
        let (min, max) = vctx.variants.register_enum(
            "OrderStatus",
            &[
                "Pending".to_owned(),
                "Confirmed".to_owned(),
                "Shipped".to_owned(),
            ],
        );
        vctx.enum_ranges
            .insert("OrderStatus".to_owned(), (min, max));
        let (min, max) = vctx.variants.register_enum(
            "UiStatus",
            &["Idle".to_owned(), "Ready".to_owned(), "Done".to_owned()],
        );
        vctx.enum_ranges.insert("UiStatus".to_owned(), (min, max));
        vctx
    }

    fn make_system_with_int_fields() -> IRSystem {
        IRSystem {
            name: "Ui".to_owned(),
            store_params: vec![],
            fields: vec![
                IRField {
                    name: "screen".to_owned(),
                    ty: IRType::Int,
                    default: None,
                    initial_constraint: None,
                },
                IRField {
                    name: "mode".to_owned(),
                    ty: IRType::Int,
                    default: None,
                    initial_constraint: None,
                },
            ],
            entities: vec![],
            commands: vec![IRCommand {
                name: "handle".to_owned(),
                params: vec![],
                return_type: None,
            }],
            steps: vec![IRStep {
                name: "handle".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "screen".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        }
    }

    fn make_system_with_fsm_field() -> IRSystem {
        IRSystem {
            name: "Ui".to_owned(),
            store_params: vec![],
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "UiStatus".to_owned(),
                    variants: vec![],
                },
                default: None,
                initial_constraint: None,
            }],
            entities: vec![],
            commands: vec![IRCommand {
                name: "advance".to_owned(),
                params: vec![],
                return_type: None,
            }],
            steps: vec![IRStep {
                name: "advance".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "status".to_owned(),
                                ty: IRType::Enum {
                                    name: "UiStatus".to_owned(),
                                    variants: vec![],
                                },
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "UiStatus".to_owned(),
                            ctor: "Done".to_owned(),
                            span: None,
                            args: vec![],
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            }],
            fsm_decls: vec![IRFsm {
                field: "status".to_owned(),
                enum_name: "UiStatus".to_owned(),
                transitions: vec![IRFsmTransition {
                    from: "Idle".to_owned(),
                    to: "Ready".to_owned(),
                }],
            }],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        }
    }

    #[test]
    fn fire_tracking_aggregates_multi_clause_commands_per_step() {
        let entity = make_order_entity();
        let vctx = make_vctx();
        let pool = create_slot_pool_with_systems(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 1_usize)]),
            2,
            &[IRSystem {
                name: "Shop".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec![entity.name.clone()],
                commands: vec![IRCommand {
                    name: "tick".to_owned(),
                    params: vec![],
                    return_type: None,
                }],
                steps: vec![
                    IRStep {
                        name: "tick".to_owned(),
                        params: vec![],
                        guard: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                        body: vec![],
                        return_expr: None,
                    },
                    IRStep {
                        name: "tick".to_owned(),
                        params: vec![],
                        guard: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                        body: vec![],
                        return_expr: None,
                    },
                ],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
        );

        let fire_tracking = transition_constraints_with_fire(
            &pool,
            &vctx,
            &[entity],
            &[IRSystem {
                name: "Shop".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec!["Order".to_owned()],
                commands: vec![IRCommand {
                    name: "tick".to_owned(),
                    params: vec![],
                    return_type: None,
                }],
                steps: vec![
                    IRStep {
                        name: "tick".to_owned(),
                        params: vec![],
                        guard: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                        body: vec![],
                        return_expr: None,
                    },
                    IRStep {
                        name: "tick".to_owned(),
                        params: vec![],
                        guard: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                        body: vec![],
                        return_expr: None,
                    },
                ],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            2,
            &IRAssumptionSet::default_for_verify(),
        );

        let command_fire = fire_tracking
            .fire_vars
            .get(&("Shop".to_owned(), "tick".to_owned()))
            .expect("command fire entry");
        assert_eq!(command_fire.len(), 2);
        let first_clause_fire = fire_tracking
            .clause_fire_vars
            .get(&("Shop".to_owned(), "tick".to_owned(), 0))
            .expect("first clause fire entry");
        let second_clause_fire = fire_tracking
            .clause_fire_vars
            .get(&("Shop".to_owned(), "tick".to_owned(), 1))
            .expect("second clause fire entry");
        assert_eq!(first_clause_fire.len(), 2);
        assert_eq!(second_clause_fire.len(), 2);
    }

    #[test]
    fn fire_tracking_frames_unmodified_system_fields() {
        let vctx = make_vctx();
        let system = make_system_with_int_fields();
        let pool = create_slot_pool_with_systems(&[], &HashMap::new(), 1, &[system.clone()]);

        let fire_tracking = transition_constraints_with_fire(
            &pool,
            &vctx,
            &[],
            std::slice::from_ref(&system),
            1,
            &IRAssumptionSet::default_for_verify(),
        );

        let solver = AbideSolver::new();
        for c in &fire_tracking.constraints {
            solver.assert(c);
        }

        let fire = fire_tracking
            .clause_fire_vars
            .get(&("Ui".to_owned(), "handle".to_owned(), 0))
            .expect("handle clause fire entry");
        solver.assert(&fire[0]);

        let screen_t0 = pool.system_field_at("Ui", "screen", 0).expect("screen t0");
        let screen_t1 = pool.system_field_at("Ui", "screen", 1).expect("screen t1");
        let mode_t0 = pool.system_field_at("Ui", "mode", 0).expect("mode t0");
        let mode_t1 = pool.system_field_at("Ui", "mode", 1).expect("mode t1");

        if let SmtValue::Int(v) = screen_t0 {
            solver.assert(smt::int_eq(v, &smt::int_lit(0)));
        }
        if let SmtValue::Int(v) = screen_t1 {
            solver.assert(smt::int_eq(v, &smt::int_lit(1)));
        }
        if let SmtValue::Int(v) = mode_t0 {
            solver.assert(smt::int_eq(v, &smt::int_lit(7)));
        }
        if let SmtValue::Int(v) = mode_t1 {
            solver.assert(smt::int_eq(v, &smt::int_lit(9)));
        }

        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn fire_tracking_enforces_system_field_fsm_transitions() {
        let vctx = make_vctx();
        let system = make_system_with_fsm_field();
        let pool = create_slot_pool_with_systems(&[], &HashMap::new(), 1, &[system.clone()]);

        let fire_tracking = transition_constraints_with_fire(
            &pool,
            &vctx,
            &[],
            std::slice::from_ref(&system),
            1,
            &IRAssumptionSet::default_for_verify(),
        );

        let solver = AbideSolver::new();
        for c in &fire_tracking.constraints {
            solver.assert(c);
        }

        let fire = fire_tracking
            .clause_fire_vars
            .get(&("Ui".to_owned(), "advance".to_owned(), 0))
            .expect("advance clause fire entry");
        solver.assert(&fire[0]);

        let status_t0 = pool.system_field_at("Ui", "status", 0).expect("status t0");
        let status_t1 = pool.system_field_at("Ui", "status", 1).expect("status t1");
        let idle_id = vctx
            .variants
            .try_id_of("UiStatus", "Idle")
            .expect("Idle variant id");
        let done_id = vctx
            .variants
            .try_id_of("UiStatus", "Done")
            .expect("Done variant id");
        if let SmtValue::Int(v) = status_t0 {
            solver.assert(smt::int_eq(v, &smt::int_lit(idle_id)));
        }
        if let SmtValue::Int(v) = status_t1 {
            solver.assert(smt::int_eq(v, &smt::int_lit(done_id)));
        }

        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn lasso_loopback_includes_system_fields() {
        let system = make_system_with_int_fields();
        let pool = create_slot_pool_with_systems(&[], &HashMap::new(), 1, &[system.clone()]);
        let lasso = lasso_loopback(&pool, &[], &[system]);

        let solver = AbideSolver::new();
        for c in &lasso.constraints {
            solver.assert(c);
        }

        let mode_t0 = pool.system_field_at("Ui", "mode", 0).expect("mode t0");
        let mode_t1 = pool.system_field_at("Ui", "mode", 1).expect("mode t1");
        if let SmtValue::Int(v) = mode_t0 {
            solver.assert(smt::int_eq(v, &smt::int_lit(1)));
        }
        if let SmtValue::Int(v) = mode_t1 {
            solver.assert(smt::int_eq(v, &smt::int_lit(2)));
        }

        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn slot_pool_creation() {
        let entity = make_order_entity();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 3);

        let pool = create_slot_pool(&[entity], &scopes, 2);

        // 3 slots × 3 fields = 9 field var sets
        assert_eq!(pool.slots_for("Order"), 3);
        // Each slot has variables for all 3 steps (bound=2 → steps 0,1,2)
        assert!(pool.field_at("Order", 0, "status", 0).is_some());
        assert!(pool.field_at("Order", 2, "total", 2).is_some());
        assert!(pool.field_at("Order", 3, "status", 0).is_none()); // out of slots
                                                                   // Active flags
        assert!(pool.active_at("Order", 0, 0).is_some());
        assert!(pool.active_at("Order", 2, 2).is_some());
    }

    #[test]
    fn initial_state_all_inactive() {
        let entity = make_order_entity();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 3);
        let pool = create_slot_pool(&[entity], &scopes, 2);

        let constraints = initial_state_constraints(&pool);
        // 3 slots should produce 3 "not active at step 0" constraints
        assert_eq!(constraints.len(), 3);
    }

    #[test]
    fn domain_constraints_for_enum() {
        let entity = make_order_entity();
        let vctx = make_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 2);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        let constraints = domain_constraints(&pool, &vctx, &[entity]);
        // 2 slots × 1 enum field × 2 steps × 2 constraints (min,max) = 8
        assert_eq!(constraints.len(), 8);
    }

    #[test]
    fn encode_action_produces_formula() {
        let entity = make_order_entity();
        let vctx = make_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 2);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 2);

        let action = &entity.transitions[0]; // confirm
        let no_params = HashMap::new();
        let formula = encode_action(&pool, &vctx, &entity, action, 0, 0, &no_params);
        // Should produce a non-trivial Bool formula
        assert!(!format!("{formula:?}").is_empty());
    }

    #[test]
    fn encode_action_sat_check() {
        let entity = make_order_entity();
        let vctx = make_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 1);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        let action = &entity.transitions[0]; // confirm: requires status == Pending

        // Set status at step 0 to Pending (variant ID 0)
        let pending_id = vctx.variants.id_of("OrderStatus", "Pending");
        let status_t0 = pool.field_at("Order", 0, "status", 0).unwrap();

        let solver = AbideSolver::new();
        // Slot is active
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
            solver.assert(active);
        }
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 1) {
            solver.assert(active);
        }
        // Status = Pending at step 0
        if let SmtValue::Int(s) = status_t0 {
            solver.assert(smt::int_eq(&s, &smt::int_lit(pending_id)));
        }

        // Encode and assert the action
        let no_params = HashMap::new();
        let formula = encode_action(&pool, &vctx, &entity, action, 0, 0, &no_params);
        solver.assert(&formula);

        assert_eq!(solver.check(), SatResult::Sat);

        // Verify: status at step 1 should be Confirmed
        let confirmed_id = vctx.variants.id_of("OrderStatus", "Confirmed");
        let status_t1 = pool.field_at("Order", 0, "status", 1).unwrap();
        solver.push();
        if let SmtValue::Int(s) = status_t1 {
            solver.assert(smt::int_eq(&s, &smt::int_lit(confirmed_id)));
        }
        assert_eq!(solver.check(), SatResult::Sat);
        solver.pop();

        // Verify: status at step 1 should NOT be Pending
        solver.push();
        if let SmtValue::Int(s) = status_t1 {
            solver.assert(smt::int_eq(&s, &smt::int_lit(pending_id)));
        }
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();
    }

    #[test]
    fn stutter_preserves_state() {
        let entity = make_order_entity();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 1);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        let stutter = stutter_constraint(&pool, &[entity], 0);

        let solver = AbideSolver::new();
        // Set status at step 0
        if let Some(SmtValue::Int(s0)) = pool.field_at("Order", 0, "status", 0) {
            solver.assert(smt::int_eq(&s0, &smt::int_lit(42)));
        }
        solver.assert(&stutter);

        // Status at step 1 should equal step 0
        if let Some(SmtValue::Int(s1)) = pool.field_at("Order", 0, "status", 1) {
            solver.push();
            solver.assert(smt::int_eq(&s1, &smt::int_lit(42)));
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();

            solver.push();
            solver.assert(smt::int_eq(&s1, &smt::int_lit(99)));
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop();
        }
    }

    // ── Fix 5: Focused tests ────────────────────────────────────────

    /// Helper: create an Account entity with a `balance: Int` field and
    /// a `deposit(amount: Int)` action that requires `amount > 0` and sets
    /// `balance' = balance + amount`.
    fn make_account_entity() -> IREntity {
        IREntity {
            name: "Account".to_owned(),
            fields: vec![IRField {
                name: "balance".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "deposit".to_owned(),
                refs: vec![],
                params: vec![IRTransParam {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
                guard: IRExpr::BinOp {
                    op: "OpGt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "amount".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "balance".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "balance".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "amount".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        ty: IRType::Int,

                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        }
    }

    fn make_account_vctx() -> VerifyContext {
        VerifyContext {
            variants: super::super::context::VariantMap::new(),
            enum_ranges: HashMap::new(),
            entities: HashMap::new(),
            adt_sorts: HashMap::new(),
            command_params: HashMap::new(),
            system_queries: HashMap::new(),
            defs: super::defenv::DefEnv::from_ir(&crate::ir::types::IRProgram {
                types: vec![],
                constants: vec![],
                functions: vec![],
                entities: vec![],
                systems: vec![],
                verifies: vec![],
                theorems: vec![],
                axioms: vec![],
                lemmas: vec![],
                scenes: vec![],
            }),
        }
    }

    #[test]
    fn test_apply_with_params() {
        let entity = make_account_entity();
        let vctx = make_account_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Account".to_owned(), 1);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        let action = &entity.transitions[0]; // deposit

        // Build params: amount = 100
        let mut params = HashMap::new();
        params.insert("amount".to_owned(), smt::int_val(100));

        let solver = AbideSolver::new();
        // Slot is active
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 0) {
            solver.assert(active);
        }
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 1) {
            solver.assert(active);
        }
        // Balance = 50 at step 0
        if let Some(SmtValue::Int(b0)) = pool.field_at("Account", 0, "balance", 0) {
            solver.assert(smt::int_eq(&b0, &smt::int_lit(50)));
        }

        let formula = encode_action(&pool, &vctx, &entity, action, 0, 0, &params);
        solver.assert(&formula);

        // Should be SAT (amount=100 > 0, balance becomes 150)
        assert_eq!(solver.check(), SatResult::Sat);

        // Verify: balance at step 1 should be 150
        if let Some(SmtValue::Int(b1)) = pool.field_at("Account", 0, "balance", 1) {
            solver.push();
            solver.assert(smt::int_eq(&b1, &smt::int_lit(150)));
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();

            // balance at step 1 should NOT be 50 (unchanged)
            solver.push();
            solver.assert(smt::int_eq(&b1, &smt::int_lit(50)));
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop();
        }

        // Now test with amount = -5 (violates guard), should be UNSAT
        let mut bad_params = HashMap::new();
        bad_params.insert("amount".to_owned(), smt::int_val(-5));
        let solver2 = AbideSolver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 0) {
            solver2.assert(active);
        }
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 1) {
            solver2.assert(active);
        }
        let formula2 = encode_action(&pool, &vctx, &entity, action, 0, 0, &bad_params);
        solver2.assert(&formula2);
        assert_eq!(solver2.check(), SatResult::Unsat);
    }

    #[test]
    fn test_forall_inactive_slot_framed() {
        // 2 slots: slot 0 active, slot 1 inactive.
        // After ForAll encoding, inactive slot 1's fields must be unchanged.
        let entity = make_account_entity();
        let vctx = make_account_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Account".to_owned(), 2);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        // Build a ForAll event with deposit action
        let event = IRStep {
            name: "deposit_all".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::ForAll {
                var: "a".to_owned(),
                entity: "Account".to_owned(),
                ops: vec![IRAction::Apply {
                    target: "Account".to_owned(),
                    transition: "deposit".to_owned(),
                    refs: vec![],
                    args: vec![IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 10 },

                        span: None,
                    }],
                }],
            }],
            return_expr: None,
        };

        let solver = AbideSolver::new();
        // Slot 0: active
        if let Some(SmtValue::Bool(a0)) = pool.active_at("Account", 0, 0) {
            solver.assert(a0);
        }
        if let Some(SmtValue::Bool(a0_next)) = pool.active_at("Account", 0, 1) {
            solver.assert(a0_next);
        }
        // Slot 1: inactive
        if let Some(SmtValue::Bool(a1)) = pool.active_at("Account", 1, 0) {
            solver.assert(smt::bool_not(&a1));
        }

        // Set slot 1 balance at step 0
        if let Some(SmtValue::Int(b1_t0)) = pool.field_at("Account", 1, "balance", 0) {
            solver.assert(smt::int_eq(&b1_t0, &smt::int_lit(200)));
        }

        // Set slot 0 balance at step 0
        if let Some(SmtValue::Int(b0_t0)) = pool.field_at("Account", 0, "balance", 0) {
            solver.assert(smt::int_eq(&b0_t0, &smt::int_lit(100)));
        }

        let formula = encode_step(&pool, &vctx, &[entity], &[], &event, 0);
        solver.assert(&formula);
        assert_eq!(solver.check(), SatResult::Sat);

        // Inactive slot 1: balance at step 1 must equal step 0 (200)
        if let Some(SmtValue::Int(b1_t1)) = pool.field_at("Account", 1, "balance", 1) {
            solver.push();
            solver.assert(smt::int_eq(&b1_t1, &smt::int_lit(200)));
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();

            // Must NOT be possible for slot 1 balance to change
            solver.push();
            solver.assert(smt::int_eq(&b1_t1, &smt::int_lit(999)));
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop();
        }

        // Inactive slot 1: active flag at step 1 must still be false
        if let Some(SmtValue::Bool(a1_t1)) = pool.active_at("Account", 1, 1) {
            solver.push();
            solver.assert(smt::bool_not(&a1_t1));
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();

            solver.push();
            solver.assert(a1_t1);
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop();
        }
    }

    #[test]
    fn test_create_non_selected_slot_stable() {
        // 2 slots, both inactive. Create for slot 0.
        // Slot 1's fields must be unchanged (not arbitrary).
        let entity = make_account_entity();
        let vctx = make_account_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Account".to_owned(), 2);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        let solver = AbideSolver::new();
        // Both slots inactive at step 0
        if let Some(SmtValue::Bool(a0)) = pool.active_at("Account", 0, 0) {
            solver.assert(smt::bool_not(&a0));
        }
        if let Some(SmtValue::Bool(a1)) = pool.active_at("Account", 1, 0) {
            solver.assert(smt::bool_not(&a1));
        }

        // Set slot 1 balance at step 0
        if let Some(SmtValue::Int(b1_t0)) = pool.field_at("Account", 1, "balance", 0) {
            solver.assert(smt::int_eq(&b1_t0, &smt::int_lit(500)));
        }

        // Encode create for Account with balance = 100
        let create_fields = vec![(
            "balance".to_owned(),
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 100 },

                span: None,
            },
        )];
        let formula = encode_create(
            &pool,
            &vctx,
            "Account",
            Some(&entity),
            &create_fields,
            0,
            &HashMap::new(),
        );
        solver.assert(&formula);

        assert_eq!(solver.check(), SatResult::Sat);

        // The non-selected slot's balance at step 1 must be unchanged (500)
        // We need to check that at least one disjunct constrains the other slot.
        // Since both slots are inactive and one gets created, the other must be framed.
        //
        // The create chose one of the two slots. In either branch, the other is framed.
        // So slot 1's balance at step 1 must be 500 if slot 0 was chosen,
        // and slot 0's balance at step 1 must be unchanged if slot 1 was chosen.
        //
        // Let's force slot 0 to be the created one and verify slot 1 is framed.
        solver.push();
        if let Some(SmtValue::Bool(a0_t1)) = pool.active_at("Account", 0, 1) {
            solver.assert(a0_t1); // slot 0 becomes active
        }
        // Slot 1 balance at step 1 must equal step 0
        if let Some(SmtValue::Int(b1_t1)) = pool.field_at("Account", 1, "balance", 1) {
            solver.push();
            solver.assert(smt::int_eq(&b1_t1, &smt::int_lit(500)));
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();

            solver.push();
            solver.assert(smt::int_eq(&b1_t1, &smt::int_lit(999)));
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop();
        }
        solver.pop();
    }

    /// / regression: when a top-level Apply targets an
    /// entity-typed event parameter (e.g. `tick(j: Job) { j.toggle() }`),
    /// the encoder must constrain the per-step `param_<target>_<step>`
    /// Z3 var to equal the slot index that the body actually mutates.
    /// Without this tie, per-tuple fairness encoding cannot identify
    /// which tuple actually fired.
    #[test]
    fn apply_on_entity_param_ties_param_to_slot() {
        // entity Job { triggered: Bool = false action toggle() { triggered' = not triggered } }
        let job = IREntity {
            name: "Job".to_owned(),
            fields: vec![IRField {
                name: "triggered".to_owned(),
                ty: IRType::Bool,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "toggle".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "triggered".to_owned(),
                    value: IRExpr::UnOp {
                        op: "OpNot".to_owned(),
                        operand: Box::new(IRExpr::Var {
                            name: "triggered".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        // event tick(j: Job) { j.toggle() }
        let tick = IRStep {
            name: "tick".to_owned(),
            params: vec![IRTransParam {
                name: "j".to_owned(),
                ty: IRType::Entity {
                    name: "Job".to_owned(),
                },
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Apply {
                target: "j".to_owned(),
                transition: "toggle".to_owned(),
                refs: vec![],
                args: vec![],
            }],
            return_expr: None,
        };

        let vctx = make_account_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Job".to_owned(), 2);
        let pool = create_slot_pool(&[job.clone()], &scopes, 1);

        // Two active Job slots, both initially triggered=false
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(a0)) = pool.active_at("Job", 0, 0) {
            solver.assert(a0);
        }
        if let Some(SmtValue::Bool(a1)) = pool.active_at("Job", 1, 0) {
            solver.assert(a1);
        }
        if let Some(SmtValue::Bool(a0_t1)) = pool.active_at("Job", 0, 1) {
            solver.assert(a0_t1);
        }
        if let Some(SmtValue::Bool(a1_t1)) = pool.active_at("Job", 1, 1) {
            solver.assert(a1_t1);
        }
        if let Some(SmtValue::Bool(t0)) = pool.field_at("Job", 0, "triggered", 0) {
            solver.assert(smt::bool_not(&t0));
        }
        if let Some(SmtValue::Bool(t1)) = pool.field_at("Job", 1, "triggered", 0) {
            solver.assert(smt::bool_not(&t1));
        }

        let system = IRSystem {
            name: "S".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Job".to_owned()],
            commands: vec![],
            steps: vec![tick.clone()],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            let_bindings: vec![],
            preds: vec![],
            procs: vec![],
        };
        let formula = encode_step(&pool, &vctx, &[job], &[system], &tick, 0);
        solver.assert(&formula);

        // Force the param value to slot 0
        let param_j_0 = smt::int_var("param_j_0");
        if let SmtValue::Int(p) = &param_j_0 {
            solver.assert(smt::int_eq(&p, &smt::int_lit(0)));
        }

        // Sanity: the constrained system is satisfiable
        assert_eq!(solver.check(), SatResult::Sat);

        // With the param-slot link, picking param=0 forces the body to
        // act on slot 0 → slot 0's `triggered` flips to true and slot 1
        // stays at false. Asserting "slot 1 triggered at step 1 is true"
        // must therefore be UNSAT.
        if let Some(SmtValue::Bool(t1_t1)) = pool.field_at("Job", 1, "triggered", 1) {
            solver.push();
            solver.assert(t1_t1);
            assert_eq!(
                solver.check(),
                SatResult::Unsat,
                "with param_j_0 = 0, slot 1 must be framed (triggered must stay false)"
            );
            solver.pop();

            // And asserting "slot 1 triggered at step 1 stays false" must be SAT.
            solver.push();
            solver.assert(smt::bool_not(&t1_t1));
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();
        }

        // Symmetrically, slot 0 must have toggled to true.
        if let Some(SmtValue::Bool(t0_t1)) = pool.field_at("Job", 0, "triggered", 1) {
            solver.push();
            solver.assert(t0_t1);
            assert_eq!(solver.check(), SatResult::Sat);
            solver.pop();

            solver.push();
            solver.assert(smt::bool_not(&t0_t1));
            assert_eq!(
                solver.check(),
                SatResult::Unsat,
                "with param_j_0 = 0, slot 0's triggered must flip to true"
            );
            solver.pop();
        }
    }

    /// / regression: `encode_step_enabled` for an
    /// event whose body is a top-level Apply on an entity-typed param
    /// must consult the action's guard at the targeted slot. Without
    /// this, fairness obligations get the wrong enablement and either
    /// produce spurious liveness violations or overconstrain the lasso.
    #[test]
    fn enabled_for_apply_on_param_checks_action_guard() {
        // entity Job { triggered: Bool action toggle() requires not triggered { triggered' = not triggered } }
        let job = IREntity {
            name: "Job".to_owned(),
            fields: vec![IRField {
                name: "triggered".to_owned(),
                ty: IRType::Bool,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "toggle".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Var {
                        name: "triggered".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "triggered".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        let tick = IRStep {
            name: "tick".to_owned(),
            params: vec![IRTransParam {
                name: "j".to_owned(),
                ty: IRType::Entity {
                    name: "Job".to_owned(),
                },
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Apply {
                target: "j".to_owned(),
                transition: "toggle".to_owned(),
                refs: vec![],
                args: vec![],
            }],
            return_expr: None,
        };

        let vctx = make_account_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Job".to_owned(), 2);
        let pool = create_slot_pool(&[job.clone()], &scopes, 1);

        // Slot 0 active and already triggered (so toggle's guard `not triggered` fails);
        // slot 1 active and not triggered (so toggle's guard succeeds).
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(a0)) = pool.active_at("Job", 0, 0) {
            solver.assert(a0);
        }
        if let Some(SmtValue::Bool(a1)) = pool.active_at("Job", 1, 0) {
            solver.assert(a1);
        }
        if let Some(SmtValue::Bool(t0)) = pool.field_at("Job", 0, "triggered", 0) {
            solver.assert(t0); // slot 0 is already triggered
        }
        if let Some(SmtValue::Bool(t1)) = pool.field_at("Job", 1, "triggered", 0) {
            solver.assert(smt::bool_not(&t1)); // slot 1 is not triggered
        }

        // Per-tuple enabledness for j = 0: tick(j=0) tries to toggle slot 0,
        // but slot 0 is already triggered, so the action guard fails →
        // enabledness must be FALSE (UNSAT when asserted as true).
        let mut params_for_j_0 = HashMap::new();
        params_for_j_0.insert("j".to_owned(), smt::int_val(0));
        let enabled_with_j_0 = encode_step_enabled_with_params(
            &pool,
            &vctx,
            &[job.clone()],
            &[],
            &tick,
            0,
            params_for_j_0,
        );
        solver.push();
        solver.assert(&enabled_with_j_0);
        assert_eq!(
            solver.check(),
            SatResult::Unsat,
            "tick(j=0) must be DISABLED when slot 0's `not triggered` guard is false"
        );
        solver.pop();

        // Per-tuple enabledness for j = 1: slot 1 is not triggered, so the
        // action guard holds → enabledness must be TRUE (SAT).
        let mut params_for_j_1 = HashMap::new();
        params_for_j_1.insert("j".to_owned(), smt::int_val(1));
        let enabled_with_j_1 = encode_step_enabled_with_params(
            &pool,
            &vctx,
            &[job.clone()],
            &[],
            &tick,
            0,
            params_for_j_1,
        );
        solver.push();
        solver.assert(&enabled_with_j_1);
        assert_eq!(
            solver.check(),
            SatResult::Sat,
            "tick(j=1) must be ENABLED when slot 1's `not triggered` guard holds"
        );
        solver.pop();
    }

    /// / regression: when a top-level Apply targets an
    /// entity-typed event parameter AND another entity in the program
    /// defines a transition with the same name, the enabledness encoder
    /// must resolve the target via the param's entity type, not via
    /// "unique transition" name matching. The body encoder uses
    /// `var_to_entity` (populated from event params) to disambiguate;
    /// the enabledness encoder must mirror that to keep fairness
    /// obligations consistent with the actual transition semantics.
    #[test]
    fn enabled_for_apply_resolves_param_target_when_transition_name_is_shared() {
        // entity Job { triggered: Bool action toggle() requires not triggered { triggered' = true } }
        let job = IREntity {
            name: "Job".to_owned(),
            fields: vec![IRField {
                name: "triggered".to_owned(),
                ty: IRType::Bool,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "toggle".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Var {
                        name: "triggered".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "triggered".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        // entity Worker { busy: Bool action toggle() requires not busy { busy' = true } }
        // The transition name `toggle` is shared with Job. Without proper
        // var_to_entity-style resolution, the enabledness encoder's
        // unique-transition fallback returns None and silently skips the
        // body precondition.
        let worker = IREntity {
            name: "Worker".to_owned(),
            fields: vec![IRField {
                name: "busy".to_owned(),
                ty: IRType::Bool,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![IRTransition {
                name: "toggle".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Var {
                        name: "busy".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "busy".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };

        // event tick(j: Job) { j.toggle() }
        let tick = IRStep {
            name: "tick".to_owned(),
            params: vec![IRTransParam {
                name: "j".to_owned(),
                ty: IRType::Entity {
                    name: "Job".to_owned(),
                },
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Apply {
                target: "j".to_owned(),
                transition: "toggle".to_owned(),
                refs: vec![],
                args: vec![],
            }],
            return_expr: None,
        };

        let vctx = make_account_vctx();
        let mut scopes = HashMap::new();
        scopes.insert("Job".to_owned(), 1);
        scopes.insert("Worker".to_owned(), 1);
        let pool = create_slot_pool(&[job.clone(), worker.clone()], &scopes, 1);

        // Job slot 0 is active and ALREADY triggered (so toggle's guard fails).
        // Worker slot 0 is active and not busy (so Worker::toggle's guard would
        // succeed, but tick(j: Job) should target Job, not Worker).
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(j0)) = pool.active_at("Job", 0, 0) {
            solver.assert(j0);
        }
        if let Some(SmtValue::Bool(w0)) = pool.active_at("Worker", 0, 0) {
            solver.assert(w0);
        }
        if let Some(SmtValue::Bool(jt0)) = pool.field_at("Job", 0, "triggered", 0) {
            solver.assert(jt0); // Job is already triggered
        }
        if let Some(SmtValue::Bool(wb0)) = pool.field_at("Worker", 0, "busy", 0) {
            solver.assert(smt::bool_not(&wb0)); // Worker is not busy
        }

        // tick(j=0) should be DISABLED because Job slot 0's `not triggered`
        // guard fails. If the enabledness encoder confuses Job::toggle with
        // Worker::toggle (unique-transition fallback fails because there
        // are TWO entities with `toggle`), it will silently drop the
        // precondition and report enablement as true.
        let mut params_for_j_0 = HashMap::new();
        params_for_j_0.insert("j".to_owned(), smt::int_val(0));
        let enabled_with_j_0 = encode_step_enabled_with_params(
            &pool,
            &vctx,
            &[job.clone(), worker.clone()],
            &[],
            &tick,
            0,
            params_for_j_0,
        );
        solver.assert(&enabled_with_j_0);
        assert_eq!(
            solver.check(),
            SatResult::Unsat,
            "tick(j=0) must resolve to Job::toggle (not Worker::toggle) and report DISABLED"
        );
    }
}
