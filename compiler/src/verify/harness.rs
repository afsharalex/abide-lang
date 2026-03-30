//! Bounded verification harness — multi-slot entity pools with time-stepped variables.
//!
//! Implements the Alloy-style bounded model: each entity type has N slots
//! (from scope), each with an `active` flag and field variables per time step.
//! Actions are transition relations, events compose actions, and the harness
//! assembles domain/transition/frame/initial constraints for the solver.

use std::collections::{HashMap, HashSet};

use z3::ast::{Bool, Int};
use z3::Sort;

use crate::ir::types::{
    IRAction, IREntity, IREvent, IRExpr, IRSystem, IRTransParam, IRTransition, IRType, LitVal,
};

use super::context::VerifyContext;
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
                            IRType::Map { .. } | IRType::Set { .. } | IRType::Seq { .. } => {
                                smt::array_var(&name, &field.ty)
                                    .expect("internal: array sort expected for Map/Set/Seq field")
                            }
                            _ => smt::int_var(&name),
                        }
                    })
                    .collect();
                field_vars.insert((entity.name.clone(), slot, field.name.clone()), vars);
            }
        }
    }

    SlotPool {
        field_vars,
        active_vars,
        pool_sizes,
        bound,
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
                                constraints.push(var.ge(Int::from_i64(min_id)));
                                constraints.push(var.le(Int::from_i64(max_id)));
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
            constraints.push(active_t0.not());
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
                    // ¬active[i] → ¬active[i+1]  ≡  active[i+1] → active[i]
                    constraints.push(act_j.implies(act_i));
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
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let ctx = SlotEncodeCtx {
        pool,
        vctx,
        entity: &entity.name,
        slot,
        params: params.clone(),
        bindings: HashMap::new(),
    };

    let mut conjuncts = Vec::new();

    // Guard: encode the requires clause for this slot at this step
    let guard = encode_slot_expr(&ctx, &action.guard, step);
    conjuncts.push(guard.to_bool().expect("internal: guard to_bool"));

    // Updates: for each primed assignment, set the field at step+1
    let updated_fields: Vec<String> = action.updates.iter().map(|u| u.field.clone()).collect();

    for update in &action.updates {
        let new_val = encode_slot_expr(&ctx, &update.value, step);
        if let Some(field_next) = pool.field_at(&entity.name, slot, &update.field, step + 1) {
            conjuncts.push(smt::smt_eq(&new_val, field_next).expect("internal: update smt_eq"));
        }
    }

    // Frame: fields NOT in updates stay the same
    for field in &entity.fields {
        if !updated_fields.contains(&field.name) {
            if let (Some(curr), Some(next)) = (
                pool.field_at(&entity.name, slot, &field.name, step),
                pool.field_at(&entity.name, slot, &field.name, step + 1),
            ) {
                conjuncts.push(smt::smt_eq(curr, next).expect("internal: frame smt_eq"));
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

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    Bool::and(&refs)
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
    // Build a context that resolves field names from read_vars
    let mut conjuncts = Vec::new();

    // Guard: evaluate against read_vars
    let guard = eval_expr_with_vars(&action.guard, entity, read_vars, vctx, params);
    conjuncts.push(guard.to_bool().expect("internal: chained guard to_bool"));

    // Updates: evaluate value from read_vars, constrain write_vars
    let updated_fields: Vec<String> = action.updates.iter().map(|u| u.field.clone()).collect();
    for update in &action.updates {
        let new_val = eval_expr_with_vars(&update.value, entity, read_vars, vctx, params);
        if let Some(write_val) = write_vars.get(&update.field) {
            conjuncts
                .push(smt::smt_eq(&new_val, write_val).expect("internal: chained update smt_eq"));
        }
    }

    // Frame: fields NOT in updates copied from read to write
    for field in &entity.fields {
        if !updated_fields.contains(&field.name) {
            if let (Some(read_val), Some(write_val)) =
                (read_vars.get(&field.name), write_vars.get(&field.name))
            {
                conjuncts.push(
                    smt::smt_eq(read_val, write_val).expect("internal: chained frame smt_eq"),
                );
            }
        }
    }

    if conjuncts.is_empty() {
        return Bool::from_bool(true);
    }
    let refs: Vec<&Bool> = conjuncts.iter().collect();
    Bool::and(&refs)
}

/// Evaluate an IR expression using explicit variable maps instead of `SlotPool`.
///
/// Resolves field names from `vars` (a map of `field_name` → `SmtValue`).
/// Falls back to `params` for action parameters.
#[allow(clippy::only_used_in_recursion)]
fn eval_expr_with_vars(
    expr: &IRExpr,
    entity: &IREntity,
    vars: &HashMap<String, SmtValue>,
    vctx: &VerifyContext,
    params: &HashMap<String, SmtValue>,
) -> SmtValue {
    match expr {
        IRExpr::Lit { value, .. } => encode_slot_literal(value),
        IRExpr::Var { name, .. } => {
            if let Some(val) = params.get(name) {
                return val.clone();
            }
            if let Some(val) = vars.get(name) {
                return val.clone();
            }
            panic!("variable not found in chained encoding: {name}")
        }
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                // Qualified lookup in params (cross-entity or event-level refs)
                let qualified = format!("{name}.{field}");
                if let Some(val) = params.get(&qualified) {
                    return val.clone();
                }
                // Same-entity field: only resolve from vars (intermediate state)
                if let Some(val) = vars.get(field) {
                    return val.clone();
                }
                // Check unqualified in params as last resort
                if let Some(val) = params.get(field) {
                    return val.clone();
                }
            }
            // No blind fallback — strict resolution only
            panic!(
                "field {field} not found in chained encoding (vars: {:?}, params: {:?})",
                vars.keys().collect::<Vec<_>>(),
                params.keys().collect::<Vec<_>>()
            )
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.id_of(enum_name, ctor);
            smt::int_val(id)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = eval_expr_with_vars(left, entity, vars, vctx, params);
            let r = eval_expr_with_vars(right, entity, vars, vctx, params);
            smt::binop(op, &l, &r).expect("internal: chained binop")
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = eval_expr_with_vars(operand, entity, vars, vctx, params);
            smt::unop(op, &v).expect("internal: chained unop")
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = eval_expr_with_vars(map, entity, vars, vctx, params);
            let k = eval_expr_with_vars(key, entity, vars, vctx, params);
            let v = eval_expr_with_vars(value, entity, vars, vctx, params);
            SmtValue::Array(
                arr.as_array()
                    .expect("internal: chained map update as_array")
                    .store(&k.to_dynamic(), &v.to_dynamic()),
            )
        }
        IRExpr::Index { map, key, .. } => {
            let arr = eval_expr_with_vars(map, entity, vars, vctx, params);
            let k = eval_expr_with_vars(key, entity, vars, vctx, params);
            SmtValue::Dynamic(
                arr.as_array()
                    .expect("internal: chained index as_array")
                    .select(&k.to_dynamic()),
            )
        }
        _ => panic!(
            "unsupported expression in chained action encoding: {:?}",
            std::mem::discriminant(expr)
        ),
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
    event_params: &HashMap<String, SmtValue>,
) -> Bool {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let n_slots = pool.slots_for(entity_name);
    let mut slot_disjuncts = Vec::new();

    for slot in 0..n_slots {
        let ctx = SlotEncodeCtx {
            pool,
            vctx,
            entity: entity_name,
            slot,
            params: event_params.clone(),
            bindings: HashMap::new(),
        };

        let mut conjuncts = Vec::new();

        // Slot must be inactive at current step
        if let Some(SmtValue::Bool(act_curr)) = pool.active_at(entity_name, slot, step) {
            conjuncts.push(act_curr.not());
        }
        // Activate at next step
        if let Some(SmtValue::Bool(act_next)) = pool.active_at(entity_name, slot, step + 1) {
            conjuncts.push(act_next.clone());
        }

        // Set field values at next step from create block
        let create_field_names: HashSet<&str> =
            create_fields.iter().map(|(n, _)| n.as_str()).collect();
        for (field_name, value_expr) in create_fields {
            let val = encode_slot_expr(&ctx, value_expr, step);
            if let Some(field_next) = pool.field_at(entity_name, slot, field_name, step + 1) {
                conjuncts
                    .push(smt::smt_eq(&val, field_next).expect("internal: create field smt_eq"));
            }
        }

        // Apply entity defaults for fields NOT specified in the create block.
        // Without this, unconstrained fields could take any value, making the
        // verification overly permissive.
        if let Some(ent) = entity_ir {
            for field in &ent.fields {
                if create_field_names.contains(field.name.as_str()) {
                    continue; // already set by create block
                }
                if let Some(ref default_expr) = field.default {
                    let val = encode_slot_expr(&ctx, default_expr, step);
                    if let Some(field_next) =
                        pool.field_at(entity_name, slot, &field.name, step + 1)
                    {
                        conjuncts.push(
                            smt::smt_eq(&val, field_next).expect("internal: create default smt_eq"),
                        );
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
            slot_disjuncts.push(Bool::and(&refs));
        }
    }

    // Any slot can be chosen for creation
    let refs: Vec<&Bool> = slot_disjuncts.iter().collect();
    if refs.is_empty() {
        Bool::from_bool(false) // no slots available
    } else {
        Bool::or(&refs)
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
                conjuncts.push(next.eq(curr.clone()));
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
    Bool::and(&refs)
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
                conjuncts.push(next.eq(curr.clone()));
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
            conjuncts.push(next.eq(curr.clone()));
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

/// Build a `HashMap<String, SmtValue>` mapping action parameter names to Z3 values
/// from the positional `args` and `refs` of an `Apply` action.
///
/// `action.params[i].name` maps to `encode(args[i])`, and `action.refs[i].name` maps
/// to the slot-resolved value for the entity variable name in `refs[i]`.
fn build_apply_params(
    ctx: &SlotEncodeCtx<'_>,
    action: &IRTransition,
    args: &[IRExpr],
    refs: &[String],
    step: usize,
) -> HashMap<String, SmtValue> {
    let mut map = HashMap::new();

    // Wire positional args to action params
    for (param, arg_expr) in action.params.iter().zip(args.iter()) {
        let val = encode_slot_expr(ctx, arg_expr, step);
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

    map
}

/// Build a `HashMap<String, SmtValue>` of Z3 variables for event parameters.
///
/// Each parameter gets a fresh Z3 variable named `param_{name}_{step}`, scoped
/// to the given step so that parameter values are independent across steps.
fn build_event_params(params: &[IRTransParam], step: usize) -> HashMap<String, SmtValue> {
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
}

impl GuardCtx {
    fn with_binding(&self, var: &str, entity: &str, slot: usize) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(var.to_owned(), (entity.to_owned(), slot));
        Self {
            bindings,
            params: self.params.clone(),
        }
    }
}

/// Encode an event guard expression, expanding entity quantifiers over slots.
///
/// Uses `GuardCtx` to track entity bindings from enclosing quantifiers,
/// ensuring that field references resolve correctly across nested quantifiers.
fn encode_guard_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    expr: &IRExpr,
    event_params: &HashMap<String, SmtValue>,
    step: usize,
) -> Bool {
    let ctx = GuardCtx {
        bindings: HashMap::new(),
        params: event_params.clone(),
    };
    encode_guard_inner(pool, vctx, &ctx, expr, step)
}

fn encode_guard_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> Bool {
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
                let body_val = encode_guard_inner(pool, vctx, &inner_ctx, body, step);
                if let Some(SmtValue::Bool(act)) = active {
                    disjuncts.push(Bool::and(&[act, &body_val]));
                }
            }
            if disjuncts.is_empty() {
                return Bool::from_bool(false);
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Bool::or(&refs)
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
                let body_val = encode_guard_inner(pool, vctx, &inner_ctx, body, step);
                if let Some(SmtValue::Bool(act)) = active {
                    conjuncts.push(act.implies(&body_val));
                }
            }
            if conjuncts.is_empty() {
                return Bool::from_bool(true);
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Bool::and(&refs)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" => {
            let l = encode_guard_inner(pool, vctx, ctx, left, step);
            let r = encode_guard_inner(pool, vctx, ctx, right, step);
            match op.as_str() {
                "OpAnd" => Bool::and(&[&l, &r]),
                "OpOr" => Bool::or(&[&l, &r]),
                "OpImplies" => l.implies(&r),
                _ => unreachable!(),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            encode_guard_inner(pool, vctx, ctx, operand, step).not()
        }
        IRExpr::Lit {
            value: LitVal::Bool { value },
            ..
        } => Bool::from_bool(*value),
        // Non-boolean expressions (comparisons, field access, etc.) —
        // encode as value using the guard context bindings
        other => encode_guard_value(pool, vctx, ctx, other, step)
            .to_bool()
            .expect("internal: guard to_bool"),
    }
}

/// Encode a value expression within a guard context.
/// Resolves field references using the guard's entity bindings.
fn encode_guard_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    ctx: &GuardCtx,
    expr: &IRExpr,
    step: usize,
) -> SmtValue {
    match expr {
        IRExpr::Lit { value, .. } => encode_slot_literal(value),
        IRExpr::Var { name, .. } => {
            // Check event params first
            if let Some(val) = ctx.params.get(name.as_str()) {
                return val.clone();
            }
            // Check entity bindings (last-bound entity for bare field names)
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, name, step) {
                    return val.clone();
                }
            }
            panic!(
                "guard variable not found: {name} (bindings: {:?})",
                ctx.bindings.keys().collect::<Vec<_>>()
            )
        }
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            // Resolve receiver variable to entity/slot via bindings
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                if let Some((entity, slot)) = ctx.bindings.get(name.as_str()) {
                    if let Some(val) = pool.field_at(entity, *slot, field, step) {
                        return val.clone();
                    }
                }
            }
            // Fallback: try all bindings
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, field, step) {
                    return val.clone();
                }
            }
            panic!("guard field not found: {field}")
        }
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = vctx.variants.id_of(enum_name, ctor);
            smt::int_val(id)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_guard_value(pool, vctx, ctx, left, step);
            let r = encode_guard_value(pool, vctx, ctx, right, step);
            smt::binop(op, &l, &r).expect("internal: guard binop")
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = encode_guard_value(pool, vctx, ctx, operand, step);
            smt::unop(op, &v).expect("internal: guard unop")
        }
        IRExpr::Prime { expr, .. } => encode_guard_value(pool, vctx, ctx, expr, step + 1),
        other => panic!("unsupported expression in guard value encoding: {other:?}"),
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
pub fn encode_event(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IREvent,
    step: usize,
) -> Bool {
    let (formula, touched) =
        encode_event_inner(pool, vctx, entities, all_systems, event, step, 0, None);
    apply_global_frame(pool, entities, &touched, step, formula)
}

/// Encode an event with specific parameter values (for scene checking).
///
/// Scene events supply concrete argument values (resolved from given bindings)
/// rather than fresh unconstrained Z3 variables.
#[allow(clippy::implicit_hasher)]
pub fn encode_event_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IREvent,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Bool {
    let (formula, touched) = encode_event_inner(
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
fn apply_global_frame(
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
    Bool::and(&refs)
}

/// Inner recursive implementation of `encode_event` with depth tracking
/// to prevent infinite loops from cyclic cross-system calls.
///
/// Returns `(action_formula, touched_slots)` — the formula describing the
/// event's effects WITHOUT global framing, plus the set of entity slots
/// modified by the event. Global framing is applied once by the top-level
/// caller (`encode_event` / `encode_event_with_params`), NOT inside
/// recursive `CrossCall` invocations.
///
/// `override_params` allows callers (e.g., `CrossCall`) to supply pre-built
/// Z3 values for the target event's parameters, wiring the caller's args
/// into the target event instead of creating fresh unconstrained variables.
#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
fn encode_event_inner(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IREvent,
    step: usize,
    depth: usize,
    override_params: Option<HashMap<String, SmtValue>>,
) -> (Bool, HashSet<(String, usize)>) {
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
    let event_params = override_params.unwrap_or_else(|| build_event_params(&event.params, step));

    // Event guard encoding with support for quantifiers over entity slots.
    // For guards that are trivially `true`, skip encoding.
    // For non-trivial guards, use `encode_guard_expr` which handles:
    // - Quantifiers (`exists o: Order | ...`, `forall o: Order | ...`) by
    //   expanding over active slots
    // - Boolean connectives by recursing
    // - Param-only or literal guards via `encode_slot_expr` with event params
    if !matches!(
        &event.guard,
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        }
    ) {
        let guard = encode_guard_expr(pool, vctx, &event.guard, &event_params, step);
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

    // Accumulated Choose variable params: after a `choose r: Reservation ...`
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
                let mut merged_params = event_params.clone();
                merged_params.extend(choose_var_params.clone());

                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: merged_params.clone(),
                        bindings: HashMap::new(),
                    };

                    let mut slot_conjuncts = Vec::new();

                    // Must be active
                    if let Some(SmtValue::Bool(active)) = pool.active_at(ent_name, slot, step) {
                        slot_conjuncts.push(active.clone());
                    }

                    // Filter must hold
                    let filt = encode_slot_expr(&ctx, filter, step);
                    slot_conjuncts.push(filt.to_bool().expect("internal: choose filter to_bool"));

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
                                            let action_params = build_apply_params(
                                                &ctx, trans, args, apply_refs, step,
                                            );
                                            let action_formula = encode_action(
                                                pool,
                                                vctx,
                                                ent,
                                                trans,
                                                slot,
                                                step,
                                                &action_params,
                                            );
                                            slot_conjuncts.push(action_formula);
                                        }
                                    }
                                    _ => {
                                        unimplemented!(
                                            "nested action in Choose not yet supported: {op:?}"
                                        )
                                    }
                                }
                            }
                        } else {
                            // Multi-apply chain — create intermediate variables.
                            // Chain: step_k → inter_0 → inter_1 → ... → step_k+1
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
                                                IRType::Map { .. }
                                                | IRType::Set { .. }
                                                | IRType::Seq { .. } => {
                                                    smt::array_var(&name, &f.ty)
                                                        .expect("internal: array sort expected for Map/Set/Seq field")
                                                }
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
                                    build_apply_params(&ctx, trans, args, apply_refs, step)
                                } else {
                                    let mut params = HashMap::new();
                                    // Positional params
                                    for (pi, param) in trans.params.iter().enumerate() {
                                        if let Some(arg_expr) = args.get(pi) {
                                            let val = eval_expr_with_vars(
                                                arg_expr,
                                                ent,
                                                read_from,
                                                vctx,
                                                &ctx.params,
                                            );
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

                                let formula = encode_action_with_vars(
                                    ent,
                                    trans,
                                    slot,
                                    read_from,
                                    write_to,
                                    vctx,
                                    &action_params,
                                );
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
                                        unimplemented!(
                                            "nested action in Choose not yet supported: {op:?}"
                                        )
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
                                        slot_conjuncts.push(s.eq(f.clone()));
                                    }
                                    (SmtValue::Bool(s), SmtValue::Bool(f)) => {
                                        slot_conjuncts.push(s.eq(f.clone()));
                                    }
                                    (SmtValue::Real(s), SmtValue::Real(f)) => {
                                        slot_conjuncts.push(s.eq(f.clone()));
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
                        slot_options.push(Bool::and(&refs));
                    }
                }

                // At least one slot must satisfy Choose
                let refs: Vec<&Bool> = slot_options.iter().collect();
                if !refs.is_empty() {
                    conjuncts.push(Bool::or(&refs));
                    for slot in 0..n_slots {
                        touched.insert((ent_name.clone(), slot));
                    }
                }

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
                let mut slot_options = Vec::new();
                for slot in 0..n_slots {
                    let apply_ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: {
                            let mut p = event_params.clone();
                            p.extend(choose_var_params.clone());
                            p
                        },
                        bindings: HashMap::new(),
                    };
                    let action_params =
                        build_apply_params(&apply_ctx, trans, args, apply_refs, step);
                    let mut slot_conjuncts = Vec::new();
                    let formula = encode_action(pool, vctx, ent, trans, slot, step, &action_params);
                    slot_conjuncts.push(formula);
                    // Frame all OTHER slots of this entity
                    let slot_frame = frame_entity_slots_except(pool, ent, slot, step);
                    slot_conjuncts.extend(slot_frame);
                    let refs: Vec<&Bool> = slot_conjuncts.iter().collect();
                    slot_options.push(Bool::and(&refs));
                }
                let refs: Vec<&Bool> = slot_options.iter().collect();
                if !refs.is_empty() {
                    conjuncts.push(Bool::or(&refs));
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
                let create = encode_create(
                    pool,
                    vctx,
                    ent_name,
                    entity_ir,
                    &create_fields,
                    step,
                    &event_params,
                );
                conjuncts.push(create);
                // Mark all slots of this entity as potentially touched
                let n_slots = pool.slots_for(ent_name);
                for slot in 0..n_slots {
                    touched.insert((ent_name.clone(), slot));
                }
            }

            // Issue 2: ForAll encoding — conjunction over all active slots.
            // For each slot:
            //   (active AND ops AND active_next) OR (!active AND frame_this_slot)
            // This ensures inactive slots are explicitly framed (not left unconstrained).
            IRAction::ForAll {
                var: _,
                entity: ent_name,
                ops,
            } => {
                let n_slots = pool.slots_for(ent_name);
                let entity_ir = entities.iter().find(|e| e.name == *ent_name);

                for slot in 0..n_slots {
                    let ctx = SlotEncodeCtx {
                        pool,
                        vctx,
                        entity: ent_name,
                        slot,
                        params: {
                            let mut p = event_params.clone();
                            p.extend(choose_var_params.clone());
                            p
                        },
                        bindings: HashMap::new(),
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
                                        let action_params =
                                            build_apply_params(&ctx, trans, args, apply_refs, step);
                                        let action_formula = encode_action(
                                            pool,
                                            vctx,
                                            ent,
                                            trans,
                                            slot,
                                            step,
                                            &action_params,
                                        );
                                        op_conjuncts.push(action_formula);
                                    }
                                }
                            }
                            _ => {
                                unimplemented!("nested action in ForAll not yet supported: {op:?}")
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
                            Bool::and(&refs)
                        };

                        // Inactive branch: !active AND frame (all fields + active flag unchanged)
                        let mut frame_parts = vec![active.not()];
                        // Active flag unchanged
                        if let Some(SmtValue::Bool(act_next)) =
                            pool.active_at(ent_name, slot, step + 1)
                        {
                            frame_parts.push(act_next.eq(active.clone()));
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
                        let inactive_branch = Bool::and(&frame_refs);

                        conjuncts.push(Bool::or(&[&active_branch, &inactive_branch]));
                    }

                    touched.insert((ent_name.clone(), slot));
                }
            }

            IRAction::CrossCall {
                system: target_system,
                event: event_name,
                args: cross_args,
            } => {
                // Find the target system and its event, then encode it inline.
                // Wire CrossCall args into the target event's parameters so that
                // the target event uses the caller's values, not fresh variables.
                if let Some(target_sys) = all_systems.iter().find(|s| s.name == *target_system) {
                    if let Some(target_event) =
                        target_sys.events.iter().find(|e| e.name == *event_name)
                    {
                        // Build override params: evaluate each CrossCall arg in
                        // the current event's context (using event_params) and
                        // bind it to the corresponding target event param name.
                        let mut cross_params: HashMap<String, SmtValue> = HashMap::new();
                        let arg_ctx = SlotEncodeCtx {
                            pool,
                            vctx,
                            entity: "",
                            slot: 0,
                            params: {
                                let mut p = event_params.clone();
                                p.extend(choose_var_params.clone());
                                p
                            },
                            bindings: HashMap::new(),
                        };
                        if target_event.params.len() != cross_args.len() {
                            // Arity mismatches are validated in scene checking,
                            // but keep harness encoding total so verify checks
                            // never panic during recursive CrossCall expansion.
                            conjuncts.push(Bool::from_bool(false));
                            continue;
                        }
                        for (target_param, arg_expr) in
                            target_event.params.iter().zip(cross_args.iter())
                        {
                            let val = encode_slot_expr(&arg_ctx, arg_expr, step);
                            cross_params.insert(target_param.name.clone(), val);
                        }

                        // Recursively encode the target event with wired params.
                        // Merge the callee's touched set into ours — this is the key
                        // fix for CrossCall framing: the callee does NOT apply its own
                        // global frame, so there's no conflict with our modifications.
                        let (cross_formula, cross_touched) = encode_event_inner(
                            pool,
                            vctx,
                            entities,
                            all_systems,
                            target_event,
                            step,
                            depth + 1,
                            Some(cross_params),
                        );
                        conjuncts.push(cross_formula);
                        // Merge callee's actual touched slots (not coarse system-level)
                        touched.extend(cross_touched);
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
                        let mut p = event_params.clone();
                        p.extend(choose_var_params.clone());
                        p
                    },
                    bindings: HashMap::new(),
                };
                let val = encode_slot_expr(&expr_ctx, expr, step);
                conjuncts.push(val.to_bool().expect("internal: expr_stmt to_bool"));
            }
        }
    }

    // Postcondition: if the event has an `ensures` clause, assert it at step+1.
    // The postcondition is a constraint on the post-state that the event guarantees.
    if let Some(post) = &event.postcondition {
        let post_guard = encode_guard_expr(pool, vctx, post, &event_params, step + 1);
        conjuncts.push(post_guard);
    }

    // Return action formula + touched set. Global framing is applied by the
    // top-level caller, NOT here — this allows CrossCall to compose without
    // conflicting frame constraints.
    let formula = {
        let refs: Vec<&Bool> = conjuncts.iter().collect();
        if refs.is_empty() {
            Bool::from_bool(true)
        } else {
            Bool::and(&refs)
        }
    };
    (formula, touched)
}

// ── Transition relation ─────────────────────────────────────────────

/// Generate the full transition relation at a given step.
///
/// At each step, exactly one of the following happens:
/// - One of the system events fires (disjunction over all events)
/// - Stutter (idle — nothing changes)
///
/// Returns: `event_1(step) OR event_2(step) OR ... OR stutter(step)`
pub fn transition_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    systems: &[IRSystem],
    step: usize,
) -> Bool {
    assert!(
        step < pool.bound,
        "step {step} out of bounds for bound {}",
        pool.bound
    );

    let mut disjuncts = Vec::new();

    // Each system event is a possible transition
    for system in systems {
        for event in &system.events {
            let event_formula = encode_event(pool, vctx, entities, systems, event, step);
            disjuncts.push(event_formula);
        }
    }

    // Stutter: nothing changes
    let stutter = stutter_constraint(pool, entities, step);
    disjuncts.push(stutter);

    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Bool::or(&refs)
}

// ── Slot-scoped expression encoding ─────────────────────────────────

/// Encode an IR expression with a specific entity slot in scope.
///
/// Variable and field references resolve to `entity_s{slot}_{field}_t{step}`.
/// Parameters (from action/event signatures) are checked first, then slot fields.
#[allow(clippy::too_many_lines)]
pub fn encode_slot_expr(ctx: &SlotEncodeCtx<'_>, expr: &IRExpr, step: usize) -> SmtValue {
    match expr {
        IRExpr::Lit { value, .. } => encode_slot_literal(value),

        IRExpr::Var { name, .. } => {
            // Check action/event parameters first
            if let Some(val) = ctx.params.get(name) {
                return val.clone();
            }
            // Resolve to this slot's field variable
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, name, step) {
                return val.clone();
            }
            // Try cross-entity bindings (from prior Choose blocks)
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = ctx.pool.field_at(entity, *slot, name, step) {
                    return val.clone();
                }
            }
            panic!(
                "slot variable not found: {}.{name} slot={} step={step}",
                ctx.entity, ctx.slot
            );
        }

        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = ctx.vctx.variants.id_of(enum_name, ctor);
            smt::int_val(id)
        }

        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_slot_expr(ctx, left, step);
            let r = encode_slot_expr(ctx, right, step);
            smt::binop(op, &l, &r).expect("internal: slot binop")
        }

        IRExpr::UnOp { op, operand, .. } => {
            let v = encode_slot_expr(ctx, operand, step);
            smt::unop(op, &v).expect("internal: slot unop")
        }

        IRExpr::Field {
            expr: recv, field, ..
        } => {
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                // Check shared Choose variable params: `var.field` → shared Z3 var
                let qualified = format!("{name}.{field}");
                if let Some(val) = ctx.params.get(&qualified) {
                    return val.clone();
                }
                // Check cross-entity bindings (e.g., r.product_id where
                // r is from a prior Choose over Reservation)
                if let Some((entity, slot)) = ctx.bindings.get(name.as_str()) {
                    if let Some(val) = ctx.pool.field_at(entity, *slot, field, step) {
                        return val.clone();
                    }
                }
            }
            // Fall back to current entity context
            if let Some(val) = ctx.pool.field_at(ctx.entity, ctx.slot, field, step) {
                return val.clone();
            }
            panic!(
                "slot field not found: {}.{field} slot={} step={step}",
                ctx.entity, ctx.slot
            );
        }

        IRExpr::Prime { expr, .. } => encode_slot_expr(ctx, expr, step + 1),

        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = encode_slot_expr(ctx, map, step);
            let k = encode_slot_expr(ctx, key, step);
            let v = encode_slot_expr(ctx, value, step);
            SmtValue::Array(
                arr.as_array()
                    .expect("internal: slot map update as_array")
                    .store(&k.to_dynamic(), &v.to_dynamic()),
            )
        }

        IRExpr::Index { map, key, .. } => {
            let arr = encode_slot_expr(ctx, map, step);
            let k = encode_slot_expr(ctx, key, step);
            SmtValue::Dynamic(
                arr.as_array()
                    .expect("internal: slot index as_array")
                    .select(&k.to_dynamic()),
            )
        }

        IRExpr::MapLit { entries, ty, .. } => {
            // Build constant array with default value, then store each entry
            let (key_ty, val_ty) = match ty {
                IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
                _ => panic!("MapLit with non-Map type: {ty:?}"),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default_val = smt::default_dynamic(val_ty);
            let mut arr = z3::ast::Array::const_array(&key_sort, &default_val);
            for entry in entries {
                let k = encode_slot_expr(ctx, &entry.0, step);
                let v = encode_slot_expr(ctx, &entry.1, step);
                arr = arr.store(&k.to_dynamic(), &v.to_dynamic());
            }
            SmtValue::Array(arr)
        }

        IRExpr::SetLit { elements, ty, .. } => {
            // Set as characteristic function: Array<T, Bool>
            let elem_ty = match ty {
                IRType::Set { element } => element.as_ref(),
                _ => panic!("SetLit with non-Set type: {ty:?}"),
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_val = smt::bool_val(false).to_dynamic();
            let mut arr = z3::ast::Array::const_array(&elem_sort, &false_val);
            let true_val = smt::bool_val(true).to_dynamic();
            for elem in elements {
                let e = encode_slot_expr(ctx, elem, step);
                arr = arr.store(&e.to_dynamic(), &true_val);
            }
            SmtValue::Array(arr)
        }

        IRExpr::SeqLit { elements, ty, .. } => {
            // Seq as int-indexed array: Array<Int, T>
            let elem_ty = match ty {
                IRType::Seq { element } => element.as_ref(),
                _ => panic!("SeqLit with non-Seq type: {ty:?}"),
            };
            let default_val = smt::default_dynamic(elem_ty);
            let mut arr = z3::ast::Array::const_array(&Sort::int(), &default_val);
            for (i, elem) in elements.iter().enumerate() {
                let idx = smt::int_val(i64::try_from(i).unwrap_or(0)).to_dynamic();
                let v = encode_slot_expr(ctx, elem, step);
                arr = arr.store(&idx, &v.to_dynamic());
            }
            SmtValue::Array(arr)
        }

        IRExpr::Card { expr: inner, .. } => match inner.as_ref() {
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
            _ => panic!(
                "unsupported cardinality in action context — \
                 should be caught by pre-check: {inner:?}"
            ),
        },

        other => unimplemented!("slot expression encoding not yet supported: {other:?}"),
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
mod tests {
    use super::*;
    use crate::ir::types::{IRField, IRUpdate};
    use z3::Solver;

    fn make_order_entity() -> IREntity {
        IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Enum {
                        name: "OrderStatus".to_owned(),
                        constructors: vec![
                            "Pending".to_owned(),
                            "Confirmed".to_owned(),
                            "Shipped".to_owned(),
                        ],
                    },
                    default: None,
                },
                IRField {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    default: None,
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

                        span: None,
                    },
                }],
                postcondition: None,
            }],
        }
    }

    fn make_vctx() -> VerifyContext {
        let mut vctx = VerifyContext {
            variants: super::super::context::VariantMap::new(),
            enum_ranges: HashMap::new(),
            entities: HashMap::new(),
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
        vctx
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

        let solver = Solver::new();
        // Slot is active
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
            solver.assert(active);
        }
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 1) {
            solver.assert(active);
        }
        // Status = Pending at step 0
        if let SmtValue::Int(s) = status_t0 {
            solver.assert(&s.eq(Int::from_i64(pending_id)));
        }

        // Encode and assert the action
        let no_params = HashMap::new();
        let formula = encode_action(&pool, &vctx, &entity, action, 0, 0, &no_params);
        solver.assert(&formula);

        assert_eq!(solver.check(), z3::SatResult::Sat);

        // Verify: status at step 1 should be Confirmed
        let confirmed_id = vctx.variants.id_of("OrderStatus", "Confirmed");
        let status_t1 = pool.field_at("Order", 0, "status", 1).unwrap();
        solver.push();
        if let SmtValue::Int(s) = status_t1 {
            solver.assert(&s.eq(Int::from_i64(confirmed_id)));
        }
        assert_eq!(solver.check(), z3::SatResult::Sat);
        solver.pop(1);

        // Verify: status at step 1 should NOT be Pending
        solver.push();
        if let SmtValue::Int(s) = status_t1 {
            solver.assert(&s.eq(Int::from_i64(pending_id)));
        }
        assert_eq!(solver.check(), z3::SatResult::Unsat);
        solver.pop(1);
    }

    #[test]
    fn stutter_preserves_state() {
        let entity = make_order_entity();
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 1);
        let pool = create_slot_pool(&[entity.clone()], &scopes, 1);

        let stutter = stutter_constraint(&pool, &[entity], 0);

        let solver = Solver::new();
        // Set status at step 0
        if let Some(SmtValue::Int(s0)) = pool.field_at("Order", 0, "status", 0) {
            solver.assert(&s0.eq(Int::from_i64(42)));
        }
        solver.assert(&stutter);

        // Status at step 1 should equal step 0
        if let Some(SmtValue::Int(s1)) = pool.field_at("Order", 0, "status", 1) {
            solver.push();
            solver.assert(&s1.eq(Int::from_i64(42)));
            assert_eq!(solver.check(), z3::SatResult::Sat);
            solver.pop(1);

            solver.push();
            solver.assert(&s1.eq(Int::from_i64(99)));
            assert_eq!(solver.check(), z3::SatResult::Unsat);
            solver.pop(1);
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
        }
    }

    fn make_account_vctx() -> VerifyContext {
        VerifyContext {
            variants: super::super::context::VariantMap::new(),
            enum_ranges: HashMap::new(),
            entities: HashMap::new(),
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

        let solver = Solver::new();
        // Slot is active
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 0) {
            solver.assert(active);
        }
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 1) {
            solver.assert(active);
        }
        // Balance = 50 at step 0
        if let Some(SmtValue::Int(b0)) = pool.field_at("Account", 0, "balance", 0) {
            solver.assert(&b0.eq(Int::from_i64(50)));
        }

        let formula = encode_action(&pool, &vctx, &entity, action, 0, 0, &params);
        solver.assert(&formula);

        // Should be SAT (amount=100 > 0, balance becomes 150)
        assert_eq!(solver.check(), z3::SatResult::Sat);

        // Verify: balance at step 1 should be 150
        if let Some(SmtValue::Int(b1)) = pool.field_at("Account", 0, "balance", 1) {
            solver.push();
            solver.assert(&b1.eq(Int::from_i64(150)));
            assert_eq!(solver.check(), z3::SatResult::Sat);
            solver.pop(1);

            // balance at step 1 should NOT be 50 (unchanged)
            solver.push();
            solver.assert(&b1.eq(Int::from_i64(50)));
            assert_eq!(solver.check(), z3::SatResult::Unsat);
            solver.pop(1);
        }

        // Now test with amount = -5 (violates guard), should be UNSAT
        let mut bad_params = HashMap::new();
        bad_params.insert("amount".to_owned(), smt::int_val(-5));
        let solver2 = Solver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 0) {
            solver2.assert(active);
        }
        if let Some(SmtValue::Bool(active)) = pool.active_at("Account", 0, 1) {
            solver2.assert(active);
        }
        let formula2 = encode_action(&pool, &vctx, &entity, action, 0, 0, &bad_params);
        solver2.assert(&formula2);
        assert_eq!(solver2.check(), z3::SatResult::Unsat);
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
        let event = IREvent {
            name: "deposit_all".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            postcondition: None,
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
        };

        let solver = Solver::new();
        // Slot 0: active
        if let Some(SmtValue::Bool(a0)) = pool.active_at("Account", 0, 0) {
            solver.assert(a0);
        }
        if let Some(SmtValue::Bool(a0_next)) = pool.active_at("Account", 0, 1) {
            solver.assert(a0_next);
        }
        // Slot 1: inactive
        if let Some(SmtValue::Bool(a1)) = pool.active_at("Account", 1, 0) {
            solver.assert(&a1.not());
        }

        // Set slot 1 balance at step 0
        if let Some(SmtValue::Int(b1_t0)) = pool.field_at("Account", 1, "balance", 0) {
            solver.assert(&b1_t0.eq(Int::from_i64(200)));
        }

        // Set slot 0 balance at step 0
        if let Some(SmtValue::Int(b0_t0)) = pool.field_at("Account", 0, "balance", 0) {
            solver.assert(&b0_t0.eq(Int::from_i64(100)));
        }

        let formula = encode_event(&pool, &vctx, &[entity], &[], &event, 0);
        solver.assert(&formula);
        assert_eq!(solver.check(), z3::SatResult::Sat);

        // Inactive slot 1: balance at step 1 must equal step 0 (200)
        if let Some(SmtValue::Int(b1_t1)) = pool.field_at("Account", 1, "balance", 1) {
            solver.push();
            solver.assert(&b1_t1.eq(Int::from_i64(200)));
            assert_eq!(solver.check(), z3::SatResult::Sat);
            solver.pop(1);

            // Must NOT be possible for slot 1 balance to change
            solver.push();
            solver.assert(&b1_t1.eq(Int::from_i64(999)));
            assert_eq!(solver.check(), z3::SatResult::Unsat);
            solver.pop(1);
        }

        // Inactive slot 1: active flag at step 1 must still be false
        if let Some(SmtValue::Bool(a1_t1)) = pool.active_at("Account", 1, 1) {
            solver.push();
            solver.assert(&a1_t1.not());
            assert_eq!(solver.check(), z3::SatResult::Sat);
            solver.pop(1);

            solver.push();
            solver.assert(a1_t1);
            assert_eq!(solver.check(), z3::SatResult::Unsat);
            solver.pop(1);
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

        let solver = Solver::new();
        // Both slots inactive at step 0
        if let Some(SmtValue::Bool(a0)) = pool.active_at("Account", 0, 0) {
            solver.assert(&a0.not());
        }
        if let Some(SmtValue::Bool(a1)) = pool.active_at("Account", 1, 0) {
            solver.assert(&a1.not());
        }

        // Set slot 1 balance at step 0
        if let Some(SmtValue::Int(b1_t0)) = pool.field_at("Account", 1, "balance", 0) {
            solver.assert(&b1_t0.eq(Int::from_i64(500)));
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

        assert_eq!(solver.check(), z3::SatResult::Sat);

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
            solver.assert(&b1_t1.eq(Int::from_i64(500)));
            assert_eq!(solver.check(), z3::SatResult::Sat);
            solver.pop(1);

            solver.push();
            solver.assert(&b1_t1.eq(Int::from_i64(999)));
            assert_eq!(solver.check(), z3::SatResult::Unsat);
            solver.pop(1);
        }
        solver.pop(1);
    }
}
