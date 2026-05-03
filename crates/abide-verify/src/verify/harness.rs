//! Bounded verification harness — multi-slot entity pools with time-stepped variables.
//!
//! Implements the Alloy-style bounded model: each entity type has N slots
//! (from scope), each with an `active` flag and field variables per time step.
//! Actions are transition relations, events compose actions, and the harness
//! assembles domain/transition/frame/initial constraints for the solver.

use std::collections::{HashMap, HashSet};

use super::smt::Bool;

use crate::ir::types::{
    IRAction, IRAssumptionSet, IREntity, IRExpr, IRSystem, IRSystemAction, IRTransParam,
    IRTransition, IRType, LitVal,
};

use super::context::VerifyContext;
use super::defenv;
use super::defenv::AppHeadKind;
use super::scope::VerifyStoreRange;
use super::smt::{self, SmtValue};
mod action;
mod expr;
mod fairness;
mod framing;
mod guard;
mod step;
mod temporal;
use self::action::*;
pub use self::action::{
    encode_action, encode_action_with_vars, encode_create, try_encode_action,
    try_encode_action_with_vars, try_encode_create,
};
use self::expr::*;
pub use self::expr::{encode_slot_expr, try_encode_slot_expr};
pub use self::fairness::{fairness_constraints, try_fairness_constraints};
use self::framing::*;
pub use self::framing::{
    extract_primed_system_fields, frame_specific_slots, frame_system_fields, stutter_constraint,
    system_field_initial_constraints, try_system_field_initial_constraints,
};
pub(crate) use self::guard::try_encode_guard_expr;
use self::guard::*;
use self::step::*;
pub(crate) use self::step::{apply_global_frame, encode_step_with_params, try_encode_step_inner};
pub use self::temporal::{
    encode_step_enabled, encode_step_enabled_with_params, lasso_loopback, transition_constraints,
    transition_constraints_with_fire, try_encode_step_enabled, try_encode_step_enabled_with_params,
    try_transition_constraints_with_fire, FireTracking, LassoLoop,
};

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

/// Generate initial state constraints.
///
/// Legacy entity scopes without explicit stores start with all slots inactive.
/// Explicit store ranges start with exactly their declared lower-bound
/// population, occupying the store's first slots. Later transition constraints
/// can grow the active population up to the declared upper bound.
pub fn initial_state_constraints(
    pool: &SlotPool,
    store_ranges: &HashMap<String, VerifyStoreRange>,
) -> Vec<Bool> {
    let mut constraints = Vec::new();
    let mut explicit_initial_active: HashSet<(String, usize)> = HashSet::new();
    let mut explicit_initial_inactive: HashSet<(String, usize)> = HashSet::new();
    for range in store_ranges.values() {
        for slot in range.start_slot..range.start_slot + range.slot_count {
            let key = (range.entity_type.clone(), slot);
            if slot < range.start_slot + range.min_active {
                explicit_initial_active.insert(key);
            } else {
                explicit_initial_inactive.insert(key);
            }
        }
    }

    for ((entity, slot), actives) in &pool.active_vars {
        if let SmtValue::Bool(active_t0) = &actives[0] {
            let key = (entity.clone(), *slot);
            if explicit_initial_active.contains(&key) {
                constraints.push(active_t0.clone());
            } else if explicit_initial_inactive.contains(&key) {
                constraints.push(smt::bool_not(active_t0));
            } else {
                constraints.push(smt::bool_not(active_t0));
            }
        }
    }

    constraints
}

/// Constrain each explicit store's active population at every encoded step.
///
/// The store upper bound is also the slot capacity, so `sum <= max_active` is
/// usually tautological. Keeping it explicit makes the cardinality contract
/// local to this helper and protects future encodings that may introduce
/// deactivation or non-contiguous store ownership.
pub fn store_active_cardinality_constraints(
    pool: &SlotPool,
    store_ranges: &HashMap<String, VerifyStoreRange>,
) -> Vec<Bool> {
    let mut constraints = Vec::new();
    for range in store_ranges.values() {
        for step in 0..=pool.bound {
            let terms: Vec<_> = (range.start_slot..range.start_slot + range.slot_count)
                .filter_map(
                    |slot| match pool.active_at(&range.entity_type, slot, step) {
                        Some(SmtValue::Bool(active)) => {
                            Some(smt::int_ite(active, &smt::int_lit(1), &smt::int_lit(0)))
                        }
                        _ => None,
                    },
                )
                .collect();
            let refs: Vec<_> = terms.iter().collect();
            let active_count = if refs.is_empty() {
                smt::int_lit(0)
            } else {
                smt::int_add(&refs)
            };
            let min_active = i64::try_from(range.min_active).unwrap_or(i64::MAX);
            let max_active = i64::try_from(range.max_active).unwrap_or(i64::MAX);
            constraints.push(smt::int_ge(&active_count, &smt::int_lit(min_active)));
            constraints.push(smt::int_le(&active_count, &smt::int_lit(max_active)));
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
/// assumption set. `verify`, `theorem`, and `lemma` default to stutter on;
/// use `assume { no stutter }` when a blocked state should be reported as
/// deadlock rather than treated as an idle behavior.
/// The construct defaults are:
/// * `verify` → stutter on (TLA+-style idle steps)
/// * `theorem`/`lemma` → stutter on (refinement-friendly, TLA+-style)
///   The caller passes the verification site's `IRAssumptionSet` so each
///   site sees the trace model it actually opted into.

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
// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
#[allow(clippy::cloned_ref_to_slice_refs, clippy::needless_borrow)]
mod tests;
