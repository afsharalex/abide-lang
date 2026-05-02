//! Property encoding for BMC verification.
//!
//! This module handles the encoding of Abide property expressions (assertions,
//! invariants, quantified properties) into Z3 formulas for bounded model checking.
//!
//! Key components:
//! - `PropertyCtx`: context tracking quantifier-bound variables and system fields
//! - `encode_verify_properties`: top-level property encoding for verify blocks
//! - `encode_prop_expr` / `encode_prop_value`: recursive property expression encoding
//! - Aggregator encoding: `sum`, `product`, `min`, `max`, `count` over entity pools,
//!   fieldless enums, and Bool domains
//! - Thread-local state for precondition obligation tracking and path guards

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use super::smt::{AbideSolver, Bool, Dynamic, Int, SatResult};

use crate::ir::types::{IRExpr, IRSystem, IRType};

use super::context::VerifyContext;
use super::defenv;
use super::encode::{
    bind_pattern_vars, build_domain_predicate, build_z3_quantifier, encode_ite,
    encode_pattern_cond, enum_variant_count, make_z3_var_ctx,
};
use super::harness::SlotPool;
use super::scope::VerifyStoreRange;
use super::smt::{self, SmtValue};
use super::walkers::dynamic_to_smt_value;

// ── Thread-local precondition obligation tracking ───────────────────

// Thread-local accumulator for call-site precondition obligations found
// during system-verification property encoding (encode_prop_expr /
// encode_prop_value). Each obligation is a Z3 Bool that represents
// `path_condition → precondition`. After encoding, these are checked
// as a conjunction: if any obligation is falsifiable, the property
// has a call-site precondition violation.
thread_local! {
    static PROP_PRECOND_OBLIGATIONS: RefCell<Vec<(Bool, String)>> =
        const { RefCell::new(Vec::new()) };
}

static PROP_CHOOSE_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Record a precondition obligation during property encoding.
/// `obligation` is `path_guard → precondition` (already guarded).
pub(super) fn record_prop_precondition_obligation(obligation: Bool, fn_name: String) {
    PROP_PRECOND_OBLIGATIONS.with(|v| {
        v.borrow_mut().push((obligation, fn_name));
    });
}

/// Take (and clear) all recorded precondition obligations.
fn take_prop_precondition_obligations() -> Vec<(Bool, String)> {
    PROP_PRECOND_OBLIGATIONS.with(|v| std::mem::take(&mut *v.borrow_mut()))
}

/// Clear all recorded precondition obligations (call before encoding).
pub(super) fn clear_prop_precondition_obligations() {
    PROP_PRECOND_OBLIGATIONS.with(|v| v.borrow_mut().clear());
}

// Thread-local path guard stack. When encoding inside `A implies B`,
// the path guard for B is `A` (the call is only reachable when A is true).
// Nested implications accumulate: `A implies (B implies f(x))` has
// path guard `A ∧ B` for the `f(x)` call.
thread_local! {
    static PROP_PATH_GUARD: RefCell<Vec<Bool>> = const { RefCell::new(Vec::new()) };
}

fn push_path_guard(guard: Bool) {
    PROP_PATH_GUARD.with(|v| v.borrow_mut().push(guard));
}

fn pop_path_guard() {
    PROP_PATH_GUARD.with(|v| v.borrow_mut().pop());
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

pub(super) fn clear_path_guard_stack() {
    PROP_PATH_GUARD.with(|v| v.borrow_mut().clear());
}

/// Get the current path guard (conjunction of all guards on the stack).
/// Returns `true` if the stack is empty (unconditional context).
pub(super) fn current_path_guard() -> Bool {
    PROP_PATH_GUARD.with(|v| {
        let guards = v.borrow();
        if guards.is_empty() {
            smt::bool_const(true)
        } else {
            let refs: Vec<&Bool> = guards.iter().collect();
            smt::bool_and(&refs)
        }
    })
}

/// Check accumulated precondition obligations. Returns the first
/// violation found (a function name whose precondition is falsifiable).
pub(super) fn check_prop_precondition_obligations() -> Option<String> {
    let obligations = take_prop_precondition_obligations();
    for (obligation, fn_name) in &obligations {
        let vc = AbideSolver::new();
        vc.assert(smt::bool_not(obligation));
        if vc.check() != SatResult::Unsat {
            return Some(format!(
                "precondition of '{fn_name}' may not hold at call site in property"
            ));
        }
    }
    None
}

// ── Property encoding context ────────────────────────────────────────

/// Tracks quantifier-bound variables mapping `var_name` → (`entity_name`, `slot_index`).
///
/// When encoding nested multi-entity quantifiers like
/// `all s: Session | all u: User | u.status == @Locked and s.user_id == u.id`
/// the context accumulates bindings for each enclosing quantifier so that
/// field references from ANY bound entity can be resolved correctly.
pub(super) struct PropertyCtx {
    /// Quantifier-bound variables: `var_name` → (`entity_name`, `slot_index`)
    pub(super) bindings: HashMap<String, (String, usize)>,
    /// Non-entity quantifier variables: `var_name` → `SmtValue`
    /// Used for enum/Int/Bool/Real domain quantifiers in verify/theorem properties.
    pub(super) locals: HashMap<String, SmtValue>,
    /// Store ranges from `compute_verify_scope`. Maps `store_name` →
    /// `VerifyStoreRange { entity_type, start_slot, slot_count, ... }`.
    /// Available for future store-scoped quantifier iteration: when a
    /// quantifier has an `in store_name` filter, the encoding can
    /// restrict iteration to `start_slot..start_slot+slot_count` instead
    /// of the full entity pool. Currently preserved but not yet wired
    /// into the Forall/Exists encoding arms.
    pub(super) store_ranges: HashMap<String, VerifyStoreRange>,
    /// system field name → system name for flat state field resolution.
    /// Includes both flat fields ("screen" → "MailTui") and compound struct
    /// fields ("ui.screen" → "MailTui"). Also tracks struct base names.
    pub(super) system_fields: HashMap<String, String>,
    /// struct base names → system name (e.g., "ui" → "MailTui")
    pub(super) system_struct_bases: HashMap<String, String>,
}

fn property_ctx_with_locals(ctx: &PropertyCtx, locals: HashMap<String, SmtValue>) -> PropertyCtx {
    PropertyCtx {
        bindings: ctx.bindings.clone(),
        locals,
        store_ranges: ctx.store_ranges.clone(),
        system_fields: ctx.system_fields.clone(),
        system_struct_bases: ctx.system_struct_bases.clone(),
    }
}

impl PropertyCtx {
    pub(super) fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            locals: HashMap::new(),
            store_ranges: HashMap::new(),
            system_fields: HashMap::new(),
            system_struct_bases: HashMap::new(),
        }
    }

    /// Set store ranges on this context. Returns self for chaining.
    pub(super) fn with_store_ranges(
        mut self,
        store_ranges: HashMap<String, VerifyStoreRange>,
    ) -> Self {
        self.store_ranges = store_ranges;
        self
    }

    /// Create a new context with an additional entity binding.
    pub(super) fn with_binding(&self, var: &str, entity: &str, slot: usize) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.insert(var.to_owned(), (entity.to_owned(), slot));
        Self {
            bindings,
            locals: self.locals.clone(),
            store_ranges: self.store_ranges.clone(),
            system_fields: self.system_fields.clone(),
            system_struct_bases: self.system_struct_bases.clone(),
        }
    }

    /// Create a new context with all given bindings (var → (entity, slot))
    /// merged into the existing bindings.
    pub(super) fn with_given_bindings(&self, given: &HashMap<String, (String, usize)>) -> Self {
        let mut bindings = self.bindings.clone();
        for (var, (entity, slot)) in given {
            bindings.insert(var.clone(), (entity.clone(), *slot));
        }
        Self {
            bindings,
            locals: self.locals.clone(),
            store_ranges: self.store_ranges.clone(),
            system_fields: self.system_fields.clone(),
            system_struct_bases: self.system_struct_bases.clone(),
        }
    }

    /// Create a new context with a non-entity local variable binding.
    pub(super) fn with_local(&self, var: &str, val: SmtValue) -> Self {
        let mut locals = self.locals.clone();
        locals.insert(var.to_owned(), val);
        Self {
            bindings: self.bindings.clone(),
            locals,
            store_ranges: self.store_ranges.clone(),
            system_fields: self.system_fields.clone(),
            system_struct_bases: self.system_struct_bases.clone(),
        }
    }

    /// populate system field references from in-scope systems.
    /// If the same field name appears in multiple systems, marks it as
    /// ambiguous ("") so the resolver can report an error instead of
    /// silently picking one.
    pub(super) fn with_system_fields(mut self, systems: &[IRSystem]) -> Self {
        for sys in systems {
            for field in &sys.fields {
                if let Some(existing) = self.system_fields.get(&field.name) {
                    if existing != &sys.name {
                        // Ambiguous: same field name in multiple systems
                        self.system_fields.insert(field.name.clone(), String::new());
                    }
                } else {
                    self.system_fields
                        .insert(field.name.clone(), sys.name.clone());
                }
                if field.name.contains('.') {
                    if let Some(base) = field.name.split('.').next() {
                        if let Some(existing) = self.system_struct_bases.get(base) {
                            if existing != &sys.name {
                                self.system_struct_bases
                                    .insert(base.to_owned(), String::new());
                            }
                        } else {
                            self.system_struct_bases
                                .insert(base.to_owned(), sys.name.clone());
                        }
                    }
                }
            }
        }
        self
    }
}

// ── Property encoding for BMC ───────────────────────────────────────

/// Bridges the `PropertyCtx` (which uses `locals` for non-entity bindings) to
/// `build_domain_predicate` (which needs a `HashMap<String, SmtValue>` env).
/// This ensures refinement type predicates and enum range guards are applied
/// correctly in verify/theorem property expressions.
pub(super) fn prop_domain_predicate(
    domain: &crate::ir::types::IRType,
    bound_var: &SmtValue,
    ctx: &PropertyCtx,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
) -> Result<Option<Bool>, String> {
    // Build a minimal env from PropertyCtx locals for the pure expression encoder
    let env: HashMap<String, SmtValue> = ctx.locals.clone();
    build_domain_predicate(domain, bound_var, &env, vctx, defs, None)
}

pub(super) fn encode_step_properties_all_steps(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    step_properties: &[IRExpr],
    bound: usize,
    store_ranges: &HashMap<String, VerifyStoreRange>,
    systems: &[IRSystem],
) -> Result<Bool, String> {
    let mut all_props = Vec::new();

    for property in step_properties {
        for step in 0..=bound {
            let prop =
                encode_property_at_step(pool, vctx, defs, property, step, store_ranges, systems)?;
            all_props.push(prop);
        }
    }

    if all_props.is_empty() {
        return Ok(smt::bool_const(true));
    }

    let refs: Vec<&Bool> = all_props.iter().collect();
    Ok(smt::bool_and(&refs))
}

/// Encode a property expression at a specific BMC step.
///
/// Entry point that creates an empty `PropertyCtx` and delegates to
/// `encode_prop_expr`, which handles nested multi-entity quantifiers.
pub(super) fn encode_property_at_step(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    expr: &IRExpr,
    step: usize,
    store_ranges: &HashMap<String, VerifyStoreRange>,
    systems: &[IRSystem],
) -> Result<Bool, String> {
    let ctx = PropertyCtx::new()
        .with_store_ranges(store_ranges.clone())
        .with_system_fields(systems);
    encode_prop_expr_with_ctx(pool, vctx, defs, &ctx, expr, step)
}

pub(super) fn encode_prop_expr_with_ctx(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<Bool, String> {
    clear_path_guard_stack();
    let normalized = normalize_verifier_choose_expr(expr)?;
    let body = encode_prop_expr(pool, vctx, defs, ctx, &normalized, step)?;
    clear_path_guard_stack();
    Ok(body)
}

pub(super) fn encode_prop_value_with_ctx(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<(SmtValue, Vec<Bool>), String> {
    clear_path_guard_stack();
    let value = encode_prop_value(pool, vctx, defs, ctx, expr, step)?;
    clear_path_guard_stack();
    Ok((value, Vec::new()))
}

/// Encode a property expression with quantifier context.
///
/// Handles entity quantifiers (`all o: Order | P(o)`) by expanding
/// over all active slots. The `PropertyCtx` tracks bindings from all
/// enclosing quantifiers so that nested multi-entity references like
/// `s.user_id` and `u.status` resolve to their correct entity slots.
pub(super) fn encode_prop_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<Bool, String> {
    // Try def expansion — but only if the name is NOT shadowed by a local binding
    // (quantifier-bound variables take precedence over definitions).
    if let IRExpr::Var { name, .. } = expr {
        if !ctx.bindings.contains_key(name) {
            if let Some(expanded) = defs.expand_var(name) {
                return encode_prop_expr(pool, vctx, defs, ctx, &expanded, step);
            }
        }
    }
    if let IRExpr::App { .. } = expr {
        // Record context-sensitive precondition obligations.
        // Each obligation is guarded by the current path condition,
        // so calls inside `A implies f(0)` only require the precondition
        // when A is true.
        if let Some(preconditions) = defs.call_preconditions(expr) {
            let fn_name =
                defenv::decompose_app_chain_name(expr).unwrap_or_else(|| "(unknown)".to_owned());
            let path_guard = current_path_guard();
            for pre in &preconditions {
                if let Ok(pre_bool) = encode_prop_expr(pool, vctx, defs, ctx, pre, step) {
                    // Obligation: path_guard → precondition
                    record_prop_precondition_obligation(
                        smt::bool_implies(&path_guard, &pre_bool),
                        fn_name.clone(),
                    );
                }
            }
        }
        if let Some(expanded) = defs.expand_app(expr) {
            return encode_prop_expr(pool, vctx, defs, ctx, &expanded, step);
        }
    }

    match expr {
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            encode_prop_expr(pool, vctx, defs, ctx, expr, step)
        }
        IRExpr::Let { bindings, body, .. } => {
            encode_prop_let_expr(pool, vctx, defs, ctx, bindings, body, step)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_bool = encode_prop_expr(pool, vctx, defs, ctx, cond, step)?;
            let then_bool = encode_prop_expr(pool, vctx, defs, ctx, then_body, step)?;
            if let Some(else_body) = else_body {
                let else_bool = encode_prop_expr(pool, vctx, defs, ctx, else_body, step)?;
                Ok(smt::bool_ite(&cond_bool, &then_bool, &else_bool))
            } else {
                Ok(smt::bool_implies(&cond_bool, &then_bool))
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let scrut = encode_prop_value(pool, vctx, defs, ctx, scrutinee, step)?;
            let result = encode_prop_match(pool, vctx, defs, ctx, &scrut, arms, step)?;
            result.to_bool()
        }
        // `all x: Entity | P(x)` — conjunction over entity slots.
        // When sema lowered `all x: Entity in store | P(x)` to
        // `(x in store) implies P(x)`, detect that guard pattern here and
        // restrict iteration to the store's slot range.
        IRExpr::Forall {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let (slots, body) =
                narrow_entity_quantifier_slots(ctx, var, entity_name, body, "OpImplies", n_slots);
            let mut conjuncts = Vec::new();
            for slot in slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    // active => P(slot)
                    conjuncts.push(smt::bool_implies(act, &body_val));
                }
            }
            if conjuncts.is_empty() {
                return Ok(smt::bool_const(true));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        // `exists x: Entity | P(x)` — disjunction over active entity slots.
        // `exists x: Entity in store | P(x)` lowers to
        // `(x in store) and P(x)`; detect that guard pattern and iterate only
        // the store's slot range.
        IRExpr::Exists {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let (slots, body) =
                narrow_entity_quantifier_slots(ctx, var, entity_name, body, "OpAnd", n_slots);
            let mut disjuncts = Vec::new();
            for slot in slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    // active AND P(slot)
                    disjuncts.push(smt::bool_and(&[act, &body_val]));
                }
            }
            if disjuncts.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        // `one x: Entity | P(x)` — exactly one active slot satisfies P
        IRExpr::One {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let (slots, body) =
                narrow_entity_quantifier_slots(ctx, var, entity_name, body, "OpAnd", n_slots);
            // Encode P(slot) for each slot, paired with active flag
            let mut slot_preds = Vec::new();
            for slot in slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    slot_preds.push(smt::bool_and(&[act, &body_val]));
                }
            }
            if slot_preds.is_empty() {
                return Ok(smt::bool_const(false));
            }
            // Exactly one: at least one AND at most one (pairwise exclusion)
            let at_least_one = {
                let refs: Vec<&Bool> = slot_preds.iter().collect();
                smt::bool_or(&refs)
            };
            let mut exclusion_conjuncts = Vec::new();
            for i in 0..slot_preds.len() {
                for j in (i + 1)..slot_preds.len() {
                    // ¬(P(i) ∧ P(j))
                    exclusion_conjuncts.push(smt::bool_not(&smt::bool_and(&[
                        &slot_preds[i],
                        &slot_preds[j],
                    ])));
                }
            }
            if exclusion_conjuncts.is_empty() {
                // Only one slot — at_least_one is sufficient
                Ok(at_least_one)
            } else {
                let excl_refs: Vec<&Bool> = exclusion_conjuncts.iter().collect();
                let at_most_one = smt::bool_and(&excl_refs);
                Ok(smt::bool_and(&[&at_least_one, &at_most_one]))
            }
        }
        // `lone x: Entity | P(x)` — at most one active slot satisfies P
        IRExpr::Lone {
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let (slots, body) =
                narrow_entity_quantifier_slots(ctx, var, entity_name, body, "OpAnd", n_slots);
            let mut slot_preds = Vec::new();
            for slot in slots {
                let active = pool.active_at(entity_name, slot, step);
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let body_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                if let Some(SmtValue::Bool(act)) = active {
                    slot_preds.push(smt::bool_and(&[act, &body_val]));
                }
            }
            if slot_preds.len() <= 1 {
                // 0 or 1 slots — at most one trivially true
                return Ok(smt::bool_const(true));
            }
            // Pairwise exclusion: no two slots both satisfy
            let mut exclusion_conjuncts = Vec::new();
            for i in 0..slot_preds.len() {
                for j in (i + 1)..slot_preds.len() {
                    exclusion_conjuncts.push(smt::bool_not(&smt::bool_and(&[
                        &slot_preds[i],
                        &slot_preds[j],
                    ])));
                }
            }
            let refs: Vec<&Bool> = exclusion_conjuncts.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        // ── Non-entity domain quantifiers ──────────────────────────────
        //
        // Two strategies:
        // 1. Fieldless enums: finite expansion over variant indices (decidable).
        // 2. Everything else (ADT enums, refinement types, Int/Bool/Real):
        // Z3 native quantifiers with domain predicates.
        //
        // Fieldless-enum finite expansion (Forall = conjunction, Exists = disjunction):
        IRExpr::Forall {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut conjuncts = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                conjuncts.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if conjuncts.is_empty() {
                return Ok(smt::bool_const(true));
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        IRExpr::Exists {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut disjuncts = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                disjuncts.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if disjuncts.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        IRExpr::One {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut preds = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                preds.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if preds.is_empty() {
                return Ok(smt::bool_const(false));
            }
            // Exactly one: at least one AND pairwise exclusion
            let at_least_one = {
                let refs: Vec<&Bool> = preds.iter().collect();
                smt::bool_or(&refs)
            };
            let mut exclusions = Vec::new();
            for i in 0..preds.len() {
                for j in (i + 1)..preds.len() {
                    exclusions.push(smt::bool_not(&smt::bool_and(&[&preds[i], &preds[j]])));
                }
            }
            if exclusions.is_empty() {
                Ok(at_least_one)
            } else {
                let excl_refs: Vec<&Bool> = exclusions.iter().collect();
                Ok(smt::bool_and(&[&at_least_one, &smt::bool_and(&excl_refs)]))
            }
        }
        IRExpr::Lone {
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            let mut preds = Vec::new();
            for idx in 0..n {
                let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
                preds.push(encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?);
            }
            if preds.len() <= 1 {
                return Ok(smt::bool_const(true));
            }
            let mut exclusions = Vec::new();
            for i in 0..preds.len() {
                for j in (i + 1)..preds.len() {
                    exclusions.push(smt::bool_not(&smt::bool_and(&[&preds[i], &preds[j]])));
                }
            }
            let refs: Vec<&Bool> = exclusions.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        // Z3 native quantifiers for all other non-entity domains:
        // ADT enums (infinite values per constructor), refinement types
        // (domain predicate restricts range), Int/Bool/Real.
        //
        // Domain predicates are applied via build_domain_predicate to
        // constrain bound variables to their declared domain.
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let bound_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let inner_ctx = ctx.with_local(var, bound_var.clone());
            let body_bool = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
            let dp = prop_domain_predicate(domain, &bound_var, &inner_ctx, vctx, defs)?;
            let guarded = match dp {
                Some(d) => smt::bool_implies(&d, &body_bool),
                None => body_bool,
            };
            build_z3_quantifier(true, &bound_var, &guarded, var, domain)
        }
        IRExpr::Exists {
            var, domain, body, ..
        } => {
            let bound_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let inner_ctx = ctx.with_local(var, bound_var.clone());
            let body_bool = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
            let dp = prop_domain_predicate(domain, &bound_var, &inner_ctx, vctx, defs)?;
            let guarded = match dp {
                Some(d) => smt::bool_and(&[&d, &body_bool]),
                None => body_bool,
            };
            build_z3_quantifier(false, &bound_var, &guarded, var, domain)
        }
        IRExpr::One {
            var, domain, body, ..
        } => {
            // Exactly one: ∃x. D(x) ∧ P(x) ∧ ∀y. D(y) ∧ P(y) → y = x
            let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let x_ctx = ctx.with_local(var, x_var.clone());
            let p_x = encode_prop_expr(pool, vctx, defs, &x_ctx, body, step)?;
            let d_x = prop_domain_predicate(domain, &x_var, &x_ctx, vctx, defs)?;
            let x_satisfies = match &d_x {
                Some(dp) => smt::bool_and(&[dp, &p_x]),
                None => p_x.clone(),
            };

            let y_name = format!("{var}__unique");
            let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
            let y_ctx = ctx.with_local(var, y_var.clone());
            let p_y = encode_prop_expr(pool, vctx, defs, &y_ctx, body, step)?;
            let d_y = prop_domain_predicate(domain, &y_var, &y_ctx, vctx, defs)?;
            let y_satisfies = match &d_y {
                Some(dp) => smt::bool_and(&[dp, &p_y]),
                None => p_y,
            };

            let y_eq_x = smt::smt_eq(&y_var, &x_var)?;
            let forall_unique = build_z3_quantifier(
                true,
                &y_var,
                &smt::bool_implies(&y_satisfies, &y_eq_x),
                &y_name,
                domain,
            )?;
            let exists_body = smt::bool_and(&[&x_satisfies, &forall_unique]);
            build_z3_quantifier(false, &x_var, &exists_body, var, domain)
        }
        IRExpr::Lone {
            var, domain, body, ..
        } => {
            // At most one: ∀x, y. D(x) ∧ D(y) ∧ P(x) ∧ P(y) → x = y
            let x_var = make_z3_var_ctx(var, domain, Some(vctx))?;
            let x_ctx = ctx.with_local(var, x_var.clone());
            let p_x = encode_prop_expr(pool, vctx, defs, &x_ctx, body, step)?;
            let d_x = prop_domain_predicate(domain, &x_var, &x_ctx, vctx, defs)?;

            let y_name = format!("{var}__unique");
            let y_var = make_z3_var_ctx(&y_name, domain, Some(vctx))?;
            let y_ctx = ctx.with_local(var, y_var.clone());
            let p_y = encode_prop_expr(pool, vctx, defs, &y_ctx, body, step)?;
            let d_y = prop_domain_predicate(domain, &y_var, &y_ctx, vctx, defs)?;

            let mut antecedents = Vec::new();
            if let Some(dp) = &d_x {
                antecedents.push(dp.clone());
            }
            if let Some(dp) = &d_y {
                antecedents.push(dp.clone());
            }
            antecedents.push(p_x);
            antecedents.push(p_y);
            let antecedent_refs: Vec<&Bool> = antecedents.iter().collect();
            let lhs = smt::bool_and(&antecedent_refs);

            let x_eq_y = smt::smt_eq(&x_var, &y_var)?;
            let forall_body = smt::bool_implies(&lhs, &x_eq_y);
            let inner = build_z3_quantifier(true, &y_var, &forall_body, &y_name, domain)?;
            build_z3_quantifier(true, &x_var, &inner, var, domain)
        }
        // Boolean connectives — recurse
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" || op == "OpOr" || op == "OpImplies" || op == "OpXor" => {
            let l = encode_prop_expr(pool, vctx, defs, ctx, left, step)?;
            // For implication, the RHS is only reachable when the LHS is true.
            // Push the LHS as a path guard so that precondition obligations
            // inside the RHS are guarded by it. Use a scope guard to ensure
            // pop happens even if encoding the RHS returns an error.
            let is_implies = op == "OpImplies";
            if is_implies {
                push_path_guard(l.clone());
            }
            let r_result = encode_prop_expr(pool, vctx, defs, ctx, right, step);
            if is_implies {
                pop_path_guard();
            }
            let r = r_result?;
            match op.as_str() {
                "OpAnd" => Ok(smt::bool_and(&[&l, &r])),
                "OpOr" => Ok(smt::bool_or(&[&l, &r])),
                "OpImplies" => Ok(smt::bool_implies(&l, &r)),
                "OpXor" => Ok(smt::bool_xor(&l, &r)),
                _ => Err(format!("unsupported boolean operator: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = encode_prop_expr(pool, vctx, defs, ctx, operand, step)?;
            Ok(smt::bool_not(&inner))
        }
        // Nested temporal operators — in BMC, `always P` at a single step
        // is just P (the outer loop iterates over steps), and `eventually P`
        // is also just P at this step (the outer loop handles the disjunction).
        IRExpr::Always { body, .. } | IRExpr::Eventually { body, .. } => {
            encode_prop_expr(pool, vctx, defs, ctx, body, step)
        }
        // `P until Q` should not reach here from BMC (desugared at top level
        // after def expansion). If it does arrive (e.g., from scene encoding or
        // other non-BMC paths), use same-step: Q(s) ∨ P(s). This is an
        // over-approximation but avoids unsound false proofs.
        IRExpr::Until { left, right, .. } => {
            let q = encode_prop_expr(pool, vctx, defs, ctx, right, step)?;
            let p = encode_prop_expr(pool, vctx, defs, ctx, left, step)?;
            Ok(smt::bool_or(&[&q, &p]))
        }
        // / — past-time temporal operators.
        //
        // At step `n`, each past-time operator unfolds into a finite
        // formula over states `[0, n]`. Generated constraints are
        // O(n) (or O(n²) for `since`), which is fine at typical BMC
        // bounds. Nesting works automatically: when these operators
        // appear under `always`/`forall`/etc., the surrounding
        // dispatch evaluates the body at every step `n`, and each
        // recursive evaluation references the appropriate prefix.
        //
        // **Stutter interaction ( open question 1):** the
        // BMC trace is the linear unfolding `[0, n]`. When a verify
        // block opts into stutter via `assume { stutter }`, stutter
        // steps appear in this prefix as identity transitions: the
        // state at step k+1 equals the state at step k. Past-time
        // predicates therefore evaluate to the same Boolean at a
        // stutter step as at the previous non-stutter step — they
        // are *observable* but the predicate value is unchanged. No
        // special-casing is required: `historically P` with k = K
        // and k = K+1 (stutter) both check `P` against the same
        // state assignment, so the conjunction is unaffected.
        IRExpr::Historically { body, .. } => {
            // historically P @ step n ≡ ⋀ k in [0, n]. P @ step k
            let mut conjuncts: Vec<Bool> = Vec::with_capacity(step + 1);
            for k in 0..=step {
                conjuncts.push(encode_prop_expr(pool, vctx, defs, ctx, body, k)?);
            }
            let refs: Vec<&Bool> = conjuncts.iter().collect();
            Ok(smt::bool_and(&refs))
        }
        IRExpr::Once { body, .. } => {
            // once P @ step n ≡ ⋁ k in [0, n]. P @ step k
            let mut disjuncts: Vec<Bool> = Vec::with_capacity(step + 1);
            for k in 0..=step {
                disjuncts.push(encode_prop_expr(pool, vctx, defs, ctx, body, k)?);
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        IRExpr::Previously { body, .. } => {
            // previously P @ step n ≡ if n > 0 then P @ step (n-1) else false
            // ( false at trace position 0; Past-LTL convention)
            if step == 0 {
                Ok(smt::bool_const(false))
            } else {
                encode_prop_expr(pool, vctx, defs, ctx, body, step - 1)
            }
        }
        IRExpr::Since { left, right, .. } => {
            // P since Q @ step n ≡
            // ⋁ k in [0, n]. (Q @ k) ∧ ⋀ j in (k, n]. P @ j
            // ("Q became true at some past step k, and P held continuously
            // from k+1 up to and including the current step.")
            let mut disjuncts: Vec<Bool> = Vec::with_capacity(step + 1);
            for k in 0..=step {
                let q_at_k = encode_prop_expr(pool, vctx, defs, ctx, right, k)?;
                let mut p_between: Vec<Bool> = Vec::new();
                for j in (k + 1)..=step {
                    p_between.push(encode_prop_expr(pool, vctx, defs, ctx, left, j)?);
                }
                let p_conj = if p_between.is_empty() {
                    smt::bool_const(true)
                } else {
                    let p_refs: Vec<&Bool> = p_between.iter().collect();
                    smt::bool_and(&p_refs)
                };
                disjuncts.push(smt::bool_and(&[&q_at_k, &p_conj]));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        // / — `saw Sys::event(args)` past-time observation.
        //
        // At step `n`, `saw E::f(a1, a2,...) ≡ ⋁ k ∈ [0, n].
        // fire_E_f_k ∧ ⋀ i. match(a_i, param_i_k)`
        //
        // The fire indicator `fire_{sys}_{event}_t{k}` is created by
        // `transition_constraints_with_fire` and shares Z3 namespace.
        // The parameter variables `param_{name}_{k}` are created by
        // `build_event_params` during event body encoding and are
        // shared by name across the solver context.
        //
        // Args that are `None` are wildcards (no constraint).
        // Args that are `Some(expr)` must equal the parameter value.
        //
        // **Stutter clarification ():** stutter steps have
        // `stutter_t{k} = true` and no fire indicator is true, so
        // `saw` is naturally silent across stutter steps.
        IRExpr::Saw {
            system_name,
            event_name,
            args,
            ..
        } => {
            let params = vctx
                .command_params
                .get(&(system_name.clone(), event_name.clone()))
                .ok_or_else(|| format!("saw: unknown event {system_name}::{event_name}"))?;

            let mut disjuncts: Vec<Bool> = Vec::with_capacity(step + 1);
            for k in 0..=step {
                // fire indicator for this event at step k
                let fire_var = smt::bool_var(&format!("fire_{system_name}_{event_name}_t{k}"));
                let fire_bool = fire_var
                    .to_bool()
                    .map_err(|e| format!("saw fire var: {e}"))?;

                let mut conjuncts: Vec<Bool> = vec![fire_bool];

                // For each non-wildcard arg, constrain equality with the
                // per-step parameter variable.
                for (i, arg_opt) in args.iter().enumerate() {
                    if let Some(arg_expr) = arg_opt {
                        if i < params.len() {
                            let p = &params[i];
                            let param_var = match &p.ty {
                                crate::ir::types::IRType::Bool => {
                                    smt::bool_var(&format!("param_{}_{}", p.name, k))
                                }
                                crate::ir::types::IRType::Real
                                | crate::ir::types::IRType::Float => {
                                    smt::real_var(&format!("param_{}_{}", p.name, k))
                                }
                                _ => smt::int_var(&format!("param_{}_{}", p.name, k)),
                            };
                            // Encode the arg expression at the CURRENT step
                            // (not step k) — args reference the property's
                            // ambient scope, not the historical step.
                            let arg_val = encode_prop_value(pool, vctx, defs, ctx, arg_expr, step)?;
                            let eq = smt::smt_eq(&param_var, &arg_val)
                                .map_err(|e| format!("saw arg eq: {e}"))?;
                            conjuncts.push(eq);
                        }
                    }
                }

                let conj_refs: Vec<&Bool> = conjuncts.iter().collect();
                disjuncts.push(smt::bool_and(&conj_refs));
            }

            if disjuncts.is_empty() {
                // step == -1 can't happen (usize), but guard anyway
                Ok(smt::bool_const(false))
            } else {
                let refs: Vec<&Bool> = disjuncts.iter().collect();
                Ok(smt::bool_or(&refs))
            }
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpMapHas" => {
            let map_val = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let key_val = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            let Some(IRType::Map { value, .. }) = expr_type(left) else {
                return Err("Map::has requires a map-typed left operand".to_owned());
            };
            Ok(smt::map_has(&map_val, &key_val, value)?.to_bool()?)
        }
        // Comparison and other BinOps that produce Bool (OpEq, OpNEq, OpLt, etc.)
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            Ok(smt::binop(op, &l, &r)?.to_bool()?)
        }
        // Literals
        IRExpr::Lit {
            value: crate::ir::types::LitVal::Bool { value },
            ..
        } => Ok(smt::bool_const(*value)),
        // Everything else: encode as value and convert to Bool
        other => {
            let val = encode_prop_value(pool, vctx, defs, ctx, other, step)?;
            Ok(val.to_bool()?)
        }
    }
}

fn encode_prop_let_expr(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    step: usize,
) -> Result<Bool, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return encode_prop_expr(pool, vctx, defs, ctx, body, step);
    };

    match &binding.expr {
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => match domain {
            crate::ir::types::IRType::Entity { name: entity_name } => {
                let mut disjuncts = Vec::new();
                for slot in 0..pool.slots_for(entity_name) {
                    let Some(SmtValue::Bool(active)) = pool.active_at(entity_name, slot, step)
                    else {
                        continue;
                    };
                    let pred_ctx = ctx.with_binding(var, entity_name, slot);
                    let pred_bool = if let Some(predicate) = predicate {
                        encode_prop_expr(pool, vctx, defs, &pred_ctx, predicate, step)?
                    } else {
                        smt::bool_const(true)
                    };
                    let rest_ctx = ctx.with_binding(&binding.name, entity_name, slot);
                    let rest_bool =
                        encode_prop_let_expr(pool, vctx, defs, &rest_ctx, rest, body, step)?;
                    disjuncts.push(smt::bool_and(&[active, &pred_bool, &rest_bool]));
                }
                if disjuncts.is_empty() {
                    return Ok(smt::bool_const(false));
                }
                let refs: Vec<&Bool> = disjuncts.iter().collect();
                Ok(smt::bool_or(&refs))
            }
            _ => {
                let fresh = format!(
                    "__abide_choose_{}_{}",
                    binding.name,
                    PROP_CHOOSE_COUNTER.fetch_add(1, Ordering::Relaxed)
                );
                let witness = make_z3_var_ctx(&fresh, domain, Some(vctx))?;
                let pred_ctx = ctx.with_local(var, witness.clone());
                let mut conjuncts = Vec::new();
                if let Some(domain_pred) =
                    prop_domain_predicate(domain, &witness, &pred_ctx, vctx, defs)?
                {
                    conjuncts.push(domain_pred);
                }
                if let Some(predicate) = predicate {
                    conjuncts.push(encode_prop_expr(
                        pool, vctx, defs, &pred_ctx, predicate, step,
                    )?);
                }
                let rest_ctx = ctx.with_local(&binding.name, witness.clone());
                let rest_bool =
                    encode_prop_let_expr(pool, vctx, defs, &rest_ctx, rest, body, step)?;
                conjuncts.push(rest_bool);
                let refs: Vec<&Bool> = conjuncts.iter().collect();
                build_z3_quantifier(false, &witness, &smt::bool_and(&refs), &fresh, domain)
            }
        },
        _ => {
            let mut locals = ctx.locals.clone();
            let binding_ctx = property_ctx_with_locals(ctx, locals.clone());
            let val = encode_prop_value(pool, vctx, defs, &binding_ctx, &binding.expr, step)?;
            locals.insert(binding.name.clone(), val);
            let body_ctx = property_ctx_with_locals(ctx, locals);
            encode_prop_let_expr(pool, vctx, defs, &body_ctx, rest, body, step)
        }
    }
}

fn wrap_let_expr(bindings: Vec<crate::ir::types::LetBinding>, body: IRExpr) -> IRExpr {
    if bindings.is_empty() {
        body
    } else {
        IRExpr::Let {
            bindings,
            body: Box::new(body),
            span: None,
        }
    }
}

fn logical_binop(op: &str) -> bool {
    matches!(op, "OpAnd" | "OpOr" | "OpImplies" | "OpXor")
}

fn bindings_contain_choose(bindings: &[crate::ir::types::LetBinding]) -> bool {
    bindings
        .iter()
        .any(|binding| matches!(binding.expr, IRExpr::Choose { .. }))
}

pub(super) fn normalize_verifier_choose_expr(expr: &IRExpr) -> Result<IRExpr, String> {
    match expr {
        IRExpr::Let { bindings, body, .. } => {
            let mut flat_bindings = Vec::new();
            for binding in bindings {
                let (prefix, expr) = normalize_verifier_choose_term(&binding.expr)?;
                flat_bindings.extend(prefix);
                flat_bindings.push(crate::ir::types::LetBinding {
                    name: binding.name.clone(),
                    ty: binding.ty.clone(),
                    expr,
                });
            }
            let body = normalize_verifier_choose_expr(body)?;
            Ok(IRExpr::Let {
                bindings: flat_bindings,
                body: Box::new(body),
                span: None,
            })
        }
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } if logical_binop(op) => Ok(IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(normalize_verifier_choose_expr(left)?),
            right: Box::new(normalize_verifier_choose_expr(right)?),
            ty: ty.clone(),
            span: None,
        }),
        IRExpr::UnOp {
            op, operand, ty, ..
        } if op == "OpNot" => Ok(IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(normalize_verifier_choose_expr(operand)?),
            ty: ty.clone(),
            span: None,
        }),
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => Ok(IRExpr::IfElse {
            cond: Box::new(normalize_verifier_choose_expr(cond)?),
            then_body: Box::new(normalize_verifier_choose_expr(then_body)?),
            else_body: else_body
                .as_ref()
                .map(|body| normalize_verifier_choose_expr(body))
                .transpose()?
                .map(Box::new),
            span: None,
        }),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let (scrutinee_bindings, scrutinee_expr) = normalize_verifier_choose_term(scrutinee)?;
            let arms = arms
                .iter()
                .map(|arm| {
                    Ok(crate::ir::types::IRMatchArm {
                        pattern: arm.pattern.clone(),
                        guard: arm
                            .guard
                            .as_ref()
                            .map(normalize_verifier_choose_expr)
                            .transpose()?,
                        body: normalize_verifier_choose_expr(&arm.body)?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok(wrap_let_expr(
                scrutinee_bindings,
                IRExpr::Match {
                    scrutinee: Box::new(scrutinee_expr),
                    arms,
                    span: None,
                },
            ))
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => Ok(IRExpr::Forall {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => Ok(IRExpr::Exists {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::One {
            var, domain, body, ..
        } => Ok(IRExpr::One {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => Ok(IRExpr::Lone {
            var: var.clone(),
            domain: domain.clone(),
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Always { body, .. } => Ok(IRExpr::Always {
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Eventually { body, .. } => Ok(IRExpr::Eventually {
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Historically { body, .. } => Ok(IRExpr::Historically {
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Once { body, .. } => Ok(IRExpr::Once {
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Previously { body, .. } => Ok(IRExpr::Previously {
            body: Box::new(normalize_verifier_choose_expr(body)?),
            span: None,
        }),
        IRExpr::Until { left, right, .. } => Ok(IRExpr::Until {
            left: Box::new(normalize_verifier_choose_expr(left)?),
            right: Box::new(normalize_verifier_choose_expr(right)?),
            span: None,
        }),
        IRExpr::Since { left, right, .. } => Ok(IRExpr::Since {
            left: Box::new(normalize_verifier_choose_expr(left)?),
            right: Box::new(normalize_verifier_choose_expr(right)?),
            span: None,
        }),
        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            ..
        } => {
            let (bindings, body_expr) = normalize_verifier_choose_term(body)?;
            let agg = IRExpr::Aggregate {
                kind: *kind,
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(body_expr),
                in_filter: in_filter
                    .as_ref()
                    .map(|f| normalize_verifier_choose_expr(f))
                    .transpose()?
                    .map(Box::new),
                span: None,
            };
            Ok(wrap_let_expr(bindings, agg))
        }
        IRExpr::Saw {
            system_name,
            event_name,
            args,
            ..
        } => {
            let mut bindings = Vec::new();
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                if let Some(arg) = arg {
                    let (arg_bindings, arg_expr) = normalize_verifier_choose_term(arg)?;
                    bindings.extend(arg_bindings);
                    new_args.push(Some(Box::new(arg_expr)));
                } else {
                    new_args.push(None);
                }
            }
            Ok(wrap_let_expr(
                bindings,
                IRExpr::Saw {
                    system_name: system_name.clone(),
                    event_name: event_name.clone(),
                    args: new_args,
                    span: None,
                },
            ))
        }
        other => {
            let (bindings, expr) = normalize_verifier_choose_term(other)?;
            Ok(wrap_let_expr(bindings, expr))
        }
    }
}

fn normalize_verifier_choose_term(
    expr: &IRExpr,
) -> Result<(Vec<crate::ir::types::LetBinding>, IRExpr), String> {
    match expr {
        IRExpr::Choose { ty, .. } => {
            let name = format!(
                "__abide_prop_choose_{}",
                PROP_CHOOSE_COUNTER.fetch_add(1, Ordering::Relaxed)
            );
            Ok((
                vec![crate::ir::types::LetBinding {
                    name: name.clone(),
                    ty: ty.clone(),
                    expr: expr.clone(),
                }],
                IRExpr::Var {
                    name,
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::Lit { .. }
        | IRExpr::Var { .. }
        | IRExpr::Prime { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => Ok((Vec::new(), expr.clone())),
        IRExpr::Field {
            expr: base,
            field,
            ty,
            ..
        } => {
            let (bindings, base) = normalize_verifier_choose_term(base)?;
            Ok((
                bindings,
                IRExpr::Field {
                    expr: Box::new(base),
                    field: field.clone(),
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::App { func, arg, ty, .. } => {
            let (mut bindings, func) = normalize_verifier_choose_term(func)?;
            let (arg_bindings, arg) = normalize_verifier_choose_term(arg)?;
            bindings.extend(arg_bindings);
            Ok((
                bindings,
                IRExpr::App {
                    func: Box::new(func),
                    arg: Box::new(arg),
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::UnOp {
            op, operand, ty, ..
        } => {
            let (bindings, operand) = normalize_verifier_choose_term(operand)?;
            Ok((
                bindings,
                IRExpr::UnOp {
                    op: op.clone(),
                    operand: Box::new(operand),
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            ..
        } => {
            let (mut bindings, left) = normalize_verifier_choose_term(left)?;
            let (right_bindings, right) = normalize_verifier_choose_term(right)?;
            bindings.extend(right_bindings);
            Ok((
                bindings,
                IRExpr::BinOp {
                    op: op.clone(),
                    left: Box::new(left),
                    right: Box::new(right),
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut flat_bindings = Vec::new();
            for binding in bindings {
                let (prefix, expr) = normalize_verifier_choose_term(&binding.expr)?;
                flat_bindings.extend(prefix);
                flat_bindings.push(crate::ir::types::LetBinding {
                    name: binding.name.clone(),
                    ty: binding.ty.clone(),
                    expr,
                });
            }
            let (body_bindings, body_expr) = normalize_verifier_choose_term(body)?;
            flat_bindings.extend(body_bindings);
            Ok((flat_bindings, body_expr))
        }
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            let mut bindings = Vec::new();
            let mut new_args = Vec::with_capacity(args.len());
            for (field, arg) in args {
                let (arg_bindings, arg_expr) = normalize_verifier_choose_term(arg)?;
                bindings.extend(arg_bindings);
                new_args.push((field.clone(), arg_expr));
            }
            Ok((
                bindings,
                IRExpr::Ctor {
                    enum_name: enum_name.clone(),
                    ctor: ctor.clone(),
                    args: new_args,
                    span: None,
                },
            ))
        }
        IRExpr::Index { map, key, ty, .. } => {
            let (mut bindings, map) = normalize_verifier_choose_term(map)?;
            let (key_bindings, key) = normalize_verifier_choose_term(key)?;
            bindings.extend(key_bindings);
            Ok((
                bindings,
                IRExpr::Index {
                    map: Box::new(map),
                    key: Box::new(key),
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            ..
        } => {
            let (mut bindings, map) = normalize_verifier_choose_term(map)?;
            let (key_bindings, key) = normalize_verifier_choose_term(key)?;
            let (value_bindings, value) = normalize_verifier_choose_term(value)?;
            bindings.extend(key_bindings);
            bindings.extend(value_bindings);
            Ok((
                bindings,
                IRExpr::MapUpdate {
                    map: Box::new(map),
                    key: Box::new(key),
                    value: Box::new(value),
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::SetLit { elements, ty, .. } => {
            let mut bindings = Vec::new();
            let mut new_elements = Vec::with_capacity(elements.len());
            for element in elements {
                let (elt_bindings, elt) = normalize_verifier_choose_term(element)?;
                bindings.extend(elt_bindings);
                new_elements.push(elt);
            }
            Ok((
                bindings,
                IRExpr::SetLit {
                    elements: new_elements,
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::SeqLit { elements, ty, .. } => {
            let mut bindings = Vec::new();
            let mut new_elements = Vec::with_capacity(elements.len());
            for element in elements {
                let (elt_bindings, elt) = normalize_verifier_choose_term(element)?;
                bindings.extend(elt_bindings);
                new_elements.push(elt);
            }
            Ok((
                bindings,
                IRExpr::SeqLit {
                    elements: new_elements,
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::MapLit { entries, ty, .. } => {
            let mut bindings = Vec::new();
            let mut new_entries = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                let (key_bindings, key) = normalize_verifier_choose_term(key)?;
                let (value_bindings, value) = normalize_verifier_choose_term(value)?;
                bindings.extend(key_bindings);
                bindings.extend(value_bindings);
                new_entries.push((key, value));
            }
            Ok((
                bindings,
                IRExpr::MapLit {
                    entries: new_entries,
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::SetComp {
            var,
            domain,
            source,
            filter,
            projection,
            ty,
            ..
        } => {
            let (projection_bindings, projection) = projection
                .as_ref()
                .map(|expr| normalize_verifier_choose_term(expr))
                .transpose()?
                .map_or((Vec::new(), None), |(bindings, expr)| {
                    (bindings, Some(Box::new(expr)))
                });
            if bindings_contain_choose(&projection_bindings) {
                return Err(
                    "bare choose inside set comprehension projections is not yet supported in verifier properties"
                        .to_owned(),
                );
            }
            Ok((
                Vec::new(),
                IRExpr::SetComp {
                    var: var.clone(),
                    domain: domain.clone(),
                    source: source
                        .as_ref()
                        .map(|source| normalize_verifier_choose_expr(source))
                        .transpose()?
                        .map(Box::new),
                    filter: Box::new(normalize_verifier_choose_expr(filter)?),
                    projection,
                    ty: ty.clone(),
                    span: None,
                },
            ))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let (then_bindings, then_body) = normalize_verifier_choose_term(then_body)?;
            let (else_bindings, else_body) = else_body
                .as_ref()
                .map(|body| normalize_verifier_choose_term(body))
                .transpose()?
                .map_or((Vec::new(), None), |(bindings, expr)| {
                    (bindings, Some(Box::new(expr)))
                });
            if bindings_contain_choose(&then_bindings) || bindings_contain_choose(&else_bindings) {
                return Err(
                    "bare choose inside value if/else branches is not yet supported in verifier properties"
                        .to_owned(),
                );
            }
            Ok((
                Vec::new(),
                IRExpr::IfElse {
                    cond: Box::new(normalize_verifier_choose_expr(cond)?),
                    then_body: Box::new(wrap_let_expr(then_bindings, then_body)),
                    else_body: else_body.map(|body| Box::new(wrap_let_expr(else_bindings, *body))),
                    span: None,
                },
            ))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let (scrutinee_bindings, scrutinee) = normalize_verifier_choose_term(scrutinee)?;
            let mut new_arms = Vec::with_capacity(arms.len());
            for arm in arms {
                let (body_bindings, body) = normalize_verifier_choose_term(&arm.body)?;
                if bindings_contain_choose(&body_bindings) {
                    return Err(
                        "bare choose inside value match arms is not yet supported in verifier properties"
                            .to_owned(),
                    );
                }
                new_arms.push(crate::ir::types::IRMatchArm {
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(normalize_verifier_choose_expr)
                        .transpose()?,
                    body: wrap_let_expr(body_bindings, body),
                });
            }
            Ok((
                scrutinee_bindings,
                IRExpr::Match {
                    scrutinee: Box::new(scrutinee),
                    arms: new_arms,
                    span: None,
                },
            ))
        }
        other => Ok((Vec::new(), other.clone())),
    }
}

fn narrow_entity_quantifier_slots<'a>(
    ctx: &PropertyCtx,
    var: &str,
    entity_name: &str,
    body: &'a IRExpr,
    guard_op: &str,
    n_slots: usize,
) -> (std::ops::Range<usize>, &'a IRExpr) {
    if let Some((start_slot, slot_count, guarded_body)) =
        extract_store_scoped_quantifier_body(ctx, var, entity_name, body, guard_op)
    {
        let start = start_slot.min(n_slots);
        let end = start_slot.saturating_add(slot_count).min(n_slots);
        return (start..end, guarded_body);
    }
    (0..n_slots, body)
}

fn extract_store_scoped_quantifier_body<'a>(
    ctx: &PropertyCtx,
    var: &str,
    entity_name: &str,
    body: &'a IRExpr,
    guard_op: &str,
) -> Option<(usize, usize, &'a IRExpr)> {
    let IRExpr::BinOp {
        op, left, right, ..
    } = body
    else {
        return None;
    };
    if op != guard_op {
        return None;
    }
    let (start_slot, slot_count) = extract_store_membership_range(ctx, var, entity_name, left)?;
    Some((start_slot, slot_count, right.as_ref()))
}

fn extract_store_membership_range(
    ctx: &PropertyCtx,
    var: &str,
    entity_name: &str,
    expr: &IRExpr,
) -> Option<(usize, usize)> {
    let IRExpr::Index { map, key, .. } = expr else {
        return None;
    };
    let IRExpr::Var {
        name: store_name, ..
    } = map.as_ref()
    else {
        return None;
    };
    let IRExpr::Var { name: key_var, .. } = key.as_ref() else {
        return None;
    };
    if key_var != var {
        return None;
    }
    let store_range = ctx.store_ranges.get(store_name)?;
    if store_range.entity_type != entity_name {
        return None;
    }
    Some((store_range.start_slot, store_range.slot_count))
}

/// Encode a value expression using the multi-entity quantifier context.
///
/// Resolves field references like `s.user_id` by looking up `"s"` in the
/// `PropertyCtx` bindings to find the bound entity and slot index,
/// then resolves via `pool.field_at(entity, slot, field, step)`.
#[allow(clippy::too_many_lines)]
pub(super) fn encode_prop_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    // Try def expansion — but only if the name is NOT shadowed by a local binding.
    if let IRExpr::Var { name, .. } = expr {
        if !ctx.bindings.contains_key(name) {
            if let Some(expanded) = defs.expand_var(name) {
                return encode_prop_value(pool, vctx, defs, ctx, &expanded, step);
            }
        }
    }
    if let IRExpr::App { .. } = expr {
        // Record context-sensitive precondition obligations (same as encode_prop_expr)
        if let Some(preconditions) = defs.call_preconditions(expr) {
            let fn_name =
                defenv::decompose_app_chain_name(expr).unwrap_or_else(|| "(unknown)".to_owned());
            let path_guard = current_path_guard();
            for pre in &preconditions {
                if let Ok(pre_bool) = encode_prop_expr(pool, vctx, defs, ctx, pre, step) {
                    record_prop_precondition_obligation(
                        smt::bool_implies(&path_guard, &pre_bool),
                        fn_name.clone(),
                    );
                }
            }
        }
        if let Some(expanded) = defs.expand_app(expr) {
            return encode_prop_value(pool, vctx, defs, ctx, &expanded, step);
        }
    }

    match expr {
        IRExpr::Choose { .. } => {
            Err("choose is only supported through let-binding in verifier properties".to_owned())
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut locals = ctx.locals.clone();
            for binding in bindings {
                let binding_ctx = property_ctx_with_locals(ctx, locals.clone());
                let val = encode_prop_value(pool, vctx, defs, &binding_ctx, &binding.expr, step)?;
                locals.insert(binding.name.clone(), val);
            }
            let body_ctx = property_ctx_with_locals(ctx, locals);
            encode_prop_value(pool, vctx, defs, &body_ctx, body, step)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_bool = encode_prop_expr(pool, vctx, defs, ctx, cond, step)?;
            let then_val = encode_prop_value(pool, vctx, defs, ctx, then_body, step)?;
            if let Some(else_body) = else_body {
                let else_val = encode_prop_value(pool, vctx, defs, ctx, else_body, step)?;
                encode_ite(&cond_bool, &then_val, &else_val)
            } else {
                let then_bool = then_val.to_bool()?;
                Ok(SmtValue::Bool(smt::bool_implies(&cond_bool, &then_bool)))
            }
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let scrut = encode_prop_value(pool, vctx, defs, ctx, scrutinee, step)?;
            encode_prop_match(pool, vctx, defs, ctx, &scrut, arms, step)
        }
        IRExpr::Lit { value, .. } => match value {
            crate::ir::types::LitVal::Int { value } => Ok(smt::int_val(*value)),
            crate::ir::types::LitVal::Bool { value } => Ok(smt::bool_val(*value)),
            crate::ir::types::LitVal::Real { value }
            | crate::ir::types::LitVal::Float { value } => {
                #[allow(clippy::cast_possible_truncation)]
                let scaled = (*value * 1_000_000.0) as i64;
                Ok(smt::real_val(scaled, 1_000_000))
            }
            crate::ir::types::LitVal::Str { .. } => Ok(smt::int_val(0)),
        },
        // Field access: `var.field` — look up var in bindings, resolve field from bound entity
        IRExpr::Field {
            expr: recv, field, ..
        } => {
            // Try to resolve the receiver as a bound variable
            if let IRExpr::Var { name, .. } = recv.as_ref() {
                if let Some((entity, slot)) = ctx.bindings.get(name) {
                    if let Some(val) = pool.field_at(entity, *slot, field, step) {
                        return Ok(val.clone());
                    }
                    return Err(format!(
                        "field not found: {entity}.{field} (var={name}, slot={slot}, step={step})"
                    ));
                }
                // struct-typed system field access (e.g., ui.screen)
                if let Some(sys_name) = ctx.system_struct_bases.get(name.as_str()) {
                    if sys_name.is_empty() {
                        return Err(format!(
                            "ambiguous system struct field `{name}`: exists in multiple in-scope systems"
                        ));
                    }
                    let compound = format!("{name}.{field}");
                    if let Some(val) = pool.system_field_at(sys_name, &compound, step) {
                        return Ok(val.clone());
                    }
                }
            }
            // No binding for receiver — try all bindings to find the field
            for (entity, slot) in ctx.bindings.values() {
                if let Some(val) = pool.field_at(entity, *slot, field, step) {
                    return Ok(val.clone());
                }
            }
            Err(format!(
                "field not found in any bound entity: {field} (step={step})"
            ))
        }
        // Bare variable: check locals first, then entity bindings, then system fields
        IRExpr::Var { name, .. } => {
            // Check non-entity local bindings first (enum/Int/Bool/Real quantifier vars)
            if let Some(val) = ctx.locals.get(name) {
                return Ok(val.clone());
            }
            // Try as a field in each bound entity — entity bindings take priority
            // over system fields so that quantified `all o: Order | o.status`
            // doesn't get shadowed by a same-named system field.
            let mut matches = Vec::new();
            for (var, (entity, slot)) in &ctx.bindings {
                if let Some(val) = pool.field_at(entity, *slot, name, step) {
                    matches.push((var.clone(), entity.clone(), val.clone()));
                }
            }
            if !matches.is_empty() {
                return match matches.len() {
                    1 => Ok(matches.into_iter().next().unwrap().2),
                    _ => {
                        Err(format!(
                        "ambiguous variable {name}: matches fields in entities {:?} (step={step})",
                        matches.iter().map(|(v, e, _)| format!("{v}:{e}")).collect::<Vec<_>>()
                    ))
                    }
                };
            }
            // check system flat state fields (after entity bindings)
            if let Some(sys_name) = ctx.system_fields.get(name) {
                if sys_name.is_empty() {
                    return Err(format!(
                        "ambiguous system field `{name}`: exists in multiple in-scope systems"
                    ));
                }
                if let Some(val) = pool.system_field_at(sys_name, name, step) {
                    return Ok(val.clone());
                }
            }
            Err(format!(
                "variable not found: {name} (bindings: {:?}, step={step})",
                ctx.bindings.keys().collect::<Vec<_>>()
            ))
        }
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => {
            // ADT-encoded enum: use constructor function with field arguments
            if let Some(dt) = vctx.adt_sorts.get(enum_name) {
                for variant in &dt.variants {
                    if smt::func_decl_name(&variant.constructor) == *ctor {
                        if args.is_empty() {
                            let result = smt::func_decl_apply(&variant.constructor, &[]);
                            return Ok(dynamic_to_smt_value(result));
                        }
                        // Build args in declared field order
                        let declared_names: Vec<std::string::String> =
                            variant.accessors.iter().map(smt::func_decl_name).collect();
                        let args_map: HashMap<&str, &IRExpr> =
                            args.iter().map(|(n, e)| (n.as_str(), e)).collect();
                        let mut z3_args: Vec<Dynamic> = Vec::new();
                        for decl_name in &declared_names {
                            if let Some(field_expr) = args_map.get(decl_name.as_str()) {
                                let val =
                                    encode_prop_value(pool, vctx, defs, ctx, field_expr, step)?;
                                z3_args.push(val.to_dynamic());
                            }
                        }
                        let arg_refs: Vec<&Dynamic> = z3_args.iter().collect();
                        let result = smt::func_decl_apply(&variant.constructor, &arg_refs);
                        return Ok(dynamic_to_smt_value(result));
                    }
                }
            }
            // Flat Int encoding for fieldless enums
            let id = vctx.variants.try_id_of(enum_name, ctor)?;
            Ok(smt::int_val(id))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpSeqConcat" => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            let Some(IRType::Seq { element }) = expr_type(left) else {
                return Err("Seq::concat requires sequence operands".to_string());
            };
            smt::seq_concat(&l, &r, element)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpMapHas" => {
            let map_val = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let key_val = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            let Some(IRType::Map { value, .. }) = expr_type(left) else {
                return Err("Map::has requires a map-typed left operand".to_owned());
            };
            smt::map_has(&map_val, &key_val, value)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpMapMerge" => {
            let left_val = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let right_val = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            let Some(IRType::Map { key, value }) = expr_type(left) else {
                return Err("Map::merge requires map operands".to_owned());
            };
            smt::map_merge(&left_val, &right_val, key, value)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_prop_value(pool, vctx, defs, ctx, left, step)?;
            let r = encode_prop_value(pool, vctx, defs, ctx, right, step)?;
            Ok(smt::binop(op, &l, &r)?)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqHead" => {
            let v = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
            let Some(IRType::Seq { element }) = expr_type(operand) else {
                return smt::unop(op, &v);
            };
            smt::seq_head(&v, element)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqTail" => {
            if let IRExpr::SeqLit { elements, ty, .. } = operand.as_ref() {
                let tail = IRExpr::SeqLit {
                    elements: elements.iter().skip(1).cloned().collect(),
                    ty: ty.clone(),
                    span: None,
                };
                return encode_prop_value(pool, vctx, defs, ctx, &tail, step);
            }
            let v = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
            let Some(IRType::Seq { element }) = expr_type(operand) else {
                return smt::unop(op, &v);
            };
            smt::seq_tail(&v, element)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqLength" => {
            if let Some(IRType::Seq { element }) = expr_type(operand) {
                let v = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
                smt::seq_length(&v, element)
            } else {
                encode_card(pool, vctx, defs, ctx, operand, step)
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpSeqEmpty" => {
            let len = if let Some(IRType::Seq { element }) = expr_type(operand) {
                let v = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
                smt::seq_length(&v, element)?
            } else {
                encode_card(pool, vctx, defs, ctx, operand, step)?
            };
            Ok(SmtValue::Bool(smt::smt_eq(&len, &smt::int_val(0))?))
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpMapDomain" => {
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
                return encode_prop_value(pool, vctx, defs, ctx, &set_lit, step);
            }
            let map_val = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
            let Some(IRType::Map { key, value }) = expr_type(operand) else {
                return Err("Map::domain requires a map operand".to_owned());
            };
            smt::map_domain(&map_val, key, value)
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpMapRange" => {
            if let IRExpr::MapLit { entries, .. } = operand.as_ref() {
                let set_lit = IRExpr::SetLit {
                    elements: entries.iter().map(|(_, v)| v.clone()).collect(),
                    ty: IRType::Set {
                        element: Box::new(match expr_type(operand) {
                            Some(IRType::Map { value, .. }) => value.as_ref().clone(),
                            _ => IRType::Int,
                        }),
                    },
                    span: None,
                };
                return encode_prop_value(pool, vctx, defs, ctx, &set_lit, step);
            }
            let map_val = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
            let Some(IRType::Map { key, value }) = expr_type(operand) else {
                return Err("Map::range requires a map operand".to_owned());
            };
            smt::map_range(&map_val, key, value)
        }
        IRExpr::UnOp { op, operand, .. } => {
            let v = encode_prop_value(pool, vctx, defs, ctx, operand, step)?;
            Ok(smt::unop(op, &v)?)
        }
        IRExpr::Prime { expr, .. } => encode_prop_value(pool, vctx, defs, ctx, expr, step + 1),
        // Nested quantifiers in value position — encode as Bool, wrap as SmtValue
        IRExpr::Forall { .. }
        | IRExpr::Exists { .. }
        | IRExpr::One { .. }
        | IRExpr::Lone { .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, expr, step,
        )?)),
        IRExpr::Always { body, .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, body, step,
        )?)),
        IRExpr::Until { .. } => Ok(SmtValue::Bool(encode_prop_expr(
            pool, vctx, defs, ctx, expr, step,
        )?)),
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let arr = encode_prop_value(pool, vctx, defs, ctx, map, step)?;
            let k = encode_prop_value(pool, vctx, defs, ctx, key, step)?;
            let v = encode_prop_value(pool, vctx, defs, ctx, value, step)?;
            if let Some(IRType::Map {
                value: value_ty, ..
            }) = expr_type(map)
            {
                return smt::map_store(&arr, &k, &v, value_ty);
            }
            Ok(SmtValue::Array(
                arr.as_array()?.store(&k.to_dynamic(), &v.to_dynamic()),
            ))
        }
        IRExpr::Index { map, key, ty, .. } => {
            let arr = encode_prop_value(pool, vctx, defs, ctx, map, step)?;
            let k = encode_prop_value(pool, vctx, defs, ctx, key, step)?;
            if let Some(IRType::Map { value, .. }) = expr_type(map) {
                return smt::map_lookup(&arr, &k, value);
            }
            if let Some(IRType::Seq { element }) = expr_type(map) {
                return smt::seq_index(&arr, &k, element);
            }
            Ok(smt::dynamic_to_typed_value(
                arr.as_array()?.select(&k.to_dynamic()),
                ty,
            ))
        }
        IRExpr::MapLit { entries, ty, .. } => {
            let (key_ty, val_ty) = match ty {
                IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
                _ => return Err(format!("MapLit with non-Map type: {ty:?}")),
            };
            let key_sort = smt::ir_type_to_sort(key_ty);
            let default_val = smt::map_none_dynamic(val_ty);
            let mut arr = smt::const_array(&key_sort, &default_val);
            for (k_expr, v_expr) in entries {
                let k = encode_prop_value(pool, vctx, defs, ctx, k_expr, step)?;
                let v = encode_prop_value(pool, vctx, defs, ctx, v_expr, step)?;
                arr = arr.store(&k.to_dynamic(), &smt::map_some_dynamic(val_ty, &v));
            }
            Ok(SmtValue::Array(arr))
        }
        IRExpr::SetLit { elements, ty, .. } => {
            let elem_ty = match ty {
                IRType::Set { element } => element.as_ref(),
                _ => return Err(format!("SetLit with non-Set type: {ty:?}")),
            };
            let elem_sort = smt::ir_type_to_sort(elem_ty);
            let false_val = smt::bool_val(false).to_dynamic();
            let true_val = smt::bool_val(true).to_dynamic();
            let mut arr = smt::const_array(&elem_sort, &false_val);
            for elem in elements {
                let e = encode_prop_value(pool, vctx, defs, ctx, elem, step)?;
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
                .map(|elem| encode_prop_value(pool, vctx, defs, ctx, elem, step))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(smt::seq_literal(elem_ty, &elems))
        }
        IRExpr::SetComp {
            var,
            source: Some(source),
            filter,
            projection,
            ty,
            ..
        } => {
            let elements = match source.as_ref() {
                IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements,
                _ => {
                    return Err(
                        "sourced SetComp in verifier properties currently requires a finite Set or Seq literal source"
                            .to_owned(),
                    );
                }
            };
            let IRType::Set { element } = ty else {
                return Err(format!("SetComp with non-Set result type: {ty:?}"));
            };
            let result_elem_sort = smt::ir_type_to_sort(element);
            let false_val = smt::bool_val(false).to_dynamic();
            let true_val = smt::bool_val(true).to_dynamic();
            let mut arr = smt::const_array(&result_elem_sort, &false_val);

            for element_expr in elements {
                let value = encode_prop_value(pool, vctx, defs, ctx, element_expr, step)?;
                let inner_ctx = ctx.with_local(var, value.clone());
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                let key = if let Some(proj_expr) = projection {
                    encode_prop_value(pool, vctx, defs, &inner_ctx, proj_expr, step)?.to_dynamic()
                } else {
                    value.to_dynamic()
                };
                let stored = arr.store(&key, &true_val);
                arr = smt::array_ite(&filter_val, &stored, &arr);
            }

            Ok(SmtValue::Array(arr))
        }
        IRExpr::SetComp {
            var,
            domain: IRType::Entity { name: entity_name },
            filter,
            projection,
            ty,
            ..
        } => {
            // Set comprehension over entity slots.
            // Simple: { a: E where P(a) } → Array<Int, Bool> (slot index → member)
            // Projection: { f(a) | a: E where P(a) } → Array<T, Bool> (value → member)
            let n_slots = pool.slots_for(entity_name);
            let result_elem_sort = match (projection.as_ref(), ty) {
                (Some(_), IRType::Set { element }) => smt::ir_type_to_sort(element),
                (Some(_), _) => {
                    return Err(format!(
                        "projection SetComp with non-Set result type: {ty:?}"
                    ))
                }
                (None, _) => smt::sort_int(), // simple form: slot indices are Int
            };
            let false_val = smt::bool_val(false).to_dynamic();
            let true_val = smt::bool_val(true).to_dynamic();
            let mut arr = smt::const_array(&result_elem_sort, &false_val);

            for slot in 0..n_slots {
                let active = pool.active_at(entity_name, slot, step);
                let is_active = match active {
                    Some(SmtValue::Bool(act)) => act.clone(),
                    _ => continue,
                };
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                // Condition: slot is active AND filter holds
                let cond = smt::bool_and(&[&is_active, &filter_val]);

                // Key: what to store true at
                let key = if let Some(proj_expr) = projection {
                    // Projection: store true at the projected value
                    encode_prop_value(pool, vctx, defs, &inner_ctx, proj_expr, step)?.to_dynamic()
                } else {
                    // Simple: store true at the slot index
                    smt::int_val(i64::try_from(slot).unwrap_or(0)).to_dynamic()
                };

                // Conditional store: ite(cond, store(arr, key, true), arr)
                let stored = arr.store(&key, &true_val);
                arr = smt::array_ite(&cond, &stored, &arr);
            }
            Ok(SmtValue::Array(arr))
        }
        IRExpr::SetComp { domain, .. } => {
            // Non-entity domain — should be caught by find_unsupported_scene_expr,
            // but if reached (e.g., manually constructed IR), return a fresh
            // unconstrained array rather than panicking.
            let sort = smt::ir_type_to_sort(domain);
            let false_val = smt::bool_val(false).to_dynamic();
            Ok(SmtValue::Array(smt::const_array(&sort, &false_val)))
        }
        // arithmetic aggregators over entity pools.
        //
        // For entity domains, unfold over all slots:
        // sum: Σ ite(active(s), body(s), 0)
        // product: Π ite(active(s), body(s), 1)
        // count: Σ ite(active(s) ∧ body(s), 1, 0) (body is Bool)
        // min/max: ite-chain tracking smallest/largest active body
        //
        // For fieldless-enum domains, unfold over variant indices.
        IRExpr::Aggregate {
            kind,
            var,
            domain: crate::ir::types::IRType::Entity { name: entity_name },
            body,
            in_filter,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            encode_aggregate_entity(
                pool,
                vctx,
                defs,
                ctx,
                *kind,
                var,
                entity_name,
                body,
                in_filter.as_deref(),
                n_slots,
                step,
            )
        }
        // Fieldless-enum domain: unfold over variant indices
        IRExpr::Aggregate {
            kind,
            var,
            domain: domain @ crate::ir::types::IRType::Enum { .. },
            body,
            in_filter,
            ..
        } if !domain.has_variant_fields() => {
            let n = enum_variant_count(domain);
            encode_aggregate_enum(
                pool,
                vctx,
                defs,
                ctx,
                *kind,
                var,
                body,
                in_filter.as_deref(),
                n,
                step,
            )
        }
        // Bool domain: unfold over {false, true} with proper Bool binding
        IRExpr::Aggregate {
            kind,
            var,
            domain: crate::ir::types::IRType::Bool,
            body,
            in_filter,
            ..
        } => encode_aggregate_bool(
            pool,
            vctx,
            defs,
            ctx,
            *kind,
            var,
            body,
            in_filter.as_deref(),
            step,
        ),
        // ADT enums with constructor fields: unbounded (can't enumerate)
        IRExpr::Aggregate {
            kind,
            domain: crate::ir::types::IRType::Enum { name, .. },
            ..
        } => Err(format!(
            "{kind:?} aggregator over ADT enum `{name}` is not supported — \
             ADT constructors carry data fields, making the domain unbounded; \
             use a fieldless enum or an entity pool"
        )),
        // Int, Real, String, refinement, and other unbounded domains:
        // Z3 has no native aggregator theory here, so reject with a
        // clear diagnostic suggesting a bounded domain form.
        IRExpr::Aggregate { kind, domain, .. } => Err(format!(
            "{kind:?} aggregator over `{domain:?}` domain is not supported — \
             aggregators require a bounded domain (entity pool, fieldless \
             enum, or Bool)"
        )),
        IRExpr::Card { expr: inner, .. } => encode_card(pool, vctx, defs, ctx, inner, step),
        IRExpr::App { func, .. } => {
            if let IRExpr::Var { name, .. } = func.as_ref() {
                return Err(format!(
                    "function `{name}` reached encoding without expansion \
                     (should have been caught by pre-validation)"
                ));
            }
            Err(format!(
                "unsupported App expression reached encoding: {expr:?}"
            ))
        }
        _ => Err(format!("unsupported expression reached encoding: {expr:?}")),
    }
}

fn encode_prop_match(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    scrut: &SmtValue,
    arms: &[crate::ir::types::IRMatchArm],
    step: usize,
) -> Result<SmtValue, String> {
    if arms.is_empty() {
        return Err("empty match expression".to_owned());
    }

    let mut result: Option<SmtValue> = None;
    for arm in arms.iter().rev() {
        let arm_cond = encode_pattern_cond(scrut, &arm.pattern, &ctx.locals, vctx)?;
        let mut arm_locals = ctx.locals.clone();
        bind_pattern_vars(&arm.pattern, scrut, &mut arm_locals, vctx)?;
        let arm_ctx = property_ctx_with_locals(ctx, arm_locals);

        let full_cond = if let Some(guard) = &arm.guard {
            let guard_bool = encode_prop_expr(pool, vctx, defs, &arm_ctx, guard, step)?;
            smt::bool_and(&[&arm_cond, &guard_bool])
        } else {
            arm_cond.clone()
        };

        let body_val = encode_prop_value(pool, vctx, defs, &arm_ctx, &arm.body, step)?;
        result = Some(match result {
            Some(else_val) => encode_ite(&full_cond, &body_val, &else_val)?,
            None => body_val,
        });
    }

    result.ok_or_else(|| "empty match".to_owned())
}

/// Encode cardinality (`#expr`) as a Z3 Int.
///
/// - **Literals** (`SetLit`, `SeqLit`, `MapLit`): compile-time constant.
/// - **Entity set comprehension** `#{ x: E where P(x) }`: exact bounded sum
///   `Σ ite(active[i] ∧ P(i), 1, 0)` over entity slots. This is the primary
///   use case in Abide specs (e.g., `#{ o: Order where o.status == @Pending } > 0`).
/// - **Projection comprehension** `#{ f(x) | x: E where P(x) }`: bounded sum
///   that counts matching slots (may overcount if projection collapses duplicates —
///   sound as upper bound for `> 0` checks, not exact for `== N`).
/// - **Other**: panics (should be caught by `find_unsupported_scene_expr`).
///   encode an aggregate over entity pool slots.
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_aggregate_entity(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    entity_name: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    n_slots: usize,
    step: usize,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;

    // Collect per-slot (active_flag, body_value) pairs.
    // When `in_filter` is present, AND the membership predicate with
    // the active flag so only elements in the collection contribute.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for slot in 0..n_slots {
        let active = pool.active_at(entity_name, slot, step);
        let inner_ctx = ctx.with_binding(var, entity_name, slot);
        if let Some(SmtValue::Bool(act)) = active {
            // Combine active flag with optional membership filter.
            let effective_active = if let Some(filter_expr) = in_filter {
                let membership = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter_expr, step)?;
                smt::bool_and(&[&act.clone(), &membership])
            } else {
                act.clone()
            };

            if kind == IRAggKind::Count {
                let pred = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
                slot_data.push((smt::bool_and(&[&effective_active, &pred]), smt::int_val(1)));
            } else {
                let val = encode_prop_value(pool, vctx, defs, &inner_ctx, body, step)?;
                slot_data.push((effective_active, val));
            }
        }
    }

    match kind {
        IRAggKind::Sum | IRAggKind::Count => {
            // Seed type: from first slot's body value, or from IR body type when no slots.
            let zero = slot_data
                .first()
                .map_or_else(|| agg_zero_from_ir(body), |(_, v)| agg_zero(v));
            let mut acc = zero;
            for (cond, val) in &slot_data {
                let z = agg_zero(val);
                let contrib = smt::binop("OpAdd", &acc, &ite_value(cond, val, &z))?;
                acc = contrib;
            }
            Ok(acc)
        }
        IRAggKind::Product => {
            let one = slot_data
                .first()
                .map_or_else(|| agg_one_from_ir(body), |(_, v)| agg_one(v));
            let mut acc = one;
            for (cond, val) in &slot_data {
                let o = agg_one(val);
                let contrib = smt::binop("OpMul", &acc, &ite_value(cond, val, &o))?;
                acc = contrib;
            }
            Ok(acc)
        }
        IRAggKind::Min | IRAggKind::Max => {
            if slot_data.is_empty() {
                return Err(format!(
                    "{kind:?} over empty entity pool (no slots allocated)"
                ));
            }
            // Build: for each slot, compute ite(active, body, acc) where
            // we chain from the LAST active slot backwards. The result is
            // correct when at least one slot is active; when none are,
            // we return a fresh unconstrained variable (min/max over empty
            // is undefined per ).
            //
            // Track the disjunction of all active flags. If no slot is
            // active at runtime, the result is unconstrained — properties
            // referencing it are neither provable nor disprovable, which
            // matches the "undefined" semantics.
            let is_min = kind == IRAggKind::Min;
            let op = if is_min { "OpLt" } else { "OpGt" };

            // Start with the first slot's value (guarded by its active flag).
            let mut acc = slot_data[0].1.clone();
            let mut any_active = slot_data[0].0.clone();

            for (cond, val) in slot_data.iter().skip(1) {
                let better = smt::binop(op, val, &acc)?.to_bool()?;
                let take = smt::bool_and(&[cond, &better]);
                // If this slot is active and better, take it; if this slot
                // is active but not better, keep acc; if inactive, keep acc.
                acc = ite_value(&take, val, &acc);
                // But if acc was from an inactive slot, any newly active
                // slot should override it unconditionally.
                let first_active = smt::bool_and(&[cond, &smt::bool_not(&any_active)]);
                acc = ite_value(&first_active, val, &acc);
                any_active = smt::bool_or(&[&any_active, cond]);
            }

            // When no slot is active, produce a fresh unconstrained
            // variable matching the body's type so the aggregate is truly
            // undefined (not a sentinel). The name includes entity, var,
            // kind, and step for uniqueness across multiple aggregates.
            let undef_name = format!(
                "__agg_{kind}_{entity_name}_{var}_undef_t{step}",
                kind = if is_min { "min" } else { "max" },
            );
            let undef = match &acc {
                SmtValue::Real(_) => smt::real_var(&undef_name),
                _ => smt::int_var(&undef_name),
            };
            acc = ite_value(&any_active, &acc, &undef);

            Ok(acc)
        }
    }
}

/// encode an aggregate over fieldless-enum variant indices.
/// encode an aggregate over the Bool domain {false, true}.
///
/// Binds the variable as `SmtValue::Bool` (not Int) so that body
/// expressions referencing the variable see a proper Bool value.
#[allow(clippy::too_many_arguments)]
pub(super) fn encode_aggregate_bool(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    step: usize,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;
    let bool_vals = [smt::bool_val(false), smt::bool_val(true)];

    // Collect (membership_flag, body_value) pairs, filtering via in_filter.
    // For count, body_value is always int_val(1) and the flag includes the predicate.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for bv in &bool_vals {
        let inner_ctx = ctx.with_local(var, bv.clone());
        let mut flag = smt::bool_const(true);
        if let Some(filter_expr) = in_filter {
            let membership = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter_expr, step)?;
            flag = membership;
        }
        if kind == IRAggKind::Count {
            let pred = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
            slot_data.push((smt::bool_and(&[&flag, &pred]), smt::int_val(1)));
        } else {
            let val = encode_prop_value(pool, vctx, defs, &inner_ctx, body, step)?;
            slot_data.push((flag, val));
        }
    }

    // Reuse the same fold logic as entity pools.
    match kind {
        IRAggKind::Sum | IRAggKind::Count => {
            let zero = slot_data
                .first()
                .map_or_else(|| agg_zero_from_ir(body), |(_, v)| agg_zero(v));
            let mut acc = zero;
            for (cond, val) in &slot_data {
                let z = agg_zero(val);
                acc = smt::binop("OpAdd", &acc, &ite_value(cond, val, &z))?;
            }
            Ok(acc)
        }
        IRAggKind::Product => {
            let one = slot_data
                .first()
                .map_or_else(|| agg_one_from_ir(body), |(_, v)| agg_one(v));
            let mut acc = one;
            for (cond, val) in &slot_data {
                let o = agg_one(val);
                acc = smt::binop("OpMul", &acc, &ite_value(cond, val, &o))?;
            }
            Ok(acc)
        }
        IRAggKind::Min | IRAggKind::Max => {
            if slot_data.is_empty() {
                return Err(format!("{kind:?} over empty Bool domain"));
            }
            let is_min = kind == IRAggKind::Min;
            let op = if is_min { "OpLt" } else { "OpGt" };
            let mut acc = slot_data[0].1.clone();
            let mut any_active = slot_data[0].0.clone();
            for (cond, val) in slot_data.iter().skip(1) {
                let better = smt::binop(op, val, &acc)?.to_bool()?;
                let take = smt::bool_and(&[cond, &better]);
                acc = ite_value(&take, val, &acc);
                let first_active = smt::bool_and(&[cond, &smt::bool_not(&any_active)]);
                acc = ite_value(&first_active, val, &acc);
                any_active = smt::bool_or(&[&any_active, cond]);
            }
            let undef_name = format!(
                "__agg_{}_bool_{var}_undef_t{step}",
                if is_min { "min" } else { "max" }
            );
            let undef = if ir_expr_is_real(body) {
                smt::real_var(&undef_name)
            } else {
                smt::int_var(&undef_name)
            };
            acc = ite_value(&any_active, &acc, &undef);
            Ok(acc)
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn encode_aggregate_enum(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    n: usize,
    step: usize,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;

    // Collect (filter_flag, body_value) pairs for each variant.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for idx in 0..n {
        let inner_ctx = ctx.with_local(var, smt::int_val(idx as i64));
        let mut flag = smt::bool_const(true);
        if let Some(filter_expr) = in_filter {
            let membership = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter_expr, step)?;
            flag = membership;
        }
        if kind == IRAggKind::Count {
            let pred = encode_prop_expr(pool, vctx, defs, &inner_ctx, body, step)?;
            slot_data.push((smt::bool_and(&[&flag, &pred]), smt::int_val(1)));
        } else {
            let val = encode_prop_value(pool, vctx, defs, &inner_ctx, body, step)?;
            slot_data.push((flag, val));
        }
    }

    // If no in_filter, all flags are `true` and the fold is equivalent
    // to the original direct encoding.
    match kind {
        IRAggKind::Sum | IRAggKind::Count => {
            let zero = slot_data
                .first()
                .map_or_else(|| agg_zero_from_ir(body), |(_, v)| agg_zero(v));
            let mut acc = zero;
            for (cond, val) in &slot_data {
                let z = agg_zero(val);
                acc = smt::binop("OpAdd", &acc, &ite_value(cond, val, &z))?;
            }
            Ok(acc)
        }
        IRAggKind::Product => {
            let one = slot_data
                .first()
                .map_or_else(|| agg_one_from_ir(body), |(_, v)| agg_one(v));
            let mut acc = one;
            for (cond, val) in &slot_data {
                let o = agg_one(val);
                acc = smt::binop("OpMul", &acc, &ite_value(cond, val, &o))?;
            }
            Ok(acc)
        }
        IRAggKind::Min | IRAggKind::Max => {
            if slot_data.is_empty() {
                return Err(format!("{kind:?} over empty enum domain"));
            }
            let is_min = kind == IRAggKind::Min;
            let op = if is_min { "OpLt" } else { "OpGt" };
            let mut acc = slot_data[0].1.clone();
            let mut any_active = slot_data[0].0.clone();
            for (cond, val) in slot_data.iter().skip(1) {
                let better = smt::binop(op, val, &acc)?.to_bool()?;
                let take = smt::bool_and(&[cond, &better]);
                acc = ite_value(&take, val, &acc);
                let first_active = smt::bool_and(&[cond, &smt::bool_not(&any_active)]);
                acc = ite_value(&first_active, val, &acc);
                any_active = smt::bool_or(&[&any_active, cond]);
            }
            // When no element passes the filter, produce undefined.
            let undef_name = format!(
                "__agg_{}_enum_{var}_undef_t{step}",
                if is_min { "min" } else { "max" },
            );
            let undef = if ir_expr_is_real(body) {
                smt::real_var(&undef_name)
            } else {
                smt::int_var(&undef_name)
            };
            acc = ite_value(&any_active, &acc, &undef);
            Ok(acc)
        }
    }
}

/// Return the additive identity (0) matching the type of `sample`.
pub(super) fn agg_zero(sample: &SmtValue) -> SmtValue {
    match sample {
        SmtValue::Real(_) => smt::real_val(0, 1),
        _ => smt::int_val(0),
    }
}

/// Return the multiplicative identity (1) matching the type of `sample`.
pub(super) fn agg_one(sample: &SmtValue) -> SmtValue {
    match sample {
        SmtValue::Real(_) => smt::real_val(1, 1),
        _ => smt::int_val(1),
    }
}

/// Typed zero for an aggregate, inferred from the IR body expression.
pub(super) fn agg_zero_from_ir(body: &IRExpr) -> SmtValue {
    if ir_expr_is_real(body) {
        smt::real_val(0, 1)
    } else {
        smt::int_val(0)
    }
}

/// Typed one for an aggregate, inferred from the IR body expression.
pub(super) fn agg_one_from_ir(body: &IRExpr) -> SmtValue {
    if ir_expr_is_real(body) {
        smt::real_val(1, 1)
    } else {
        smt::int_val(1)
    }
}

/// Check if an IR expression produces a Real/Float type by inspecting
/// the type annotation on its outermost node (when available).
pub(super) fn ir_expr_is_real(expr: &IRExpr) -> bool {
    use crate::ir::types::IRType;
    matches!(
        expr,
        IRExpr::Lit {
            ty: IRType::Real | IRType::Float,
            ..
        } | IRExpr::Var {
            ty: IRType::Real | IRType::Float,
            ..
        } | IRExpr::BinOp {
            ty: IRType::Real | IRType::Float,
            ..
        } | IRExpr::UnOp {
            ty: IRType::Real | IRType::Float,
            ..
        } | IRExpr::Field {
            ty: IRType::Real | IRType::Float,
            ..
        }
    )
}

pub(super) fn ite_value(cond: &Bool, then_val: &SmtValue, else_val: &SmtValue) -> SmtValue {
    match (then_val, else_val) {
        (SmtValue::Int(t), SmtValue::Int(e)) => SmtValue::Int(smt::int_ite(cond, t, e)),
        (SmtValue::Real(t), SmtValue::Real(e)) => SmtValue::Real(smt::real_ite(cond, t, e)),
        (SmtValue::Bool(t), SmtValue::Bool(e)) => SmtValue::Bool(smt::bool_ite(cond, t, e)),
        // Mixed types should not occur after type checking.
        _ => panic!("ite_value: mismatched SmtValue types"),
    }
}

pub(super) fn encode_card(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    inner: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    match inner {
        IRExpr::SetLit { elements, .. } => {
            let unique: std::collections::HashSet<String> =
                elements.iter().map(|e| format!("{e:?}")).collect();
            Ok(smt::int_val(i64::try_from(unique.len()).unwrap_or(0)))
        }
        IRExpr::SeqLit { elements, .. } => {
            Ok(smt::int_val(i64::try_from(elements.len()).unwrap_or(0)))
        }
        IRExpr::MapLit { entries, .. } => {
            let unique_keys: std::collections::HashSet<String> =
                entries.iter().map(|(k, _)| format!("{k:?}")).collect();
            Ok(smt::int_val(i64::try_from(unique_keys.len()).unwrap_or(0)))
        }
        // Entity-domain set comprehension: bounded sum over slots
        IRExpr::SetComp {
            var,
            domain: IRType::Entity { name: entity_name },
            filter,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut sum_terms: Vec<Int> = Vec::new();
            let one = smt::int_lit(1);
            let zero = smt::int_lit(0);

            for slot in 0..n_slots {
                let is_active = match pool.active_at(entity_name, slot, step) {
                    Some(SmtValue::Bool(act)) => act.clone(),
                    _ => continue,
                };
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                let cond = smt::bool_and(&[&is_active, &filter_val]);
                sum_terms.push(smt::int_ite(&cond, &one, &zero));
            }

            if sum_terms.is_empty() {
                return Ok(smt::int_val(0));
            }
            let refs: Vec<&Int> = sum_terms.iter().collect();
            Ok(SmtValue::Int(smt::int_add(&refs)))
        }
        _ => {
            if let Some(IRType::Seq { element }) = expr_type(inner) {
                let seq = encode_prop_value(pool, vctx, defs, ctx, inner, step)?;
                smt::seq_length(&seq, element)
            } else {
                Err(format!("unsupported cardinality expression: {inner:?}"))
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::needless_borrows_for_generic_args)]
mod tests {
    use super::*;
    use crate::ir::types::{IREntity, IRField, IRProgram, IRSystem, IRType, IRVariant, LitVal};
    use crate::verify::harness::create_slot_pool;

    fn empty_ir() -> IRProgram {
        IRProgram {
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
        }
    }

    fn empty_pool() -> SlotPool {
        let scopes = HashMap::new();
        create_slot_pool(&[], &scopes, 0)
    }

    fn make_order_entity() -> IREntity {
        IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: None,
            }],
            transitions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        }
    }

    #[test]
    fn precondition_obligation_tracking_reports_violations() {
        clear_prop_precondition_obligations();
        record_prop_precondition_obligation(smt::bool_const(true), "ok".to_owned());
        assert_eq!(check_prop_precondition_obligations(), None);

        clear_prop_precondition_obligations();
        record_prop_precondition_obligation(smt::bool_const(false), "bad".to_owned());
        let err = check_prop_precondition_obligations().expect("expected violation");
        assert!(err.contains("bad"));
        assert!(take_prop_precondition_obligations().is_empty());
    }

    #[test]
    fn property_ctx_builders_preserve_and_extend_bindings() {
        let mut ranges = HashMap::new();
        ranges.insert(
            "orders".to_owned(),
            crate::verify::scope::VerifyStoreRange {
                entity_type: "Order".to_owned(),
                start_slot: 2,
                slot_count: 3,
                min_active: 0,
                max_active: 3,
            },
        );
        let mut given = HashMap::new();
        given.insert("g".to_owned(), ("Order".to_owned(), 4usize));

        let systems = vec![
            IRSystem {
                name: "UI".to_owned(),
                store_params: vec![],
                fields: vec![
                    IRField {
                        name: "screen".to_owned(),
                        ty: IRType::Int,
                        default: None,
                        initial_constraint: None,
                    },
                    IRField {
                        name: "ui.screen".to_owned(),
                        ty: IRType::Int,
                        default: None,
                        initial_constraint: None,
                    },
                ],
                entities: vec![],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            },
            IRSystem {
                name: "Other".to_owned(),
                store_params: vec![],
                fields: vec![IRField {
                    name: "screen".to_owned(),
                    ty: IRType::Int,
                    default: None,
                    initial_constraint: None,
                }],
                entities: vec![],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            },
        ];

        let ctx = PropertyCtx::new()
            .with_store_ranges(ranges)
            .with_binding("o", "Order", 1)
            .with_given_bindings(&given)
            .with_local("n", smt::int_val(7))
            .with_system_fields(&systems);

        assert_eq!(ctx.bindings.get("o"), Some(&("Order".to_owned(), 1)));
        assert_eq!(ctx.bindings.get("g"), Some(&("Order".to_owned(), 4)));
        assert!(matches!(ctx.locals.get("n"), Some(SmtValue::Int(_))));
        assert_eq!(ctx.store_ranges["orders"].start_slot, 2);
        assert_eq!(
            ctx.system_fields.get("screen").map(String::as_str),
            Some("")
        );
        assert_eq!(
            ctx.system_fields.get("ui.screen").map(String::as_str),
            Some("UI")
        );
        assert_eq!(
            ctx.system_struct_bases.get("ui").map(String::as_str),
            Some("UI")
        );
    }

    #[test]
    fn aggregate_helpers_cover_numeric_shapes() {
        assert!(matches!(agg_zero(&smt::int_val(3)), SmtValue::Int(_)));
        assert!(matches!(agg_one(&smt::int_val(3)), SmtValue::Int(_)));
        assert!(matches!(agg_zero(&smt::real_val(3, 1)), SmtValue::Real(_)));
        assert!(matches!(agg_one(&smt::real_val(3, 1)), SmtValue::Real(_)));

        let int_expr = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        };
        let real_expr = IRExpr::Lit {
            ty: IRType::Real,
            value: LitVal::Real { value: 1.0 },
            span: None,
        };
        assert!(!ir_expr_is_real(&int_expr));
        assert!(ir_expr_is_real(&real_expr));
        assert!(matches!(agg_zero_from_ir(&int_expr), SmtValue::Int(_)));
        assert!(matches!(agg_one_from_ir(&int_expr), SmtValue::Int(_)));
        assert!(matches!(agg_zero_from_ir(&real_expr), SmtValue::Real(_)));
        assert!(matches!(agg_one_from_ir(&real_expr), SmtValue::Real(_)));

        let cond = smt::bool_const(true);
        assert!(matches!(
            ite_value(&cond, &smt::int_val(1), &smt::int_val(2)),
            SmtValue::Int(_)
        ));
        assert!(matches!(
            ite_value(&cond, &smt::bool_val(true), &smt::bool_val(false)),
            SmtValue::Bool(_)
        ));
        assert!(matches!(
            ite_value(&cond, &smt::real_val(1, 1), &smt::real_val(2, 1)),
            SmtValue::Real(_)
        ));

        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();
        let bool_var = IRExpr::Var {
            name: "b".to_owned(),
            ty: IRType::Bool,
            span: None,
        };
        let bool_count = encode_aggregate_bool(
            &pool,
            &vctx,
            &defs,
            &ctx,
            crate::ir::types::IRAggKind::Count,
            "b",
            &bool_var,
            None,
            0,
        )
        .expect("bool count");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            bool_count.as_int().expect("count int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);

        let bool_max_body = IRExpr::IfElse {
            cond: Box::new(bool_var),
            then_body: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            else_body: Some(Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            })),
            span: None,
        };
        let bool_max = encode_aggregate_bool(
            &pool,
            &vctx,
            &defs,
            &ctx,
            crate::ir::types::IRAggKind::Max,
            "b",
            &bool_max_body,
            None,
            0,
        )
        .expect("bool max");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            bool_max.as_int().expect("max int"),
            &smt::int_lit(2),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn prop_domain_predicate_and_encode_card_cover_literal_cases() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();

        let refinement = IRType::Refinement {
            base: Box::new(IRType::Int),
            predicate: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "$".to_owned(),
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
            }),
        };
        let pred = prop_domain_predicate(&refinement, &smt::int_val(0), &ctx, &vctx, &defs)
            .expect("refinement predicate")
            .expect("expected guard");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&pred));
        assert_eq!(solver.check(), SatResult::Unsat);

        let set_card = encode_card(
            &pool,
            &vctx,
            &defs,
            &ctx,
            &IRExpr::SetLit {
                elements: vec![
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    },
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    },
                ],
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            },
            0,
        )
        .expect("set card");
        let seq_card = encode_card(
            &pool,
            &vctx,
            &defs,
            &ctx,
            &IRExpr::SeqLit {
                elements: vec![
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    },
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },
                        span: None,
                    },
                ],
                ty: IRType::Seq {
                    element: Box::new(IRType::Int),
                },
                span: None,
            },
            0,
        )
        .expect("seq card");
        let map_card = encode_card(
            &pool,
            &vctx,
            &defs,
            &ctx,
            &IRExpr::MapLit {
                entries: vec![
                    (
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                        IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    ),
                    (
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                        IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: false },
                            span: None,
                        },
                    ),
                ],
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Bool),
                },
                span: None,
            },
            0,
        )
        .expect("map card");

        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            set_card.as_int().expect("set int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);

        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            seq_card.as_int().expect("seq int"),
            &smt::int_lit(2),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);

        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            map_card.as_int().expect("map int"),
            &smt::int_lit(1),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_covers_entity_quantifier_branches() {
        let entity = make_order_entity();
        let ir = IRProgram {
            entities: vec![entity.clone()],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 2usize);
        let pool = create_slot_pool(&[entity], &scopes, 0);
        let ctx = PropertyCtx::new();

        let eq_one = |name: &str| IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: name.to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let forall_expr = IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "o".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
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
            }),
            span: None,
        };
        let forall =
            encode_prop_expr(&pool, &vctx, &defs, &ctx, &forall_expr, 0).expect("forall entity");
        let solver = AbideSolver::new();
        solver.assert(forall);
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(
            pool.active_at("Order", 1, 0)
                .expect("active1")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 0, "status", 0)
                .expect("status0")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 1, "status", 0)
                .expect("status1")
                .as_int()
                .expect("int"),
            &smt::int_lit(0),
        ));
        assert_eq!(solver.check(), SatResult::Sat);

        let exists_expr = IRExpr::Exists {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(eq_one("o")),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &exists_expr, 0).is_ok());

        let one_expr = IRExpr::One {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(eq_one("o")),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &one_expr, 0).is_ok());

        let lone_expr = IRExpr::Lone {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(eq_one("o")),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &lone_expr, 0).is_ok());
    }

    #[test]
    fn encode_prop_expr_respects_store_scoped_entity_quantifiers() {
        let entity = make_order_entity();
        let ir = IRProgram {
            entities: vec![entity.clone()],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 2usize);
        let pool = create_slot_pool(&[entity], &scopes, 0);
        let mut ranges = HashMap::new();
        ranges.insert(
            "pending".to_owned(),
            crate::verify::scope::VerifyStoreRange {
                entity_type: "Order".to_owned(),
                start_slot: 0,
                slot_count: 1,
                min_active: 0,
                max_active: 1,
            },
        );
        ranges.insert(
            "archived".to_owned(),
            crate::verify::scope::VerifyStoreRange {
                entity_type: "Order".to_owned(),
                start_slot: 1,
                slot_count: 1,
                min_active: 0,
                max_active: 1,
            },
        );
        let ctx = PropertyCtx::new().with_store_ranges(ranges);

        let order_var = |name: &str| IRExpr::Var {
            name: name.to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        };
        let membership = |store_name: &str, var: &str| IRExpr::Index {
            map: Box::new(IRExpr::Var {
                name: store_name.to_owned(),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Bool),
                },
                span: None,
            }),
            key: Box::new(order_var(var)),
            ty: IRType::Bool,
            span: None,
        };
        let status_is_one = |var: &str| IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(order_var(var)),
                field: "status".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let forall_pending = IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(membership("pending", "o")),
                right: Box::new(status_is_one("o")),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };
        let exists_pending = IRExpr::Exists {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(membership("pending", "o")),
                right: Box::new(status_is_one("o")),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };
        let one_pending = IRExpr::One {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(membership("pending", "o")),
                right: Box::new(status_is_one("o")),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };
        let lone_pending = IRExpr::Lone {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(membership("pending", "o")),
                right: Box::new(status_is_one("o")),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };

        let forall = encode_prop_expr(&pool, &vctx, &defs, &ctx, &forall_pending, 0)
            .expect("store-scoped forall");
        let exists = encode_prop_expr(&pool, &vctx, &defs, &ctx, &exists_pending, 0)
            .expect("store-scoped exists");
        let one =
            encode_prop_expr(&pool, &vctx, &defs, &ctx, &one_pending, 0).expect("store-scoped one");
        let lone = encode_prop_expr(&pool, &vctx, &defs, &ctx, &lone_pending, 0)
            .expect("store-scoped lone");

        let solver = AbideSolver::new();
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(
            pool.active_at("Order", 1, 0)
                .expect("active1")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 0, "status", 0)
                .expect("status0")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 1, "status", 0)
                .expect("status1")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));

        solver.assert(&smt::bool_not(&forall));
        assert_eq!(solver.check(), SatResult::Unsat);

        let solver = AbideSolver::new();
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(
            pool.active_at("Order", 1, 0)
                .expect("active1")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 0, "status", 0)
                .expect("status0")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 1, "status", 0)
                .expect("status1")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::bool_not(&exists));
        assert_eq!(solver.check(), SatResult::Unsat);

        let solver = AbideSolver::new();
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(
            pool.active_at("Order", 1, 0)
                .expect("active1")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 0, "status", 0)
                .expect("status0")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 1, "status", 0)
                .expect("status1")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::bool_not(&one));
        assert_eq!(solver.check(), SatResult::Unsat);

        let solver = AbideSolver::new();
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(
            pool.active_at("Order", 1, 0)
                .expect("active1")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 0, "status", 0)
                .expect("status0")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::int_eq(
            pool.field_at("Order", 1, "status", 0)
                .expect("status1")
                .as_int()
                .expect("int"),
            &smt::int_lit(1),
        ));
        solver.assert(&smt::bool_not(&lone));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_covers_non_entity_quantifier_branches() {
        let ir = IRProgram {
            types: vec![crate::ir::types::IRTypeEntry {
                name: "Status".to_owned(),
                ty: IRType::Enum {
                    name: "Status".to_owned(),
                    variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
                },
            }],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let enum_domain = IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
        };

        let bool_forall = IRExpr::Forall {
            var: "b".to_owned(),
            domain: IRType::Bool,
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "b".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Var {
                        name: "b".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &bool_forall, 0).is_ok());

        let enum_exists = IRExpr::Exists {
            var: "s".to_owned(),
            domain: enum_domain.clone(),
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "s".to_owned(),
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
            }),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &enum_exists, 0).is_ok());

        let enum_one = IRExpr::One {
            var: "s".to_owned(),
            domain: enum_domain.clone(),
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "s".to_owned(),
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
            }),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &enum_one, 0).is_ok());

        let enum_lone = IRExpr::Lone {
            var: "s".to_owned(),
            domain: enum_domain,
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "s".to_owned(),
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
            }),
            span: None,
        };
        assert!(encode_prop_expr(&pool, &vctx, &defs, &ctx, &enum_lone, 0).is_ok());
    }

    #[test]
    fn encode_prop_expr_with_ctx_enforces_scalar_choose_predicates() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let expr = IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "n".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "n".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "n".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        };

        let encoded =
            encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &expr, 0).expect("encode choose");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn path_guard_stack_and_expr_type_cover_local_helper_branches() {
        clear_path_guard_stack();
        push_path_guard(smt::bool_const(true));
        push_path_guard(smt::bool_const(false));
        let guard = current_path_guard();
        let solver = AbideSolver::new();
        solver.assert(&guard);
        assert_eq!(solver.check(), SatResult::Unsat);
        pop_path_guard();
        pop_path_guard();

        let prime = IRExpr::Prime {
            expr: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: crate::ir::types::LitVal::Int { value: 1 },
                span: None,
            }),
            span: None,
        };
        assert_eq!(expr_type(&prime), Some(&IRType::Int));

        let let_expr = IRExpr::Let {
            bindings: vec![],
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: crate::ir::types::LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        };
        assert_eq!(expr_type(&let_expr), Some(&IRType::Bool));
        assert!(expr_type(&IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Open".to_owned(),
            args: vec![],
            span: None,
        })
        .is_none());
    }
}
