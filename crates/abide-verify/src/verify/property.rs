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
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use super::smt::{AbideSolver, Bool, Dynamic, Int, SatResult};

use crate::ir::types::{IRExpr, IRSystem, IRType};

use super::context::VerifyContext;
use super::defenv;
use super::encode::{
    bind_pattern_vars, build_domain_predicate, build_z3_quantifier, encode_ite,
    encode_pattern_cond, enum_variant_count, make_z3_bound_var_ctx, PureEncodingScope,
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
        | IRExpr::Tuple { ty, .. }
        | IRExpr::MapLit { ty, .. }
        | IRExpr::SetComp { ty, .. } => Some(ty),
        IRExpr::Prime { expr, .. } => expr_type(expr),
        IRExpr::Let { body, .. } => expr_type(body),
        IRExpr::Ctor { .. } => None,
        _ => None,
    }
}

fn finite_domain_values(domain: &IRType) -> Option<Vec<SmtValue>> {
    match domain {
        IRType::Bool => Some(vec![smt::bool_val(false), smt::bool_val(true)]),
        domain @ IRType::Enum { .. } if !domain.has_variant_fields() => Some(
            (0..enum_variant_count(domain))
                .map(|idx| smt::int_val(idx as i64))
                .collect(),
        ),
        _ => None,
    }
}

fn finite_domain_values_with_payloads(
    vctx: &VerifyContext,
    domain: &IRType,
) -> Option<Vec<SmtValue>> {
    finite_domain_values(domain).or_else(|| finite_payload_enum_values(vctx, domain))
}

fn ir_type_to_prop_sort(vctx: &VerifyContext, ty: &IRType) -> smt::Sort {
    match ty {
        IRType::Enum { name, .. } => vctx
            .adt_sorts
            .get(name)
            .map(smt::DatatypeSort::sort)
            .unwrap_or_else(|| smt::ir_type_to_sort(ty)),
        IRType::Refinement { base, .. } => ir_type_to_prop_sort(vctx, base),
        _ => smt::ir_type_to_sort(ty),
    }
}

fn finite_payload_enum_values(vctx: &VerifyContext, domain: &IRType) -> Option<Vec<SmtValue>> {
    let IRType::Enum { name, variants } = domain else {
        return None;
    };
    if !domain.has_variant_fields() {
        return None;
    }
    let dt = vctx.adt_sorts.get(name)?;
    let mut values = Vec::new();
    for variant in variants {
        let constructor = dt
            .variants
            .iter()
            .find(|candidate| smt::func_decl_name(&candidate.constructor) == variant.name)?;
        let field_values = enumerate_finite_smt_field_values(vctx, &variant.fields)?;
        for fields in field_values {
            let args: Vec<Dynamic> = fields.iter().map(SmtValue::to_dynamic).collect();
            let arg_refs: Vec<&Dynamic> = args.iter().collect();
            values.push(dynamic_to_smt_value(smt::func_decl_apply(
                &constructor.constructor,
                &arg_refs,
            )));
        }
    }
    Some(values)
}

fn enumerate_finite_smt_field_values(
    vctx: &VerifyContext,
    fields: &[crate::ir::types::IRVariantField],
) -> Option<Vec<Vec<SmtValue>>> {
    let mut out = vec![Vec::new()];
    for field in fields {
        let values = finite_domain_values_with_payloads(vctx, &field.ty)?;
        let mut next = Vec::new();
        for prefix in &out {
            for value in &values {
                let mut extended = prefix.clone();
                extended.push(value.clone());
                next.push(extended);
            }
        }
        out = next;
    }
    Some(out)
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
    /// `VerifyStoreRange { entity_type, start_slot, min_active, slot_count }`.
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

#[derive(Clone, Copy)]
pub(super) struct PropertyEncodingCtx<'a> {
    pool: &'a SlotPool,
    vctx: &'a VerifyContext,
    defs: &'a defenv::DefEnv,
    property: &'a PropertyCtx,
    step: usize,
}

impl<'a> PropertyEncodingCtx<'a> {
    fn with_property<'b>(&'b self, property: &'b PropertyCtx) -> PropertyEncodingCtx<'b> {
        PropertyEncodingCtx {
            pool: self.pool,
            vctx: self.vctx,
            defs: self.defs,
            property,
            step: self.step,
        }
    }
}

#[derive(Clone, Copy)]
struct ProjectionMembership<'a> {
    bindings: &'a [crate::ir::types::LetBinding],
    body: &'a IRExpr,
    key: &'a SmtValue,
}

#[derive(Clone, Copy)]
struct MatchRelation<'a> {
    match_expr: &'a IRExpr,
    other: &'a IRExpr,
    op: &'a str,
    match_on_left: bool,
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
    build_domain_predicate(
        domain,
        bound_var,
        PureEncodingScope {
            env: &env,
            vctx,
            defs,
            precheck: None,
        },
    )
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
            let bound_var = make_z3_bound_var_ctx(var, domain, Some(vctx))?;
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
            let bound_var = make_z3_bound_var_ctx(var, domain, Some(vctx))?;
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
            let x_var = make_z3_bound_var_ctx(var, domain, Some(vctx))?;
            let x_ctx = ctx.with_local(var, x_var.clone());
            let p_x = encode_prop_expr(pool, vctx, defs, &x_ctx, body, step)?;
            let d_x = prop_domain_predicate(domain, &x_var, &x_ctx, vctx, defs)?;
            let x_satisfies = match &d_x {
                Some(dp) => smt::bool_and(&[dp, &p_x]),
                None => p_x.clone(),
            };

            let y_name = format!("{var}__unique");
            let y_var = make_z3_bound_var_ctx(&y_name, domain, Some(vctx))?;
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
            let x_var = make_z3_bound_var_ctx(var, domain, Some(vctx))?;
            let x_ctx = ctx.with_local(var, x_var.clone());
            let p_x = encode_prop_expr(pool, vctx, defs, &x_ctx, body, step)?;
            let d_x = prop_domain_predicate(domain, &x_var, &x_ctx, vctx, defs)?;

            let y_name = format!("{var}__unique");
            let y_var = make_z3_bound_var_ctx(&y_name, domain, Some(vctx))?;
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
        // `always P` at a single BMC step is P; the caller supplies the
        // universal step iteration. Future-time liveness forms must be routed
        // to the lasso/Buchi encoders instead of weakened at a single step.
        IRExpr::Always { body, .. } => encode_prop_expr(pool, vctx, defs, ctx, body, step),
        IRExpr::Eventually { .. } | IRExpr::Until { .. } => Err(
            "future-time temporal property reached single-step property encoder; route through lasso/Buchi temporal verification".to_owned(),
        ),
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
        IRExpr::Index { map, key, .. } => {
            if let Some(member) =
                encode_setcomp_projection_membership(pool, vctx, defs, ctx, map, key, step)?
            {
                return Ok(member);
            }
            let val = encode_prop_value(pool, vctx, defs, ctx, expr, step)?;
            Ok(val.to_bool()?)
        }
        IRExpr::BinOp {
            op, left, right, ..
        } if !logical_binop(op) && op != "OpMapHas" => {
            if let Some(encoded) = encode_match_relation_with_local_choose(
                PropertyEncodingCtx {
                    pool,
                    vctx,
                    defs,
                    property: ctx,
                    step,
                },
                MatchRelation {
                    match_expr: left,
                    other: right,
                    op,
                    match_on_left: true,
                },
            )? {
                return Ok(encoded);
            }
            if let Some(encoded) = encode_match_relation_with_local_choose(
                PropertyEncodingCtx {
                    pool,
                    vctx,
                    defs,
                    property: ctx,
                    step,
                },
                MatchRelation {
                    match_expr: right,
                    other: left,
                    op,
                    match_on_left: false,
                },
            )? {
                return Ok(encoded);
            }
            let enc = PropertyEncodingCtx {
                pool,
                vctx,
                defs,
                property: ctx,
                step,
            };
            let l = encode_prop_value_for_comparison(&enc, left, right)?;
            let r = encode_prop_value_for_comparison(&enc, right, left)?;
            Ok(smt::binop(op, &l, &r)?.to_bool()?)
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
            let enc = PropertyEncodingCtx {
                pool,
                vctx,
                defs,
                property: ctx,
                step,
            };
            let l = encode_prop_value_for_comparison(&enc, left, right)?;
            let r = encode_prop_value_for_comparison(&enc, right, left)?;
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
                let witness = make_z3_bound_var_ctx(&fresh, domain, Some(vctx))?;
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

fn property_expr_mentions_var(expr: &IRExpr, target: &str) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == target,
        IRExpr::Lit { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => false,
        IRExpr::Prime { expr, .. }
        | IRExpr::Assert { expr, .. }
        | IRExpr::Assume { expr, .. }
        | IRExpr::Field { expr, .. }
        | IRExpr::Card { expr, .. }
        | IRExpr::UnOp { operand: expr, .. } => property_expr_mentions_var(expr, target),
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            property_expr_mentions_var(left, target) || property_expr_mentions_var(right, target)
        }
        IRExpr::App { func, arg, .. } => {
            property_expr_mentions_var(func, target) || property_expr_mentions_var(arg, target)
        }
        IRExpr::Let { bindings, body, .. } => {
            bindings
                .iter()
                .any(|binding| property_expr_mentions_var(&binding.expr, target))
                || property_expr_mentions_var(body, target)
        }
        IRExpr::Choose { var, predicate, .. } => {
            var != target
                && predicate
                    .as_ref()
                    .is_some_and(|predicate| property_expr_mentions_var(predicate, target))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            property_expr_mentions_var(cond, target)
                || property_expr_mentions_var(then_body, target)
                || else_body
                    .as_ref()
                    .is_some_and(|body| property_expr_mentions_var(body, target))
        }
        IRExpr::Ctor { args, .. } => args
            .iter()
            .any(|(_, arg)| property_expr_mentions_var(arg, target)),
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            property_expr_mentions_var(map, target)
                || property_expr_mentions_var(key, target)
                || property_expr_mentions_var(value, target)
        }
        IRExpr::Index { map, key, .. } => {
            property_expr_mentions_var(map, target) || property_expr_mentions_var(key, target)
        }
        IRExpr::SetLit {
            elements: items, ..
        }
        | IRExpr::SeqLit {
            elements: items, ..
        }
        | IRExpr::Tuple {
            elements: items, ..
        } => items
            .iter()
            .any(|item| property_expr_mentions_var(item, target)),
        IRExpr::MapLit { entries, .. } => entries.iter().any(|(key, value)| {
            property_expr_mentions_var(key, target) || property_expr_mentions_var(value, target)
        }),
        _ => true,
    }
}

fn bool_literal(value: bool) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Bool,
        value: crate::ir::types::LitVal::Bool { value },
        span: None,
    }
}

fn not_expr(expr: IRExpr) -> IRExpr {
    IRExpr::UnOp {
        op: "OpNot".to_owned(),
        operand: Box::new(expr),
        ty: IRType::Bool,
        span: None,
    }
}

fn implies_expr(left: IRExpr, right: IRExpr) -> IRExpr {
    IRExpr::BinOp {
        op: "OpImplies".to_owned(),
        left: Box::new(left),
        right: Box::new(right),
        ty: IRType::Bool,
        span: None,
    }
}

fn guard_branch_choose_bindings(
    bindings: Vec<crate::ir::types::LetBinding>,
    branch_guard: &IRExpr,
) -> Vec<crate::ir::types::LetBinding> {
    bindings
        .into_iter()
        .map(|binding| {
            let IRExpr::Choose {
                var,
                domain,
                predicate,
                ty,
                span,
            } = binding.expr
            else {
                return binding;
            };
            let predicate_body = predicate
                .map(|predicate| *predicate)
                .unwrap_or_else(|| bool_literal(true));
            crate::ir::types::LetBinding {
                name: binding.name,
                ty: binding.ty,
                expr: IRExpr::Choose {
                    var,
                    domain,
                    predicate: Some(Box::new(implies_expr(branch_guard.clone(), predicate_body))),
                    ty,
                    span,
                },
            }
        })
        .collect()
}

fn pattern_binds_vars(pattern: &crate::ir::types::IRPattern) -> bool {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PVar { .. } => true,
        IRPattern::PCtor { fields, .. } => fields
            .iter()
            .any(|field| pattern_binds_vars(&field.pattern)),
        IRPattern::POr { left, right } => pattern_binds_vars(left) || pattern_binds_vars(right),
        IRPattern::PWild => false,
    }
}

fn collect_pattern_vars(pattern: &crate::ir::types::IRPattern, out: &mut Vec<String>) {
    use crate::ir::types::IRPattern;
    match pattern {
        IRPattern::PVar { name } => out.push(name.clone()),
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

fn bindings_mention_any_pattern_var(
    bindings: &[crate::ir::types::LetBinding],
    pattern: &crate::ir::types::IRPattern,
) -> bool {
    let mut vars = Vec::new();
    collect_pattern_vars(pattern, &mut vars);
    bindings.iter().any(|binding| {
        vars.iter()
            .any(|var| property_expr_mentions_var(&binding.expr, var))
    })
}

fn match_arm_condition_expr(scrutinee: IRExpr, arm: &crate::ir::types::IRMatchArm) -> IRExpr {
    IRExpr::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            crate::ir::types::IRMatchArm {
                pattern: arm.pattern.clone(),
                guard: arm.guard.clone(),
                body: bool_literal(true),
            },
            crate::ir::types::IRMatchArm {
                pattern: crate::ir::types::IRPattern::PWild,
                guard: None,
                body: bool_literal(false),
            },
        ],
        span: None,
    }
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
        IRExpr::Card { expr, .. } => {
            let (bindings, expr) = normalize_verifier_choose_term(expr)?;
            Ok((
                bindings,
                IRExpr::Card {
                    expr: Box::new(expr),
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
            let hoist_projection_bindings = !projection_bindings.is_empty()
                && projection_bindings.iter().all(|binding| {
                    matches!(binding.expr, IRExpr::Choose { .. })
                        && !property_expr_mentions_var(&binding.expr, var)
                });
            let projection = projection.map(|expr| {
                if hoist_projection_bindings {
                    expr
                } else {
                    Box::new(wrap_let_expr(projection_bindings.clone(), *expr))
                }
            });
            let outer_bindings = if hoist_projection_bindings {
                projection_bindings
            } else {
                Vec::new()
            };
            Ok((
                outer_bindings,
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
            let cond = normalize_verifier_choose_expr(cond)?;
            let (then_bindings, then_body) = normalize_verifier_choose_term(then_body)?;
            let (else_bindings, else_body) = else_body
                .as_ref()
                .map(|body| normalize_verifier_choose_term(body))
                .transpose()?
                .map_or((Vec::new(), None), |(bindings, expr)| {
                    (bindings, Some(Box::new(expr)))
                });
            let mut bindings = guard_branch_choose_bindings(then_bindings, &cond);
            let else_guard = not_expr(cond.clone());
            bindings.extend(guard_branch_choose_bindings(else_bindings, &else_guard));
            Ok((
                bindings,
                IRExpr::IfElse {
                    cond: Box::new(cond),
                    then_body: Box::new(then_body),
                    else_body,
                    span: None,
                },
            ))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let (scrutinee_bindings, scrutinee) = normalize_verifier_choose_term(scrutinee)?;
            let mut hoisted_bindings = scrutinee_bindings;
            let mut new_arms = Vec::with_capacity(arms.len());
            for arm in arms {
                let (body_bindings, body) = normalize_verifier_choose_term(&arm.body)?;
                let has_pattern_dependent_choose = bindings_contain_choose(&body_bindings)
                    && pattern_binds_vars(&arm.pattern)
                    && bindings_mention_any_pattern_var(&body_bindings, &arm.pattern);
                let body = if has_pattern_dependent_choose {
                    wrap_let_expr(body_bindings, body)
                } else {
                    let guard = match_arm_condition_expr(scrutinee.clone(), arm);
                    hoisted_bindings.extend(guard_branch_choose_bindings(body_bindings, &guard));
                    body
                };
                new_arms.push(crate::ir::types::IRMatchArm {
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(normalize_verifier_choose_expr)
                        .transpose()?,
                    body,
                });
            }
            Ok((
                hoisted_bindings,
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

fn encode_prop_value_with_choose_constraints(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<(SmtValue, Vec<Bool>), String> {
    let (bindings, body) = normalize_verifier_choose_term(expr)?;
    let normalized = wrap_let_expr(bindings, body);
    encode_prop_value_with_choose_witnesses(pool, vctx, defs, ctx, &normalized, step)
        .map(|encoded| (encoded.value, encoded.constraints))
}

struct ChooseEncodedValue {
    value: SmtValue,
    constraints: Vec<Bool>,
    witnesses: Vec<(String, SmtValue, IRType)>,
}

fn encode_prop_value_with_choose_witnesses(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<ChooseEncodedValue, String> {
    let IRExpr::Let { bindings, body, .. } = expr else {
        return encode_prop_value(pool, vctx, defs, ctx, expr, step).map(|value| {
            ChooseEncodedValue {
                value,
                constraints: vec![],
                witnesses: vec![],
            }
        });
    };

    encode_prop_value_choose_bindings(pool, vctx, defs, ctx, bindings, body, step)
}

fn encode_prop_value_choose_bindings(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    step: usize,
) -> Result<ChooseEncodedValue, String> {
    let Some((binding, rest)) = bindings.split_first() else {
        return encode_prop_value(pool, vctx, defs, ctx, body, step).map(|value| {
            ChooseEncodedValue {
                value,
                constraints: vec![],
                witnesses: vec![],
            }
        });
    };

    match &binding.expr {
        IRExpr::Choose {
            var,
            domain: IRType::Entity { name: entity_name },
            predicate,
            ..
        } => {
            let mut branch_conds = Vec::new();
            let mut branch_values = Vec::new();
            let mut witnesses = Vec::new();
            for slot in 0..pool.slots_for(entity_name) {
                let Some(SmtValue::Bool(active)) = pool.active_at(entity_name, slot, step) else {
                    continue;
                };
                let choose_ctx = ctx.with_binding(var, entity_name, slot);
                let predicate_bool = if let Some(predicate) = predicate {
                    encode_prop_expr(pool, vctx, defs, &choose_ctx, predicate, step)?
                } else {
                    smt::bool_const(true)
                };
                let body_ctx = ctx.with_binding(&binding.name, entity_name, slot);
                let encoded = encode_prop_value_choose_bindings(
                    pool, vctx, defs, &body_ctx, rest, body, step,
                )?;
                witnesses.extend(encoded.witnesses);
                let mut cond_parts = vec![active.clone(), predicate_bool];
                cond_parts.extend(encoded.constraints);
                let refs: Vec<&Bool> = cond_parts.iter().collect();
                branch_conds.push(smt::bool_and(&refs));
                branch_values.push(encoded.value);
            }

            if branch_conds.is_empty() {
                return Ok(ChooseEncodedValue {
                    value: default_smt_value_for_expr(body)?,
                    constraints: vec![smt::bool_const(false)],
                    witnesses,
                });
            }

            let refs: Vec<&Bool> = branch_conds.iter().collect();
            let existence = smt::bool_or(&refs);
            let mut value = default_smt_value_for_expr(body)?;
            for (cond, branch_value) in branch_conds.iter().zip(branch_values.iter()).rev() {
                value = ite_value(cond, branch_value, &value);
            }
            Ok(ChooseEncodedValue {
                value,
                constraints: vec![existence],
                witnesses,
            })
        }
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => {
            let fresh = format!(
                "__abide_projection_choose_{}_{}",
                binding.name,
                PROP_CHOOSE_COUNTER.fetch_add(1, Ordering::Relaxed)
            );
            let witness = make_z3_bound_var_ctx(&fresh, domain, Some(vctx))?;
            let pred_ctx = ctx.with_local(var, witness.clone());
            let mut constraints = Vec::new();
            if let Some(domain_pred) =
                prop_domain_predicate(domain, &witness, &pred_ctx, vctx, defs)?
            {
                constraints.push(domain_pred);
            }
            if let Some(predicate) = predicate {
                constraints.push(encode_prop_expr(
                    pool, vctx, defs, &pred_ctx, predicate, step,
                )?);
            }
            let body_ctx = ctx.with_local(&binding.name, witness.clone());
            let mut encoded =
                encode_prop_value_choose_bindings(pool, vctx, defs, &body_ctx, rest, body, step)?;
            constraints.append(&mut encoded.constraints);
            encoded.constraints = constraints;
            encoded.witnesses.push((fresh, witness, domain.clone()));
            Ok(encoded)
        }
        _ => {
            if let IRExpr::Var { name, .. } = &binding.expr {
                if let Some((entity, slot)) = ctx.bindings.get(name) {
                    let body_ctx = ctx.with_binding(&binding.name, entity, *slot);
                    return encode_prop_value_choose_bindings(
                        pool, vctx, defs, &body_ctx, rest, body, step,
                    );
                }
            }
            let val = encode_prop_value(pool, vctx, defs, ctx, &binding.expr, step)?;
            let body_ctx = ctx.with_local(&binding.name, val);
            encode_prop_value_choose_bindings(pool, vctx, defs, &body_ctx, rest, body, step)
        }
    }
}

fn default_smt_value_for_expr(expr: &IRExpr) -> Result<SmtValue, String> {
    let Some(ty) = expr_type(expr) else {
        return Err(format!(
            "cannot infer default SMT value for expression: {expr:?}"
        ));
    };
    default_smt_value_for_type(ty)
}

fn default_smt_value_for_type(ty: &IRType) -> Result<SmtValue, String> {
    match ty {
        IRType::Bool => Ok(smt::bool_val(false)),
        IRType::Real | IRType::Float => Ok(smt::real_val(0, 1)),
        IRType::Int | IRType::Identity | IRType::String | IRType::Enum { .. } => {
            Ok(smt::int_val(0))
        }
        IRType::Refinement { base, .. } => default_smt_value_for_type(base),
        other => Err(format!(
            "unsupported choose projection value type: {other:?}"
        )),
    }
}

fn projection_has_local_choose(expr: &IRExpr) -> bool {
    matches!(
        expr,
        IRExpr::Let { bindings, .. }
            if bindings.iter().any(|binding| matches!(binding.expr, IRExpr::Choose { .. }))
    )
}

fn match_arm_has_local_choose(expr: &IRExpr) -> bool {
    matches!(
        expr,
        IRExpr::Let { bindings, .. }
            if bindings.iter().any(|binding| matches!(binding.expr, IRExpr::Choose { .. }))
    )
}

fn encode_projection_membership_with_choose(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    projection: &IRExpr,
    key: &SmtValue,
    step: usize,
) -> Result<Bool, String> {
    let IRExpr::Let { bindings, body, .. } = projection else {
        let value = encode_prop_value(pool, vctx, defs, ctx, projection, step)?;
        return smt::smt_eq(&value, key);
    };

    encode_projection_membership_bindings(
        PropertyEncodingCtx {
            pool,
            vctx,
            defs,
            property: ctx,
            step,
        },
        ProjectionMembership {
            bindings,
            body,
            key,
        },
    )
}

fn encode_projection_membership_bindings(
    enc: PropertyEncodingCtx<'_>,
    membership: ProjectionMembership<'_>,
) -> Result<Bool, String> {
    let pool = enc.pool;
    let vctx = enc.vctx;
    let defs = enc.defs;
    let ctx = enc.property;
    let step = enc.step;
    let ProjectionMembership {
        bindings,
        body,
        key,
    } = membership;
    let Some((binding, rest)) = bindings.split_first() else {
        let value = encode_prop_value(pool, vctx, defs, ctx, body, step)?;
        return smt::smt_eq(&value, key);
    };

    match &binding.expr {
        IRExpr::Choose {
            var,
            domain: IRType::Entity { name: entity_name },
            predicate,
            ..
        } => {
            let mut disjuncts = Vec::new();
            for slot in 0..pool.slots_for(entity_name) {
                let Some(SmtValue::Bool(active)) = pool.active_at(entity_name, slot, step) else {
                    continue;
                };
                let choose_ctx = ctx.with_binding(var, entity_name, slot);
                let predicate_bool = if let Some(predicate) = predicate {
                    encode_prop_expr(pool, vctx, defs, &choose_ctx, predicate, step)?
                } else {
                    smt::bool_const(true)
                };
                let body_ctx = ctx.with_binding(&binding.name, entity_name, slot);
                let rest_bool = encode_projection_membership_bindings(
                    enc.with_property(&body_ctx),
                    ProjectionMembership {
                        bindings: rest,
                        body,
                        key,
                    },
                )?;
                disjuncts.push(smt::bool_and(&[active, &predicate_bool, &rest_bool]));
            }
            if disjuncts.is_empty() {
                return Ok(smt::bool_const(false));
            }
            let refs: Vec<&Bool> = disjuncts.iter().collect();
            Ok(smt::bool_or(&refs))
        }
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ..
        } => {
            let fresh = format!(
                "__abide_projection_member_choose_{}_{}",
                binding.name,
                PROP_CHOOSE_COUNTER.fetch_add(1, Ordering::Relaxed)
            );
            let witness = make_z3_bound_var_ctx(&fresh, domain, Some(vctx))?;
            let pred_ctx = ctx.with_local(var, witness.clone());
            let mut constraints = Vec::new();
            if let Some(domain_pred) =
                prop_domain_predicate(domain, &witness, &pred_ctx, vctx, defs)?
            {
                constraints.push(domain_pred);
            }
            if let Some(predicate) = predicate {
                constraints.push(encode_prop_expr(
                    pool, vctx, defs, &pred_ctx, predicate, step,
                )?);
            }
            let body_ctx = ctx.with_local(&binding.name, witness.clone());
            constraints.push(encode_projection_membership_bindings(
                enc.with_property(&body_ctx),
                ProjectionMembership {
                    bindings: rest,
                    body,
                    key,
                },
            )?);
            let refs: Vec<&Bool> = constraints.iter().collect();
            let member = smt::bool_and(&refs);
            build_z3_quantifier(false, &witness, &member, &fresh, domain)
        }
        _ => {
            if let IRExpr::Var { name, .. } = &binding.expr {
                if let Some((entity, slot)) = ctx.bindings.get(name) {
                    let body_ctx = ctx.with_binding(&binding.name, entity, *slot);
                    return encode_projection_membership_bindings(
                        enc.with_property(&body_ctx),
                        ProjectionMembership {
                            bindings: rest,
                            body,
                            key,
                        },
                    );
                }
            }
            let val = encode_prop_value(pool, vctx, defs, ctx, &binding.expr, step)?;
            let body_ctx = ctx.with_local(&binding.name, val);
            encode_projection_membership_bindings(
                enc.with_property(&body_ctx),
                ProjectionMembership {
                    bindings: rest,
                    body,
                    key,
                },
            )
        }
    }
}

fn encode_setcomp_projection_membership(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    map: &IRExpr,
    key: &IRExpr,
    step: usize,
) -> Result<Option<Bool>, String> {
    let IRExpr::SetComp {
        var,
        source: Some(source),
        filter,
        projection: Some(projection),
        ..
    } = map
    else {
        return Ok(None);
    };
    if !projection_has_local_choose(projection) {
        return Ok(None);
    }
    let elements = match source.as_ref() {
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => elements,
        _ => return Ok(None),
    };
    let key_value = encode_prop_value(pool, vctx, defs, ctx, key, step)?;
    let mut disjuncts = Vec::new();
    for element_expr in elements {
        let value = encode_prop_value(pool, vctx, defs, ctx, element_expr, step)?;
        let inner_ctx = ctx.with_local(var, value);
        let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
        let member = encode_projection_membership_with_choose(
            pool, vctx, defs, &inner_ctx, projection, &key_value, step,
        )?;
        disjuncts.push(smt::bool_and(&[&filter_val, &member]));
    }
    if disjuncts.is_empty() {
        return Ok(Some(smt::bool_const(false)));
    }
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Ok(Some(smt::bool_or(&refs)))
}

fn encode_match_relation_with_local_choose(
    enc: PropertyEncodingCtx<'_>,
    relation: MatchRelation<'_>,
) -> Result<Option<Bool>, String> {
    let pool = enc.pool;
    let vctx = enc.vctx;
    let defs = enc.defs;
    let ctx = enc.property;
    let step = enc.step;
    let MatchRelation {
        match_expr,
        other,
        op,
        match_on_left,
    } = relation;
    let IRExpr::Match {
        scrutinee, arms, ..
    } = match_expr
    else {
        return Ok(None);
    };
    if !arms.iter().any(|arm| match_arm_has_local_choose(&arm.body)) {
        return Ok(None);
    }

    let scrut = encode_prop_value(pool, vctx, defs, ctx, scrutinee, step)?;
    let other_value = encode_prop_value(pool, vctx, defs, ctx, other, step)?;
    let mut disjuncts = Vec::new();

    for arm in arms {
        let arm_cond = encode_pattern_cond(&scrut, &arm.pattern, &ctx.locals, vctx)?;
        let mut arm_locals = ctx.locals.clone();
        bind_pattern_vars(&arm.pattern, &scrut, &mut arm_locals, vctx)?;
        let arm_ctx = property_ctx_with_locals(ctx, arm_locals);
        let full_cond = if let Some(guard) = &arm.guard {
            let guard_bool = encode_prop_expr(pool, vctx, defs, &arm_ctx, guard, step)?;
            smt::bool_and(&[&arm_cond, &guard_bool])
        } else {
            arm_cond
        };

        let encoded =
            encode_prop_value_with_choose_witnesses(pool, vctx, defs, &arm_ctx, &arm.body, step)?;
        let relation = if match_on_left {
            smt::binop(op, &encoded.value, &other_value)?.to_bool()?
        } else {
            smt::binop(op, &other_value, &encoded.value)?.to_bool()?
        };
        let mut conjuncts = vec![full_cond, relation];
        conjuncts.extend(encoded.constraints);
        let refs: Vec<&Bool> = conjuncts.iter().collect();
        let mut branch = smt::bool_and(&refs);
        for (fresh, witness, domain) in encoded.witnesses.into_iter().rev() {
            branch = build_z3_quantifier(false, &witness, &branch, &fresh, &domain)?;
        }
        disjuncts.push(branch);
    }

    if disjuncts.is_empty() {
        return Ok(Some(smt::bool_const(false)));
    }
    let refs: Vec<&Bool> = disjuncts.iter().collect();
    Ok(Some(smt::bool_or(&refs)))
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
pub(super) fn encode_prop_value(
    pool: &SlotPool,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    ctx: &PropertyCtx,
    expr: &IRExpr,
    step: usize,
) -> Result<SmtValue, String> {
    encode_prop_value_expr(
        PropertyEncodingCtx {
            pool,
            vctx,
            defs,
            property: ctx,
            step,
        },
        expr,
    )
}

fn encode_prop_value_expr(enc: PropertyEncodingCtx<'_>, expr: &IRExpr) -> Result<SmtValue, String> {
    if let Some(expanded) = expand_prop_value_expr(enc, expr) {
        return encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            &expanded,
            enc.step,
        );
    }
    match expr {
        IRExpr::Choose { .. } => {
            Err("choose is only supported through let-binding in verifier properties".to_owned())
        }
        IRExpr::Let { bindings, body, .. } => encode_prop_let_value(enc, bindings, body),
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => encode_prop_if_value(enc, cond, then_body, else_body.as_deref()),
        IRExpr::Match {
            scrutinee, arms, ..
        } => encode_prop_match_value(enc, scrutinee, arms),
        IRExpr::Lit { value, .. } => encode_prop_lit_value(value),
        IRExpr::Field {
            expr: recv, field, ..
        } => encode_prop_field_value(enc, recv, field),
        IRExpr::Var { name, .. } => encode_prop_var_value(enc, name),
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        } => encode_prop_ctor_value(enc, enum_name, ctor, args),
        IRExpr::BinOp {
            op, left, right, ..
        } => encode_prop_binop_value(enc, op, left, right),
        IRExpr::UnOp { op, operand, .. } => encode_prop_unop_value(enc, op, operand),
        IRExpr::Prime { expr, .. } => encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            expr,
            enc.step + 1,
        ),
        IRExpr::Forall { .. }
        | IRExpr::Exists { .. }
        | IRExpr::One { .. }
        | IRExpr::Lone { .. } => Ok(SmtValue::Bool(encode_prop_expr(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            expr,
            enc.step,
        )?)),
        IRExpr::Always { body, .. } => Ok(SmtValue::Bool(encode_prop_expr(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            body,
            enc.step,
        )?)),
        IRExpr::Eventually { .. } | IRExpr::Until { .. } => Err(
            "future-time temporal value reached single-step property encoder; route through lasso/Buchi temporal verification".to_owned(),
        ),
        IRExpr::MapUpdate {
            map, key, value, ..
        } => encode_prop_map_update_value(enc, map, key, value),
        IRExpr::Index { map, key, ty, .. } => encode_prop_index_value(enc, map, key, ty),
        IRExpr::MapLit { entries, ty, .. } => encode_prop_map_lit_value(enc, entries, ty),
        IRExpr::SetLit { elements, ty, .. } => encode_prop_set_lit_value(enc, elements, ty),
        IRExpr::SeqLit { elements, ty, .. } => encode_prop_seq_lit_value(enc, elements, ty),
        IRExpr::Tuple { elements, ty, .. } => encode_prop_tuple_value(enc, elements, ty),
        IRExpr::SetComp { .. } => encode_prop_set_comp_value(enc, expr),
        IRExpr::Aggregate { .. } => encode_prop_aggregate_value(enc, expr),
        IRExpr::Card { expr: inner, .. } => {
            encode_card(enc.pool, enc.vctx, enc.defs, enc.property, inner, enc.step)
        }
        IRExpr::App { func, .. } => encode_unexpanded_app_error(func, expr),
        _ => Err(format!("unsupported expression reached encoding: {expr:?}")),
    }
}

fn expand_prop_value_expr(enc: PropertyEncodingCtx<'_>, expr: &IRExpr) -> Option<IRExpr> {
    match expr {
        IRExpr::Var { name, .. } if !enc.property.bindings.contains_key(name) => {
            enc.defs.expand_var(name)
        }
        IRExpr::App { .. } => {
            record_prop_app_preconditions(enc, expr);
            enc.defs.expand_app(expr)
        }
        _ => None,
    }
}

fn record_prop_app_preconditions(enc: PropertyEncodingCtx<'_>, expr: &IRExpr) {
    let Some(preconditions) = enc.defs.call_preconditions(expr) else {
        return;
    };
    let fn_name = defenv::decompose_app_chain_name(expr).unwrap_or_else(|| "(unknown)".to_owned());
    let path_guard = current_path_guard();
    for pre in &preconditions {
        if let Ok(pre_bool) =
            encode_prop_expr(enc.pool, enc.vctx, enc.defs, enc.property, pre, enc.step)
        {
            record_prop_precondition_obligation(
                smt::bool_implies(&path_guard, &pre_bool),
                fn_name.clone(),
            );
        }
    }
}

fn encode_prop_let_value(
    enc: PropertyEncodingCtx<'_>,
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
) -> Result<SmtValue, String> {
    let mut locals = enc.property.locals.clone();
    for binding in bindings {
        let binding_ctx = property_ctx_with_locals(enc.property, locals.clone());
        let val = encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            &binding_ctx,
            &binding.expr,
            enc.step,
        )?;
        locals.insert(binding.name.clone(), val);
    }
    let body_ctx = property_ctx_with_locals(enc.property, locals);
    encode_prop_value(enc.pool, enc.vctx, enc.defs, &body_ctx, body, enc.step)
}

fn encode_prop_if_value(
    enc: PropertyEncodingCtx<'_>,
    cond: &IRExpr,
    then_body: &IRExpr,
    else_body: Option<&IRExpr>,
) -> Result<SmtValue, String> {
    let cond_bool = encode_prop_expr(enc.pool, enc.vctx, enc.defs, enc.property, cond, enc.step)?;
    let then_val = encode_prop_value(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        then_body,
        enc.step,
    )?;
    if let Some(else_body) = else_body {
        let else_val = encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            else_body,
            enc.step,
        )?;
        encode_ite(&cond_bool, &then_val, &else_val)
    } else {
        let then_bool = then_val.to_bool()?;
        Ok(SmtValue::Bool(smt::bool_implies(&cond_bool, &then_bool)))
    }
}

fn encode_prop_match_value(
    enc: PropertyEncodingCtx<'_>,
    scrutinee: &IRExpr,
    arms: &[crate::ir::types::IRMatchArm],
) -> Result<SmtValue, String> {
    let scrut = encode_prop_value(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        scrutinee,
        enc.step,
    )?;
    encode_prop_match(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        &scrut,
        arms,
        enc.step,
    )
}

fn encode_prop_lit_value(value: &crate::ir::types::LitVal) -> Result<SmtValue, String> {
    match value {
        crate::ir::types::LitVal::Int { value } => Ok(smt::int_val(*value)),
        crate::ir::types::LitVal::Bool { value } => Ok(smt::bool_val(*value)),
        crate::ir::types::LitVal::Real { value } | crate::ir::types::LitVal::Float { value } => {
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            Ok(smt::real_val(scaled, 1_000_000))
        }
        crate::ir::types::LitVal::Str { .. } => Ok(smt::int_val(0)),
    }
}

fn encode_prop_field_value(
    enc: PropertyEncodingCtx<'_>,
    recv: &IRExpr,
    field: &str,
) -> Result<SmtValue, String> {
    if let IRExpr::Var { name, .. } = recv {
        if let Some((entity, slot)) = enc.property.bindings.get(name) {
            if let Some(val) = enc.pool.field_at(entity, *slot, field, enc.step) {
                return Ok(val.clone());
            }
            return Err(format!(
                "field not found: {entity}.{field} (var={name}, slot={slot}, step={step})",
                step = enc.step,
            ));
        }
        if let Some(sys_name) = enc.property.system_struct_bases.get(name.as_str()) {
            if sys_name.is_empty() {
                return Err(format!(
                    "ambiguous system struct field `{name}`: exists in multiple in-scope systems"
                ));
            }
            let compound = format!("{name}.{field}");
            if let Some(val) = enc.pool.system_field_at(sys_name, &compound, enc.step) {
                return Ok(val.clone());
            }
        }
    }
    for (entity, slot) in enc.property.bindings.values() {
        if let Some(val) = enc.pool.field_at(entity, *slot, field, enc.step) {
            return Ok(val.clone());
        }
    }
    Err(format!(
        "field not found in any bound entity: {field} (step={step})",
        step = enc.step,
    ))
}

fn encode_prop_var_value(enc: PropertyEncodingCtx<'_>, name: &str) -> Result<SmtValue, String> {
    if let Some(val) = enc.property.locals.get(name) {
        return Ok(val.clone());
    }
    let matches = prop_entity_field_matches(enc, name);
    if !matches.is_empty() {
        return match matches.len() {
            1 => Ok(matches.into_iter().next().unwrap().2),
            _ => Err(format!(
                "ambiguous variable {name}: matches fields in entities {:?} (step={step})",
                matches
                    .iter()
                    .map(|(var, entity, _)| format!("{var}:{entity}"))
                    .collect::<Vec<_>>(),
                step = enc.step,
            )),
        };
    }
    if let Some(sys_name) = enc.property.system_fields.get(name) {
        if sys_name.is_empty() {
            return Err(format!(
                "ambiguous system field `{name}`: exists in multiple in-scope systems"
            ));
        }
        if let Some(val) = enc.pool.system_field_at(sys_name, name, enc.step) {
            return Ok(val.clone());
        }
    }
    Err(format!(
        "variable not found: {name} (bindings: {:?}, step={step})",
        enc.property.bindings.keys().collect::<Vec<_>>(),
        step = enc.step,
    ))
}

fn prop_entity_field_matches(
    enc: PropertyEncodingCtx<'_>,
    name: &str,
) -> Vec<(String, String, SmtValue)> {
    let mut matches = Vec::new();
    for (var, (entity, slot)) in &enc.property.bindings {
        if let Some(val) = enc.pool.field_at(entity, *slot, name, enc.step) {
            matches.push((var.clone(), entity.clone(), val.clone()));
        }
    }
    matches
}

fn encode_prop_ctor_value(
    enc: PropertyEncodingCtx<'_>,
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
) -> Result<SmtValue, String> {
    if let Some(value) = encode_prop_adt_ctor_value(enc, enum_name, ctor, args)? {
        return Ok(value);
    }
    let id = enc.vctx.variants.try_id_of(enum_name, ctor)?;
    Ok(smt::int_val(id))
}

fn encode_prop_adt_ctor_value(
    enc: PropertyEncodingCtx<'_>,
    enum_name: &str,
    ctor: &str,
    args: &[(String, IRExpr)],
) -> Result<Option<SmtValue>, String> {
    let Some(dt) = enc.vctx.adt_sorts.get(enum_name) else {
        return Ok(None);
    };
    for variant in &dt.variants {
        if smt::func_decl_name(&variant.constructor) != ctor {
            continue;
        }
        if args.is_empty() {
            let result = smt::func_decl_apply(&variant.constructor, &[]);
            return Ok(Some(dynamic_to_smt_value(result)));
        }
        let args_map: HashMap<&str, &IRExpr> = args
            .iter()
            .map(|(name, expr)| (name.as_str(), expr))
            .collect();
        let mut z3_args: Vec<Dynamic> = Vec::new();
        for decl_name in variant.accessors.iter().map(smt::func_decl_name) {
            if let Some(field_expr) = args_map.get(decl_name.as_str()) {
                let val = encode_prop_value(
                    enc.pool,
                    enc.vctx,
                    enc.defs,
                    enc.property,
                    field_expr,
                    enc.step,
                )?;
                z3_args.push(val.to_dynamic());
            }
        }
        let arg_refs: Vec<&Dynamic> = z3_args.iter().collect();
        let result = smt::func_decl_apply(&variant.constructor, &arg_refs);
        return Ok(Some(dynamic_to_smt_value(result)));
    }
    Ok(None)
}

fn encode_prop_binop_value(
    enc: PropertyEncodingCtx<'_>,
    op: &str,
    left: &IRExpr,
    right: &IRExpr,
) -> Result<SmtValue, String> {
    match op {
        "OpSeqConcat" => encode_prop_seq_concat_value(enc, left, right),
        "OpMapHas" => encode_prop_map_has_value(enc, left, right),
        "OpMapMerge" => encode_prop_map_merge_value(enc, left, right),
        _ => {
            let l = encode_prop_value_for_comparison(&enc, left, right)?;
            let r = encode_prop_value_for_comparison(&enc, right, left)?;
            Ok(smt::binop(op, &l, &r)?)
        }
    }
}

fn encode_prop_value_for_comparison(
    enc: &PropertyEncodingCtx<'_>,
    expr: &IRExpr,
    other: &IRExpr,
) -> Result<SmtValue, String> {
    if let (
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            ..
        },
        Some(IRType::Enum { name, variants }),
    ) = (expr, slot_field_expr_type(enc.property, other))
    {
        if args.is_empty()
            && enum_name == name
            && variants
                .iter()
                .any(|variant| variant.name == *ctor && variant.fields.is_empty())
        {
            return enc.vctx.variants.try_id_of(name, ctor).map(smt::int_val);
        }
    }

    encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, expr, enc.step)
}

fn slot_field_expr_type<'a>(ctx: &PropertyCtx, expr: &'a IRExpr) -> Option<&'a IRType> {
    let IRExpr::Field { expr: base, ty, .. } = expr else {
        return None;
    };
    let IRExpr::Var { name, .. } = base.as_ref() else {
        return None;
    };
    ctx.bindings.contains_key(name).then_some(ty)
}

fn encode_prop_seq_concat_value(
    enc: PropertyEncodingCtx<'_>,
    left: &IRExpr,
    right: &IRExpr,
) -> Result<SmtValue, String> {
    let l = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, left, enc.step)?;
    let r = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, right, enc.step)?;
    let Some(IRType::Seq { element }) = expr_type(left) else {
        return Err("Seq::concat requires sequence operands".to_string());
    };
    smt::seq_concat(&l, &r, element)
}

fn encode_prop_map_has_value(
    enc: PropertyEncodingCtx<'_>,
    left: &IRExpr,
    right: &IRExpr,
) -> Result<SmtValue, String> {
    let map_val = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, left, enc.step)?;
    let key_val = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, right, enc.step)?;
    let Some(IRType::Map { value, .. }) = expr_type(left) else {
        return Err("Map::has requires a map-typed left operand".to_owned());
    };
    smt::map_has(&map_val, &key_val, value)
}

fn encode_prop_map_merge_value(
    enc: PropertyEncodingCtx<'_>,
    left: &IRExpr,
    right: &IRExpr,
) -> Result<SmtValue, String> {
    let left_val = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, left, enc.step)?;
    let right_val = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, right, enc.step)?;
    let Some(IRType::Map { key, value }) = expr_type(left) else {
        return Err("Map::merge requires map operands".to_owned());
    };
    smt::map_merge(&left_val, &right_val, key, value)
}

fn encode_prop_unop_value(
    enc: PropertyEncodingCtx<'_>,
    op: &str,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    match op {
        "OpSeqHead" => encode_prop_seq_head_value(enc, op, operand),
        "OpSeqTail" => encode_prop_seq_tail_value(enc, op, operand),
        "OpSeqLength" => encode_prop_seq_length_value(enc, operand),
        "OpSeqEmpty" => encode_prop_seq_empty_value(enc, operand),
        "OpMapDomain" => encode_prop_map_domain_value(enc, operand),
        "OpMapRange" => encode_prop_map_range_value(enc, operand),
        _ => {
            let value = encode_prop_value(
                enc.pool,
                enc.vctx,
                enc.defs,
                enc.property,
                operand,
                enc.step,
            )?;
            Ok(smt::unop(op, &value)?)
        }
    }
}

fn encode_prop_seq_head_value(
    enc: PropertyEncodingCtx<'_>,
    op: &str,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    let value = encode_prop_value(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        operand,
        enc.step,
    )?;
    let Some(IRType::Seq { element }) = expr_type(operand) else {
        return smt::unop(op, &value);
    };
    smt::seq_head(&value, element)
}

fn encode_prop_seq_tail_value(
    enc: PropertyEncodingCtx<'_>,
    op: &str,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    if let IRExpr::SeqLit { elements, ty, .. } = operand {
        let tail = IRExpr::SeqLit {
            elements: elements.iter().skip(1).cloned().collect(),
            ty: ty.clone(),
            span: None,
        };
        return encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, &tail, enc.step);
    }
    let value = encode_prop_value(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        operand,
        enc.step,
    )?;
    let Some(IRType::Seq { element }) = expr_type(operand) else {
        return smt::unop(op, &value);
    };
    smt::seq_tail(&value, element)
}

fn encode_prop_seq_length_value(
    enc: PropertyEncodingCtx<'_>,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    if let Some(IRType::Seq { element }) = expr_type(operand) {
        let value = encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            operand,
            enc.step,
        )?;
        smt::seq_length(&value, element)
    } else {
        encode_card(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            operand,
            enc.step,
        )
    }
}

fn encode_prop_seq_empty_value(
    enc: PropertyEncodingCtx<'_>,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    let len = encode_prop_seq_length_value(enc, operand)?;
    Ok(SmtValue::Bool(smt::smt_eq(&len, &smt::int_val(0))?))
}

fn encode_prop_map_domain_value(
    enc: PropertyEncodingCtx<'_>,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    if let IRExpr::MapLit { entries, .. } = operand {
        let set_lit = IRExpr::SetLit {
            elements: entries.iter().map(|(key, _)| key.clone()).collect(),
            ty: IRType::Set {
                element: Box::new(match expr_type(operand) {
                    Some(IRType::Map { key, .. }) => key.as_ref().clone(),
                    _ => IRType::Int,
                }),
            },
            span: None,
        };
        return encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            &set_lit,
            enc.step,
        );
    }
    let map_val = encode_prop_value(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        operand,
        enc.step,
    )?;
    let Some(IRType::Map { key, value }) = expr_type(operand) else {
        return Err("Map::domain requires a map operand".to_owned());
    };
    smt::map_domain(&map_val, key, value)
}

fn encode_prop_map_range_value(
    enc: PropertyEncodingCtx<'_>,
    operand: &IRExpr,
) -> Result<SmtValue, String> {
    if let IRExpr::MapLit { entries, .. } = operand {
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
        return encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            &set_lit,
            enc.step,
        );
    }
    let map_val = encode_prop_value(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        operand,
        enc.step,
    )?;
    let Some(IRType::Map { key, value }) = expr_type(operand) else {
        return Err("Map::range requires a map operand".to_owned());
    };
    smt::map_range(&map_val, key, value)
}

fn encode_prop_map_update_value(
    enc: PropertyEncodingCtx<'_>,
    map: &IRExpr,
    key: &IRExpr,
    value: &IRExpr,
) -> Result<SmtValue, String> {
    let arr = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, map, enc.step)?;
    let k = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, key, enc.step)?;
    let v = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, value, enc.step)?;
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

fn encode_prop_index_value(
    enc: PropertyEncodingCtx<'_>,
    map: &IRExpr,
    key: &IRExpr,
    ty: &IRType,
) -> Result<SmtValue, String> {
    if let Some(membership) = encode_prop_store_membership_index(enc, map, key)? {
        return Ok(SmtValue::Bool(membership));
    }
    let arr = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, map, enc.step)?;
    let k = encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, key, enc.step)?;
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

fn encode_prop_store_membership_index(
    enc: PropertyEncodingCtx<'_>,
    map: &IRExpr,
    key: &IRExpr,
) -> Result<Option<Bool>, String> {
    let IRExpr::Var {
        name: store_name, ..
    } = map
    else {
        return Ok(None);
    };
    let Some(range) = enc.property.store_ranges.get(store_name) else {
        return Ok(None);
    };
    let IRExpr::Var { name: key_var, .. } = key else {
        return Ok(None);
    };
    let Some((entity_name, slot)) = enc.property.bindings.get(key_var) else {
        return Ok(None);
    };
    if entity_name != &range.entity_type {
        return Err(format!(
            "store `{store_name}` contains `{}`, but membership key `{key_var}` is `{entity_name}`",
            range.entity_type
        ));
    }
    let in_range =
        *slot >= range.start_slot && *slot < range.start_slot.saturating_add(range.slot_count);
    if !in_range {
        return Ok(Some(smt::bool_const(false)));
    }
    match enc.pool.active_at(entity_name, *slot, enc.step) {
        Some(SmtValue::Bool(active)) => Ok(Some(active.clone())),
        Some(other) => Err(format!(
            "store membership expected bool active flag for `{entity_name}` slot {slot}, got {other:?}"
        )),
        None => Ok(Some(smt::bool_const(false))),
    }
}

fn encode_prop_map_lit_value(
    enc: PropertyEncodingCtx<'_>,
    entries: &[(IRExpr, IRExpr)],
    ty: &IRType,
) -> Result<SmtValue, String> {
    let (key_ty, val_ty) = match ty {
        IRType::Map { key, value } => (key.as_ref(), value.as_ref()),
        _ => return Err(format!("MapLit with non-Map type: {ty:?}")),
    };
    let key_sort = smt::ir_type_to_sort(key_ty);
    let default_val = smt::map_none_dynamic(val_ty);
    let mut arr = smt::const_array(&key_sort, &default_val);
    for (key_expr, value_expr) in entries {
        let key = encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            key_expr,
            enc.step,
        )?;
        let value = encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            value_expr,
            enc.step,
        )?;
        arr = arr.store(&key.to_dynamic(), &smt::map_some_dynamic(val_ty, &value));
    }
    Ok(SmtValue::Array(arr))
}

fn encode_prop_set_lit_value(
    enc: PropertyEncodingCtx<'_>,
    elements: &[IRExpr],
    ty: &IRType,
) -> Result<SmtValue, String> {
    let elem_ty = match ty {
        IRType::Set { element } => element.as_ref(),
        _ => return Err(format!("SetLit with non-Set type: {ty:?}")),
    };
    let elem_sort = ir_type_to_prop_sort(enc.vctx, elem_ty);
    let false_val = smt::bool_val(false).to_dynamic();
    let true_val = smt::bool_val(true).to_dynamic();
    let mut arr = smt::const_array(&elem_sort, &false_val);
    for elem in elements {
        let encoded =
            encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, elem, enc.step)?;
        arr = arr.store(&encoded.to_dynamic(), &true_val);
    }
    Ok(SmtValue::Array(arr))
}

fn encode_prop_seq_lit_value(
    enc: PropertyEncodingCtx<'_>,
    elements: &[IRExpr],
    ty: &IRType,
) -> Result<SmtValue, String> {
    let elem_ty = match ty {
        IRType::Seq { element } => element.as_ref(),
        _ => return Err(format!("SeqLit with non-Seq type: {ty:?}")),
    };
    let elems = elements
        .iter()
        .map(|elem| encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, elem, enc.step))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(smt::seq_literal(elem_ty, &elems))
}

fn encode_prop_tuple_value(
    enc: PropertyEncodingCtx<'_>,
    elements: &[IRExpr],
    ty: &IRType,
) -> Result<SmtValue, String> {
    let IRType::Tuple {
        elements: element_tys,
    } = ty
    else {
        return Err(format!("Tuple expression with non-Tuple type: {ty:?}"));
    };
    let encoded = elements
        .iter()
        .map(|elem| encode_prop_value(enc.pool, enc.vctx, enc.defs, enc.property, elem, enc.step))
        .collect::<Result<Vec<_>, _>>()?;
    smt::tuple_value(element_tys, encoded)
}

fn encode_prop_set_comp_value(
    enc: PropertyEncodingCtx<'_>,
    expr: &IRExpr,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::SetComp {
            var,
            domain,
            source: Some(source),
            filter,
            projection,
            ty,
            ..
        } => encode_prop_sourced_set_comp_value(
            enc,
            var,
            domain,
            source,
            filter,
            projection.as_deref(),
            ty,
        ),
        IRExpr::SetComp {
            var,
            domain: IRType::Entity { name: entity_name },
            filter,
            projection,
            ty,
            ..
        } => encode_prop_entity_set_comp_value(
            enc,
            var,
            entity_name,
            filter,
            projection.as_deref(),
            ty,
        ),
        IRExpr::SetComp {
            var,
            domain,
            source: None,
            filter,
            projection,
            ty,
            ..
        } if finite_domain_values_with_payloads(enc.vctx, domain).is_some() => {
            encode_prop_finite_set_comp_value(enc, var, domain, filter, projection.as_deref(), ty)
        }
        IRExpr::SetComp { domain, .. } => Err(format!(
            "unsupported SetComp domain in verifier property encoding: {domain:?}"
        )),
        _ => unreachable!("set-comp dispatcher called with non-SetComp expression"),
    }
}

fn encode_prop_sourced_set_comp_value(
    enc: PropertyEncodingCtx<'_>,
    var: &str,
    domain: &IRType,
    source: &IRExpr,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    ty: &IRType,
) -> Result<SmtValue, String> {
    if let Some((entity_name, start_slot, slot_count)) =
        store_source_range(enc.property, domain, source)
    {
        return encode_prop_store_sourced_entity_set_comp_value(
            enc,
            var,
            &entity_name,
            start_slot,
            slot_count,
            filter,
            projection,
            ty,
        );
    }

    let elements = finite_sourced_set_comp_elements(source)?;
    let mut arr = empty_set_comp_array(enc.vctx, ty)?;
    let true_val = smt::bool_val(true).to_dynamic();
    for element_expr in &elements {
        let value = encode_prop_value(
            enc.pool,
            enc.vctx,
            enc.defs,
            enc.property,
            element_expr,
            enc.step,
        )?;
        let inner_ctx = enc.property.with_local(var, value.clone());
        let filter_val =
            encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, filter, enc.step)?;
        let (key, constraints) = encode_set_comp_key(
            enc.with_property(&inner_ctx),
            projection,
            value.to_dynamic(),
        )?;
        let cond = set_comp_condition(filter_val, constraints);
        let stored = arr.store(&key, &true_val);
        arr = smt::array_ite(&cond, &stored, &arr);
    }
    Ok(SmtValue::Array(arr))
}

fn finite_sourced_set_comp_elements(source: &IRExpr) -> Result<Vec<IRExpr>, String> {
    match source {
        IRExpr::SetLit { elements, .. } | IRExpr::SeqLit { elements, .. } => Ok(elements.clone()),
        IRExpr::UnOp { op, operand, .. } if op == "OpMapDomain" => match operand.as_ref() {
            IRExpr::MapLit { entries, .. } => {
                Ok(entries.iter().map(|(key, _)| key.clone()).collect())
            }
            _ => Err(
                "sourced SetComp over Map::domain currently requires a finite Map literal source"
                    .to_owned(),
            ),
        },
        _ => Err(
            "sourced SetComp in verifier properties currently requires a finite Set, Seq, or Map::domain literal source"
                .to_owned(),
        ),
    }
}

fn store_source_range(
    ctx: &PropertyCtx,
    domain: &IRType,
    source: &IRExpr,
) -> Option<(String, usize, usize)> {
    let IRType::Entity {
        name: domain_entity,
    } = domain
    else {
        return None;
    };
    let IRExpr::Var {
        name: store_name, ..
    } = source
    else {
        return None;
    };
    let store_range = ctx.store_ranges.get(store_name)?;
    if store_range.entity_type != *domain_entity {
        return None;
    }
    Some((
        store_range.entity_type.clone(),
        store_range.start_slot,
        store_range.slot_count,
    ))
}

fn encode_prop_store_sourced_entity_set_comp_value(
    enc: PropertyEncodingCtx<'_>,
    var: &str,
    entity_name: &str,
    start_slot: usize,
    slot_count: usize,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    ty: &IRType,
) -> Result<SmtValue, String> {
    let result_elem_sort = entity_set_comp_sort(enc.vctx, projection, ty)?;
    let false_val = smt::bool_val(false).to_dynamic();
    let true_val = smt::bool_val(true).to_dynamic();
    let mut arr = smt::const_array(&result_elem_sort, &false_val);
    for slot in start_slot..start_slot.saturating_add(slot_count) {
        let Some(SmtValue::Bool(active)) = enc.pool.active_at(entity_name, slot, enc.step) else {
            continue;
        };
        let inner_ctx = enc.property.with_binding(var, entity_name, slot);
        let filter_val =
            encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, filter, enc.step)?;
        let fallback = smt::int_val(i64::try_from(slot).unwrap_or(0)).to_dynamic();
        let (key, constraints) =
            encode_set_comp_key(enc.with_property(&inner_ctx), projection, fallback)?;
        let mut cond_parts = vec![active.clone(), filter_val];
        cond_parts.extend(constraints);
        let cond = bool_and_values(&cond_parts);
        let stored = arr.store(&key, &true_val);
        arr = smt::array_ite(&cond, &stored, &arr);
    }
    Ok(SmtValue::Array(arr))
}

fn encode_prop_entity_set_comp_value(
    enc: PropertyEncodingCtx<'_>,
    var: &str,
    entity_name: &str,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    ty: &IRType,
) -> Result<SmtValue, String> {
    let result_elem_sort = entity_set_comp_sort(enc.vctx, projection, ty)?;
    let false_val = smt::bool_val(false).to_dynamic();
    let true_val = smt::bool_val(true).to_dynamic();
    let mut arr = smt::const_array(&result_elem_sort, &false_val);
    for slot in 0..enc.pool.slots_for(entity_name) {
        let Some(SmtValue::Bool(active)) = enc.pool.active_at(entity_name, slot, enc.step) else {
            continue;
        };
        let inner_ctx = enc.property.with_binding(var, entity_name, slot);
        let filter_val =
            encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, filter, enc.step)?;
        let fallback = smt::int_val(i64::try_from(slot).unwrap_or(0)).to_dynamic();
        let (key, constraints) =
            encode_set_comp_key(enc.with_property(&inner_ctx), projection, fallback)?;
        let mut cond_parts = vec![active.clone(), filter_val];
        cond_parts.extend(constraints);
        let cond = bool_and_values(&cond_parts);
        let stored = arr.store(&key, &true_val);
        arr = smt::array_ite(&cond, &stored, &arr);
    }
    Ok(SmtValue::Array(arr))
}

fn encode_prop_finite_set_comp_value(
    enc: PropertyEncodingCtx<'_>,
    var: &str,
    domain: &IRType,
    filter: &IRExpr,
    projection: Option<&IRExpr>,
    ty: &IRType,
) -> Result<SmtValue, String> {
    let mut arr = empty_set_comp_array(enc.vctx, ty)?;
    let true_val = smt::bool_val(true).to_dynamic();
    let values = finite_domain_values_with_payloads(enc.vctx, domain).unwrap_or_default();
    for value in values {
        let inner_ctx = enc.property.with_local(var, value.clone());
        let filter_val =
            encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, filter, enc.step)?;
        let (key, constraints) = encode_set_comp_key(
            enc.with_property(&inner_ctx),
            projection,
            value.to_dynamic(),
        )?;
        let cond = set_comp_condition(filter_val, constraints);
        let stored = arr.store(&key, &true_val);
        arr = smt::array_ite(&cond, &stored, &arr);
    }
    Ok(SmtValue::Array(arr))
}

fn empty_set_comp_array(vctx: &VerifyContext, ty: &IRType) -> Result<smt::Array, String> {
    let IRType::Set { element } = ty else {
        return Err(format!("SetComp with non-Set result type: {ty:?}"));
    };
    let result_elem_sort = ir_type_to_prop_sort(vctx, element);
    let false_val = smt::bool_val(false).to_dynamic();
    Ok(smt::const_array(&result_elem_sort, &false_val))
}

fn entity_set_comp_sort(
    vctx: &VerifyContext,
    projection: Option<&IRExpr>,
    ty: &IRType,
) -> Result<smt::Sort, String> {
    match (projection, ty) {
        (Some(_), IRType::Set { element }) => Ok(ir_type_to_prop_sort(vctx, element)),
        (Some(_), _) => Err(format!(
            "projection SetComp with non-Set result type: {ty:?}"
        )),
        (None, _) => Ok(smt::sort_int()),
    }
}

fn encode_set_comp_key(
    enc: PropertyEncodingCtx<'_>,
    projection: Option<&IRExpr>,
    fallback: Dynamic,
) -> Result<(Dynamic, Vec<Bool>), String> {
    let Some(proj_expr) = projection else {
        return Ok((fallback, Vec::new()));
    };
    let (key, constraints) = encode_prop_value_with_choose_constraints(
        enc.pool,
        enc.vctx,
        enc.defs,
        enc.property,
        proj_expr,
        enc.step,
    )?;
    Ok((key.to_dynamic(), constraints))
}

fn set_comp_condition(filter_val: Bool, projection_constraints: Vec<Bool>) -> Bool {
    if projection_constraints.is_empty() {
        filter_val
    } else {
        let mut conjuncts = vec![filter_val];
        conjuncts.extend(projection_constraints);
        bool_and_values(&conjuncts)
    }
}

fn bool_and_values(values: &[Bool]) -> Bool {
    let refs: Vec<&Bool> = values.iter().collect();
    smt::bool_and(&refs)
}

fn encode_prop_aggregate_value(
    enc: PropertyEncodingCtx<'_>,
    expr: &IRExpr,
) -> Result<SmtValue, String> {
    match expr {
        IRExpr::Aggregate {
            kind,
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            in_filter,
            ..
        } => encode_aggregate_entity(
            enc,
            *kind,
            var,
            entity_name,
            body,
            in_filter.as_deref(),
            enc.pool.slots_for(entity_name),
        ),
        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            ..
        } if matches!(domain, IRType::Enum { .. }) && !domain.has_variant_fields() => {
            encode_aggregate_enum(
                enc,
                *kind,
                var,
                body,
                in_filter.as_deref(),
                enum_variant_count(domain),
            )
        }
        IRExpr::Aggregate {
            kind,
            var,
            domain: domain @ IRType::Enum { name, .. },
            body,
            in_filter,
            ..
        } if domain.has_variant_fields() => {
            let Some(values) = finite_payload_enum_values(enc.vctx, domain) else {
                return Err(format!(
                    "{kind:?} aggregator over ADT enum `{name}` is not supported — \
                     constructor fields must themselves have finite Bool/enum domains"
                ));
            };
            encode_aggregate_finite_values(enc, *kind, var, body, in_filter.as_deref(), &values)
        }
        IRExpr::Aggregate {
            kind,
            var,
            domain: IRType::Bool,
            body,
            in_filter,
            ..
        } => encode_aggregate_bool(enc, *kind, var, body, in_filter.as_deref()),
        IRExpr::Aggregate { kind, domain, .. } => Err(format!(
            "{kind:?} aggregator over `{domain:?}` domain is not supported — \
             aggregators require a bounded domain (entity pool, fieldless \
             enum, or Bool)"
        )),
        _ => unreachable!("aggregate dispatcher called with non-Aggregate expression"),
    }
}

fn encode_unexpanded_app_error(func: &IRExpr, expr: &IRExpr) -> Result<SmtValue, String> {
    if let IRExpr::Var { name, .. } = func {
        return Err(format!(
            "function `{name}` reached encoding without expansion \
             (should have been caught by pre-validation)"
        ));
    }
    Err(format!(
        "unsupported App expression reached encoding: {expr:?}"
    ))
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
pub(super) fn encode_aggregate_entity(
    enc: PropertyEncodingCtx<'_>,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    entity_name: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    n_slots: usize,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;

    // Collect per-slot (active_flag, body_value) pairs.
    // When `in_filter` is present, AND the membership predicate with
    // the active flag so only elements in the collection contribute.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for slot in 0..n_slots {
        let active = enc.pool.active_at(entity_name, slot, enc.step);
        let inner_ctx = enc.property.with_binding(var, entity_name, slot);
        if let Some(SmtValue::Bool(act)) = active {
            // Combine active flag with optional membership filter.
            let effective_active = if let Some(filter_expr) = in_filter {
                let membership = encode_prop_expr(
                    enc.pool,
                    enc.vctx,
                    enc.defs,
                    &inner_ctx,
                    filter_expr,
                    enc.step,
                )?;
                smt::bool_and(&[&act.clone(), &membership])
            } else {
                act.clone()
            };

            if kind == IRAggKind::Count {
                let pred =
                    encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
                slot_data.push((smt::bool_and(&[&effective_active, &pred]), smt::int_val(1)));
            } else {
                let val =
                    encode_prop_value(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
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
                step = enc.step,
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
pub(super) fn encode_aggregate_bool(
    enc: PropertyEncodingCtx<'_>,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;
    let bool_vals = [smt::bool_val(false), smt::bool_val(true)];

    // Collect (membership_flag, body_value) pairs, filtering via in_filter.
    // For count, body_value is always int_val(1) and the flag includes the predicate.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for bv in &bool_vals {
        let inner_ctx = enc.property.with_local(var, bv.clone());
        let mut flag = smt::bool_const(true);
        if let Some(filter_expr) = in_filter {
            let membership = encode_prop_expr(
                enc.pool,
                enc.vctx,
                enc.defs,
                &inner_ctx,
                filter_expr,
                enc.step,
            )?;
            flag = membership;
        }
        if kind == IRAggKind::Count {
            let pred = encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
            slot_data.push((smt::bool_and(&[&flag, &pred]), smt::int_val(1)));
        } else {
            let val = encode_prop_value(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
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
                if is_min { "min" } else { "max" },
                step = enc.step,
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

fn encode_aggregate_finite_values(
    enc: PropertyEncodingCtx<'_>,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    values: &[SmtValue],
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;

    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for value in values {
        let inner_ctx = enc.property.with_local(var, value.clone());
        let mut flag = smt::bool_const(true);
        if let Some(filter_expr) = in_filter {
            flag = encode_prop_expr(
                enc.pool,
                enc.vctx,
                enc.defs,
                &inner_ctx,
                filter_expr,
                enc.step,
            )?;
        }
        if kind == IRAggKind::Count {
            let pred = encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
            slot_data.push((smt::bool_and(&[&flag, &pred]), smt::int_val(1)));
        } else {
            let val = encode_prop_value(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
            slot_data.push((flag, val));
        }
    }

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
                return Err(format!("{kind:?} over empty finite domain"));
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
                "__agg_{}_finite_{var}_undef_t{step}",
                if is_min { "min" } else { "max" },
                step = enc.step,
            );
            let undef = if ir_expr_is_real(body) {
                smt::real_var(&undef_name)
            } else {
                smt::int_var(&undef_name)
            };
            Ok(ite_value(&any_active, &acc, &undef))
        }
    }
}

pub(super) fn encode_aggregate_enum(
    enc: PropertyEncodingCtx<'_>,
    kind: crate::ir::types::IRAggKind,
    var: &str,
    body: &IRExpr,
    in_filter: Option<&IRExpr>,
    n: usize,
) -> Result<SmtValue, String> {
    use crate::ir::types::IRAggKind;

    // Collect (filter_flag, body_value) pairs for each variant.
    let mut slot_data: Vec<(Bool, SmtValue)> = Vec::new();
    for idx in 0..n {
        let inner_ctx = enc.property.with_local(var, smt::int_val(idx as i64));
        let mut flag = smt::bool_const(true);
        if let Some(filter_expr) = in_filter {
            let membership = encode_prop_expr(
                enc.pool,
                enc.vctx,
                enc.defs,
                &inner_ctx,
                filter_expr,
                enc.step,
            )?;
            flag = membership;
        }
        if kind == IRAggKind::Count {
            let pred = encode_prop_expr(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
            slot_data.push((smt::bool_and(&[&flag, &pred]), smt::int_val(1)));
        } else {
            let val = encode_prop_value(enc.pool, enc.vctx, enc.defs, &inner_ctx, body, enc.step)?;
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
                step = enc.step,
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
    if let Some(keys) = finite_set_algebra_keys(inner) {
        return Ok(smt::int_val(i64::try_from(keys.len()).unwrap_or(0)));
    }

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
        IRExpr::SetComp {
            var,
            source: Some(source),
            filter,
            projection,
            ..
        } => {
            let elements = finite_sourced_set_comp_elements(source)?;
            let one = smt::int_lit(1);
            let zero = smt::int_lit(0);
            let mut terms = Vec::new();
            let mut prior_keys: Vec<(SmtValue, Bool)> = Vec::new();
            for element_expr in &elements {
                let value = encode_prop_value(pool, vctx, defs, ctx, element_expr, step)?;
                let inner_ctx = ctx.with_local(var, value.clone());
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                let (key, projection_constraints) = if let Some(projection) = projection {
                    encode_prop_value_with_choose_constraints(
                        pool, vctx, defs, &inner_ctx, projection, step,
                    )?
                } else {
                    (value, vec![])
                };
                let mut include_once = if projection_constraints.is_empty() {
                    filter_val.clone()
                } else {
                    let mut conjuncts = vec![filter_val.clone()];
                    conjuncts.extend(projection_constraints);
                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    smt::bool_and(&refs)
                };
                for (prior_key, prior_filter) in &prior_keys {
                    let same_key = smt::smt_eq(&key, prior_key)?;
                    let prior_included_same_key = smt::bool_and(&[prior_filter, &same_key]);
                    include_once =
                        smt::bool_and(&[&include_once, &smt::bool_not(&prior_included_same_key)]);
                }
                terms.push(smt::int_ite(&include_once, &one, &zero));
                prior_keys.push((key, include_once));
            }
            if terms.is_empty() {
                return Ok(smt::int_val(0));
            }
            let refs: Vec<&Int> = terms.iter().collect();
            Ok(SmtValue::Int(smt::int_add(&refs)))
        }
        IRExpr::SetComp {
            var,
            domain,
            source: None,
            filter,
            projection,
            ..
        } if finite_domain_values_with_payloads(vctx, domain).is_some() => {
            let one = smt::int_lit(1);
            let zero = smt::int_lit(0);
            let mut terms = Vec::new();
            let mut prior_keys: Vec<(SmtValue, Bool)> = Vec::new();
            for value in finite_domain_values_with_payloads(vctx, domain).unwrap_or_default() {
                let inner_ctx = ctx.with_local(var, value.clone());
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                let (key, projection_constraints) = if let Some(projection) = projection {
                    encode_prop_value_with_choose_constraints(
                        pool, vctx, defs, &inner_ctx, projection, step,
                    )?
                } else {
                    (value, vec![])
                };
                let include_raw = if projection_constraints.is_empty() {
                    filter_val
                } else {
                    let mut conjuncts = vec![filter_val];
                    conjuncts.extend(projection_constraints);
                    let refs: Vec<&Bool> = conjuncts.iter().collect();
                    smt::bool_and(&refs)
                };
                let mut include_once = include_raw.clone();
                for (prior_key, prior_filter) in &prior_keys {
                    let same_key = smt::smt_eq(&key, prior_key)?;
                    let prior_included_same_key = smt::bool_and(&[prior_filter, &same_key]);
                    include_once =
                        smt::bool_and(&[&include_once, &smt::bool_not(&prior_included_same_key)]);
                }
                terms.push(smt::int_ite(&include_once, &one, &zero));
                prior_keys.push((key, include_raw));
            }
            if terms.is_empty() {
                return Ok(smt::int_val(0));
            }
            let refs: Vec<&Int> = terms.iter().collect();
            Ok(SmtValue::Int(smt::int_add(&refs)))
        }
        // Entity-domain set comprehension: bounded sum over slots
        IRExpr::SetComp {
            var,
            domain: IRType::Entity { name: entity_name },
            filter,
            projection,
            ..
        } => {
            let n_slots = pool.slots_for(entity_name);
            let mut sum_terms: Vec<Int> = Vec::new();
            let mut prior_keys: Vec<(SmtValue, Bool)> = Vec::new();
            let one = smt::int_lit(1);
            let zero = smt::int_lit(0);

            for slot in 0..n_slots {
                let is_active = match pool.active_at(entity_name, slot, step) {
                    Some(SmtValue::Bool(act)) => act.clone(),
                    _ => continue,
                };
                let inner_ctx = ctx.with_binding(var, entity_name, slot);
                let filter_val = encode_prop_expr(pool, vctx, defs, &inner_ctx, filter, step)?;
                let (key, projection_constraints) = if let Some(projection) = projection {
                    encode_prop_value_with_choose_constraints(
                        pool, vctx, defs, &inner_ctx, projection, step,
                    )?
                } else {
                    (smt::int_val(i64::try_from(slot).unwrap_or(0)), vec![])
                };
                let mut cond_parts = vec![is_active, filter_val];
                cond_parts.extend(projection_constraints);
                let refs: Vec<&Bool> = cond_parts.iter().collect();
                let include_raw = smt::bool_and(&refs);
                let mut include_once = include_raw.clone();
                for (prior_key, prior_filter) in &prior_keys {
                    let same_key = smt::smt_eq(&key, prior_key)?;
                    let prior_included_same_key = smt::bool_and(&[prior_filter, &same_key]);
                    include_once =
                        smt::bool_and(&[&include_once, &smt::bool_not(&prior_included_same_key)]);
                }
                sum_terms.push(smt::int_ite(&include_once, &one, &zero));
                prior_keys.push((key, include_raw));
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

fn finite_set_algebra_keys(expr: &IRExpr) -> Option<HashSet<String>> {
    match expr {
        IRExpr::SetLit { elements, .. } => Some(
            elements
                .iter()
                .map(|element| format!("{element:?}"))
                .collect(),
        ),
        IRExpr::BinOp {
            op, left, right, ..
        } if matches!(
            op.as_str(),
            "OpDiamond" | "OpSetUnion" | "OpSetIntersect" | "OpSetDiff"
        ) =>
        {
            let left_keys = finite_set_algebra_keys(left)?;
            let right_keys = finite_set_algebra_keys(right)?;
            match op.as_str() {
                "OpDiamond" | "OpSetUnion" => Some(left_keys.union(&right_keys).cloned().collect()),
                "OpSetIntersect" => Some(left_keys.intersection(&right_keys).cloned().collect()),
                "OpSetDiff" => Some(left_keys.difference(&right_keys).cloned().collect()),
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
#[allow(clippy::needless_borrows_for_generic_args)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IREntity, IRField, IRMatchArm, IRPattern, IRProgram, IRSystem, IRType, IRTypeEntry,
        IRVariant, IRVariantField, LitVal,
    };
    use crate::verify::harness::create_slot_pool;

    fn empty_ir() -> IRProgram {
        IRProgram {
            interfaces: vec![],
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
                min_active: 0,
                slot_count: 3,
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
    fn property_encoder_rejects_future_temporal_fallbacks() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let true_expr = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        };
        let eventually = IRExpr::Eventually {
            body: Box::new(true_expr.clone()),
            span: None,
        };
        let until = IRExpr::Until {
            left: Box::new(true_expr.clone()),
            right: Box::new(true_expr),
            span: None,
        };

        let eventual_err = encode_prop_expr(&pool, &vctx, &defs, &ctx, &eventually, 0)
            .expect_err("eventually must not be weakened in property fallback");
        assert!(
            eventual_err.contains("future-time temporal"),
            "{eventual_err}"
        );
        let until_err = encode_prop_expr(&pool, &vctx, &defs, &ctx, &until, 0)
            .expect_err("until must not be weakened in property fallback");
        assert!(until_err.contains("future-time temporal"), "{until_err}");
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
            PropertyEncodingCtx {
                pool: &pool,
                vctx: &vctx,
                defs: &defs,
                property: &ctx,
                step: 0,
            },
            crate::ir::types::IRAggKind::Count,
            "b",
            &bool_var,
            None,
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
            PropertyEncodingCtx {
                pool: &pool,
                vctx: &vctx,
                defs: &defs,
                property: &ctx,
                step: 0,
            },
            crate::ir::types::IRAggKind::Max,
            "b",
            &bool_max_body,
            None,
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
    fn encode_prop_expr_with_ctx_supports_finite_payload_enum_aggregates() {
        let decision_ty = IRType::Enum {
            name: "Decision".to_owned(),
            variants: vec![
                IRVariant {
                    name: "Accept".to_owned(),
                    fields: vec![IRVariantField {
                        name: "allowed".to_owned(),
                        ty: IRType::Bool,
                    }],
                },
                IRVariant::simple("Reject"),
            ],
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![IRTypeEntry {
                name: "Decision".to_owned(),
                ty: decision_ty.clone(),
            }],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Aggregate {
                kind: crate::ir::types::IRAggKind::Count,
                var: "d".to_owned(),
                domain: decision_ty.clone(),
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "d".to_owned(),
                        ty: decision_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Decision".to_owned(),
                        ctor: "Reject".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                in_filter: None,
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

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("finite payload enum aggregate should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_finite_payload_enum_setcomp_values_and_cardinality() {
        let decision_ty = IRType::Enum {
            name: "Decision".to_owned(),
            variants: vec![
                IRVariant {
                    name: "Accept".to_owned(),
                    fields: vec![IRVariantField {
                        name: "allowed".to_owned(),
                        ty: IRType::Bool,
                    }],
                },
                IRVariant::simple("Reject"),
            ],
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![IRTypeEntry {
                name: "Decision".to_owned(),
                ty: decision_ty.clone(),
            }],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();
        let reject = IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Reject".to_owned(),
            args: vec![],
            span: None,
        };
        let reject_set = IRExpr::SetComp {
            var: "d".to_owned(),
            domain: decision_ty.clone(),
            source: None,
            filter: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "d".to_owned(),
                    ty: decision_ty.clone(),
                    span: None,
                }),
                right: Box::new(reject.clone()),
                ty: IRType::Bool,
                span: None,
            }),
            projection: None,
            ty: IRType::Set {
                element: Box::new(decision_ty),
            },
            span: None,
        };
        let member_property = IRExpr::Index {
            map: Box::new(reject_set.clone()),
            key: Box::new(reject),
            ty: IRType::Bool,
            span: None,
        };
        let card_property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Card {
                expr: Box::new(reject_set),
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

        for property in [member_property, card_property] {
            let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
                .expect("finite payload enum set-comprehension should encode");
            let solver = AbideSolver::new();
            solver.assert(smt::bool_not(&encoded));
            assert_eq!(solver.check(), SatResult::Unsat);
        }
    }

    #[test]
    fn encode_prop_value_rejects_unsupported_setcomp_domain_instead_of_empty_set() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();
        let real_set = IRExpr::SetComp {
            var: "x".to_owned(),
            domain: IRType::Real,
            source: None,
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: None,
            ty: IRType::Set {
                element: Box::new(IRType::Real),
            },
            span: None,
        };

        let err = encode_prop_value_with_ctx(&pool, &vctx, &defs, &ctx, &real_set, 0)
            .expect_err("unsupported set-comprehension domains must not encode as empty sets");
        assert!(
            err.contains("unsupported SetComp domain"),
            "diagnostic should name the unsupported SetComp domain, got: {err}"
        );
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
    fn encode_card_covers_finite_set_algebra() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();
        let int_lit = |value| IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        };
        let set_lit = |values: Vec<i64>| IRExpr::SetLit {
            elements: values.into_iter().map(int_lit).collect(),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        };
        let bin = |op: &str, left: IRExpr, right: IRExpr| IRExpr::BinOp {
            op: op.to_owned(),
            left: Box::new(left),
            right: Box::new(right),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        };

        let cases = [
            (
                bin("OpDiamond", set_lit(vec![1, 2]), set_lit(vec![2, 3])),
                3,
            ),
            (
                bin(
                    "OpSetIntersect",
                    set_lit(vec![1, 2, 3]),
                    set_lit(vec![2, 3, 4]),
                ),
                2,
            ),
            (
                bin("OpSetDiff", set_lit(vec![1, 2, 3]), set_lit(vec![2])),
                2,
            ),
        ];

        for (expr, expected) in cases {
            let card = encode_card(&pool, &vctx, &defs, &ctx, &expr, 0).expect("set algebra card");
            let solver = AbideSolver::new();
            solver.assert(&smt::bool_not(&smt::int_eq(
                card.as_int().expect("card int"),
                &smt::int_lit(expected),
            )));
            assert_eq!(solver.check(), SatResult::Unsat);
        }
    }

    #[test]
    fn encode_card_counts_tuple_projection_from_finite_map_domain_source() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let pool = empty_pool();
        let int_lit = |value| IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        };
        let map_ty = IRType::Map {
            key: Box::new(IRType::Int),
            value: Box::new(IRType::Int),
        };
        let tuple_ty = IRType::Tuple {
            elements: vec![IRType::Int, IRType::Int],
        };
        let map_lit = IRExpr::MapLit {
            entries: vec![(int_lit(1), int_lit(10)), (int_lit(2), int_lit(20))],
            ty: map_ty,
            span: None,
        };
        let entry_var = IRExpr::Var {
            name: "entry".to_owned(),
            ty: IRType::Int,
            span: None,
        };
        let set_comp = IRExpr::SetComp {
            var: "entry".to_owned(),
            domain: IRType::Int,
            source: Some(Box::new(IRExpr::UnOp {
                op: "OpMapDomain".to_owned(),
                operand: Box::new(map_lit.clone()),
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            })),
            filter: Box::new(bool_literal(true)),
            projection: Some(Box::new(IRExpr::Tuple {
                elements: vec![
                    entry_var.clone(),
                    IRExpr::Index {
                        map: Box::new(map_lit),
                        key: Box::new(entry_var),
                        ty: IRType::Int,
                        span: None,
                    },
                ],
                ty: tuple_ty.clone(),
                span: None,
            })),
            ty: IRType::Set {
                element: Box::new(tuple_ty),
            },
            span: None,
        };

        let card = encode_card(&pool, &vctx, &defs, &ctx, &set_comp, 0).expect("tuple set card");
        let solver = AbideSolver::new();
        solver.assert(&smt::bool_not(&smt::int_eq(
            card.as_int().expect("card int"),
            &smt::int_lit(2),
        )));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_covers_entity_quantifier_branches() {
        let entity = make_order_entity();
        let ir = IRProgram {
            interfaces: vec![],
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
    fn encode_prop_expr_with_ctx_supports_choose_in_value_ifelse_branches() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let choose_one = IRExpr::Choose {
            var: "candidate".to_owned(),
            domain: int_ty.clone(),
            predicate: Some(Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "candidate".to_owned(),
                    ty: int_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 1 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            })),
            ty: int_ty.clone(),
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::IfElse {
                cond: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                then_body: Box::new(choose_one),
                else_body: Some(Box::new(IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 0 },
                    span: None,
                })),
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("choose in value if/else branch should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn normalize_verifier_choose_hoists_value_ifelse_branch_choices() {
        let int_ty = IRType::Int;
        let expr = IRExpr::IfElse {
            cond: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            then_body: Box::new(IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: int_ty.clone(),
                predicate: None,
                ty: int_ty.clone(),
                span: None,
            }),
            else_body: Some(Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 0 },
                span: None,
            })),
            span: None,
        };

        let (bindings, normalized) =
            normalize_verifier_choose_term(&expr).expect("if/else choose normalization");
        assert_eq!(bindings.len(), 1);
        assert!(matches!(bindings[0].expr, IRExpr::Choose { .. }));
        assert!(matches!(normalized, IRExpr::IfElse { .. }));
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_choose_in_value_match_arms() {
        let outcome_ty = IRTypeEntry {
            name: "DecisionOutcome".to_owned(),
            ty: IRType::Enum {
                name: "DecisionOutcome".to_owned(),
                variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
            },
        };
        let ir = IRProgram {
            interfaces: vec![],
            types: vec![outcome_ty.clone()],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let choose_one = IRExpr::Choose {
            var: "candidate".to_owned(),
            domain: int_ty.clone(),
            predicate: Some(Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "candidate".to_owned(),
                    ty: int_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 1 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            })),
            ty: int_ty.clone(),
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Ctor {
                    enum_name: "DecisionOutcome".to_owned(),
                    ctor: "Open".to_owned(),
                    args: vec![],
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Open".to_owned(),
                            fields: vec![],
                        },
                        guard: None,
                        body: choose_one,
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: int_ty.clone(),
                            value: LitVal::Int { value: 0 },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("choose in value match arm should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn normalize_verifier_choose_hoists_value_match_arm_choices() {
        let int_ty = IRType::Int;
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Ctor {
                enum_name: "DecisionOutcome".to_owned(),
                ctor: "Open".to_owned(),
                args: vec![],
                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Open".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: IRExpr::Choose {
                    var: "candidate".to_owned(),
                    domain: int_ty.clone(),
                    predicate: None,
                    ty: int_ty,
                    span: None,
                },
            }],
            span: None,
        };

        let (bindings, normalized) =
            normalize_verifier_choose_term(&expr).expect("match choose normalization");
        assert_eq!(bindings.len(), 1);
        assert!(matches!(bindings[0].expr, IRExpr::Choose { .. }));
        assert!(matches!(normalized, IRExpr::Match { .. }));
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_independent_choose_in_binding_match_arms() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let match_expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Lit {
                ty: int_ty.clone(),
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "scrutinee_value".to_owned(),
                },
                guard: None,
                body: IRExpr::Choose {
                    var: "candidate".to_owned(),
                    domain: int_ty.clone(),
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "candidate".to_owned(),
                            ty: int_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: int_ty.clone(),
                            value: LitVal::Int { value: 1 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: int_ty.clone(),
                    span: None,
                },
            }],
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(match_expr),
            right: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("independent choose in binding match arm should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_dependent_choose_in_binding_match_arms() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let match_expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Lit {
                ty: int_ty.clone(),
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "scrutinee_value".to_owned(),
                },
                guard: None,
                body: IRExpr::Choose {
                    var: "candidate".to_owned(),
                    domain: int_ty.clone(),
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "candidate".to_owned(),
                            ty: int_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "scrutinee_value".to_owned(),
                                ty: int_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: int_ty.clone(),
                                value: LitVal::Int { value: 1 },
                                span: None,
                            }),
                            ty: int_ty.clone(),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: int_ty.clone(),
                    span: None,
                },
            }],
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(match_expr),
            right: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("dependent choose in binding match arm should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn normalize_verifier_choose_hoists_independent_binding_match_arm_choices() {
        let int_ty = IRType::Int;
        let expr = IRExpr::Match {
            scrutinee: Box::new(IRExpr::Lit {
                ty: int_ty.clone(),
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "scrutinee_value".to_owned(),
                },
                guard: None,
                body: IRExpr::Choose {
                    var: "candidate".to_owned(),
                    domain: int_ty.clone(),
                    predicate: None,
                    ty: int_ty,
                    span: None,
                },
            }],
            span: None,
        };

        let (bindings, normalized) =
            normalize_verifier_choose_term(&expr).expect("binding match arm choose");
        assert_eq!(bindings.len(), 1);
        assert!(matches!(bindings[0].expr, IRExpr::Choose { .. }));
        assert!(matches!(normalized, IRExpr::Match { .. }));
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_independent_choose_in_setcomp_projection() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let set_int_ty = IRType::Set {
            element: Box::new(int_ty.clone()),
        };
        let set_comp = IRExpr::SetComp {
            var: "x".to_owned(),
            domain: int_ty.clone(),
            source: Some(Box::new(IRExpr::SetLit {
                elements: vec![IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 0 },
                    span: None,
                }],
                ty: set_int_ty.clone(),
                span: None,
            })),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: int_ty.clone(),
                predicate: Some(Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "candidate".to_owned(),
                        ty: int_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: int_ty.clone(),
                        value: LitVal::Int { value: 1 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                })),
                ty: int_ty.clone(),
                span: None,
            })),
            ty: set_int_ty,
            span: None,
        };
        let property = IRExpr::Index {
            map: Box::new(set_comp),
            key: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("independent choose in set-comprehension projection should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_dependent_choose_in_setcomp_projection() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let set_int_ty = IRType::Set {
            element: Box::new(int_ty.clone()),
        };
        let set_comp = IRExpr::SetComp {
            var: "x".to_owned(),
            domain: int_ty.clone(),
            source: Some(Box::new(IRExpr::SetLit {
                elements: vec![IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 1 },
                    span: None,
                }],
                ty: set_int_ty.clone(),
                span: None,
            })),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: int_ty.clone(),
                predicate: Some(Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "candidate".to_owned(),
                        ty: int_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
                            ty: int_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: int_ty.clone(),
                            value: LitVal::Int { value: 1 },
                            span: None,
                        }),
                        ty: int_ty.clone(),
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                })),
                ty: int_ty.clone(),
                span: None,
            })),
            ty: set_int_ty,
            span: None,
        };
        let property = IRExpr::Index {
            map: Box::new(set_comp),
            key: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("dependent choose in set-comprehension projection should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_entity_choose_in_setcomp_projection() {
        let order = make_order_entity();
        let scopes = HashMap::from([("Order".to_owned(), 1usize)]);
        let pool = create_slot_pool(&[order], &scopes, 0);
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let set_int_ty = IRType::Set {
            element: Box::new(int_ty.clone()),
        };
        let set_comp = IRExpr::SetComp {
            var: "x".to_owned(),
            domain: int_ty.clone(),
            source: Some(Box::new(IRExpr::SetLit {
                elements: vec![IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 1 },
                    span: None,
                }],
                ty: set_int_ty.clone(),
                span: None,
            })),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    expr: IRExpr::Choose {
                        var: "candidate".to_owned(),
                        domain: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "candidate".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "status".to_owned(),
                                ty: int_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::Lit {
                                ty: int_ty.clone(),
                                value: LitVal::Int { value: 7 },
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: int_ty.clone(),
                    span: None,
                }),
                span: None,
            })),
            ty: set_int_ty,
            span: None,
        };
        let property = IRExpr::Index {
            map: Box::new(set_comp),
            key: Box::new(IRExpr::Lit {
                ty: int_ty,
                value: LitVal::Int { value: 7 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("entity choose in set-comprehension projection should encode");
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
            solver.assert(active);
        }
        if let Some(SmtValue::Int(status)) = pool.field_at("Order", 0, "status", 0) {
            solver.assert(smt::int_eq(status, &smt::int_lit(7)));
        }
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_counts_entity_choose_projection_cardinality() {
        let order = make_order_entity();
        let scopes = HashMap::from([("Order".to_owned(), 1usize)]);
        let pool = create_slot_pool(&[order], &scopes, 0);
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let set_int_ty = IRType::Set {
            element: Box::new(int_ty.clone()),
        };
        let card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "x".to_owned(),
                domain: int_ty.clone(),
                source: Some(Box::new(IRExpr::SetLit {
                    elements: vec![IRExpr::Lit {
                        ty: int_ty.clone(),
                        value: LitVal::Int { value: 1 },
                        span: None,
                    }],
                    ty: set_int_ty.clone(),
                    span: None,
                })),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                projection: Some(Box::new(IRExpr::Let {
                    bindings: vec![crate::ir::types::LetBinding {
                        name: "picked".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        expr: IRExpr::Choose {
                            var: "candidate".to_owned(),
                            domain: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            predicate: Some(Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "candidate".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "status".to_owned(),
                                    ty: int_ty.clone(),
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Lit {
                                    ty: int_ty.clone(),
                                    value: LitVal::Int { value: 7 },
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            })),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "picked".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: int_ty.clone(),
                        span: None,
                    }),
                    span: None,
                })),
                ty: set_int_ty,
                span: None,
            }),
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(card),
            right: Box::new(IRExpr::Lit {
                ty: int_ty.clone(),
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("entity choose projection cardinality should encode");
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
            solver.assert(active);
        }
        if let Some(SmtValue::Int(status)) = pool.field_at("Order", 0, "status", 0) {
            solver.assert(smt::int_eq(status, &smt::int_lit(7)));
        }
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_bool_setcomp_cardinality() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let bool_set_ty = IRType::Set {
            element: Box::new(IRType::Bool),
        };
        let card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "b".to_owned(),
                domain: IRType::Bool,
                source: None,
                filter: Box::new(IRExpr::Var {
                    name: "b".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                projection: None,
                ty: bool_set_ty,
                span: None,
            }),
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(card),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("Bool set-comprehension cardinality should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_fieldless_enum_setcomp_cardinality() {
        let enum_ty = IRType::Enum {
            name: "State".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        };
        let mut ir = empty_ir();
        ir.types.push(IRTypeEntry {
            name: "State".to_owned(),
            ty: enum_ty.clone(),
        });
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let enum_set_ty = IRType::Set {
            element: Box::new(enum_ty.clone()),
        };
        let card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "state".to_owned(),
                domain: enum_ty,
                source: None,
                filter: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "state".to_owned(),
                        ty: IRType::Enum {
                            name: "State".to_owned(),
                            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
                        },
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "State".to_owned(),
                        ctor: "Open".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                projection: None,
                ty: enum_set_ty,
                span: None,
            }),
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(card),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("fieldless enum set-comprehension cardinality should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_finite_domain_setcomp_values() {
        let enum_ty = IRType::Enum {
            name: "State".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        };
        let mut ir = empty_ir();
        ir.types.push(IRTypeEntry {
            name: "State".to_owned(),
            ty: enum_ty.clone(),
        });
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();

        let bool_set = IRExpr::SetComp {
            var: "b".to_owned(),
            domain: IRType::Bool,
            source: None,
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            })),
            ty: IRType::Set {
                element: Box::new(IRType::Bool),
            },
            span: None,
        };
        let true_member = IRExpr::Index {
            map: Box::new(bool_set),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let enum_set = IRExpr::SetComp {
            var: "state".to_owned(),
            domain: enum_ty.clone(),
            source: None,
            filter: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "state".to_owned(),
                    ty: enum_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "State".to_owned(),
                    ctor: "Open".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            projection: None,
            ty: IRType::Set {
                element: Box::new(enum_ty),
            },
            span: None,
        };
        let open_member = IRExpr::Index {
            map: Box::new(enum_set),
            key: Box::new(IRExpr::Ctor {
                enum_name: "State".to_owned(),
                ctor: "Open".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        for property in [true_member, open_member] {
            let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
                .expect("finite-domain set-comprehension value should encode");
            let solver = AbideSolver::new();
            solver.assert(smt::bool_not(&encoded));
            assert_eq!(solver.check(), SatResult::Unsat);
        }
    }

    #[test]
    fn encode_prop_expr_with_ctx_counts_projected_finite_domain_setcomp_cardinality() {
        let enum_ty = IRType::Enum {
            name: "State".to_owned(),
            variants: vec![IRVariant::simple("Open"), IRVariant::simple("Closed")],
        };
        let mut ir = empty_ir();
        ir.types.push(IRTypeEntry {
            name: "State".to_owned(),
            ty: enum_ty.clone(),
        });
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();

        let bool_card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "b".to_owned(),
                domain: IRType::Bool,
                source: None,
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                projection: Some(Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                })),
                ty: IRType::Set {
                    element: Box::new(IRType::Bool),
                },
                span: None,
            }),
            span: None,
        };
        let bool_property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(bool_card),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let enum_card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "state".to_owned(),
                domain: enum_ty.clone(),
                source: None,
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                projection: Some(Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "state".to_owned(),
                        ty: enum_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "State".to_owned(),
                        ctor: "Open".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                })),
                ty: IRType::Set {
                    element: Box::new(IRType::Bool),
                },
                span: None,
            }),
            span: None,
        };
        let enum_property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(enum_card),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        for property in [bool_property, enum_property] {
            let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
                .expect("projected finite-domain set-comprehension cardinality should encode");
            let solver = AbideSolver::new();
            solver.assert(smt::bool_not(&encoded));
            assert_eq!(solver.check(), SatResult::Unsat);
        }
    }

    #[test]
    fn encode_card_counts_distinct_entity_projection_values() {
        let entity = make_order_entity();
        let ir = IRProgram {
            interfaces: vec![],
            entities: vec![entity.clone()],
            ..empty_ir()
        };
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let mut scopes = HashMap::new();
        scopes.insert("Order".to_owned(), 2usize);
        let pool = create_slot_pool(&[entity], &scopes, 0);
        let ctx = PropertyCtx::new();
        let projected = IRExpr::SetComp {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            source: None,
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Field {
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
            })),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        };

        let count = encode_card(&pool, &vctx, &defs, &ctx, &projected, 0)
            .expect("entity projection cardinality should encode");
        let solver = AbideSolver::new();
        solver.assert(pool.active_at("Order", 0, 0).unwrap().to_bool().unwrap());
        solver.assert(pool.active_at("Order", 1, 0).unwrap().to_bool().unwrap());
        solver.assert(
            smt::smt_eq(
                pool.field_at("Order", 0, "status", 0).unwrap(),
                &smt::int_val(7),
            )
            .unwrap(),
        );
        solver.assert(
            smt::smt_eq(
                pool.field_at("Order", 1, "status", 0).unwrap(),
                &smt::int_val(7),
            )
            .unwrap(),
        );
        solver.assert(smt::bool_not(
            &smt::smt_eq(&count, &smt::int_val(1)).unwrap(),
        ));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_finite_sourced_setcomp_cardinality() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = defenv::DefEnv::from_ir(&ir);
        let pool = empty_pool();
        let ctx = PropertyCtx::new();
        let int_ty = IRType::Int;
        let set_int_ty = IRType::Set {
            element: Box::new(int_ty.clone()),
        };
        let card = IRExpr::Card {
            expr: Box::new(IRExpr::SetComp {
                var: "x".to_owned(),
                domain: int_ty.clone(),
                source: Some(Box::new(IRExpr::SetLit {
                    elements: vec![
                        IRExpr::Lit {
                            ty: int_ty.clone(),
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                        IRExpr::Lit {
                            ty: int_ty.clone(),
                            value: LitVal::Int { value: 2 },
                            span: None,
                        },
                        IRExpr::Lit {
                            ty: int_ty.clone(),
                            value: LitVal::Int { value: 2 },
                            span: None,
                        },
                    ],
                    ty: set_int_ty.clone(),
                    span: None,
                })),
                filter: Box::new(IRExpr::BinOp {
                    op: "OpGt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: int_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: int_ty.clone(),
                        value: LitVal::Int { value: 1 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                projection: None,
                ty: set_int_ty,
                span: None,
            }),
            span: None,
        };
        let property = IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(card),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("finite sourced set-comprehension cardinality should encode");
        let solver = AbideSolver::new();
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_with_ctx_supports_store_sourced_projected_setcomp_values() {
        let entity = make_order_entity();
        let ir = IRProgram {
            interfaces: vec![],
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
            "orders".to_owned(),
            crate::verify::scope::VerifyStoreRange {
                entity_type: "Order".to_owned(),
                start_slot: 0,
                min_active: 0,
                slot_count: 2,
            },
        );
        let ctx = PropertyCtx::new().with_store_ranges(ranges);

        let order_ty = IRType::Entity {
            name: "Order".to_owned(),
        };
        let set_int_ty = IRType::Set {
            element: Box::new(IRType::Int),
        };
        let status_set = IRExpr::SetComp {
            var: "o".to_owned(),
            domain: order_ty.clone(),
            source: Some(Box::new(IRExpr::Var {
                name: "orders".to_owned(),
                ty: IRType::Set {
                    element: Box::new(order_ty.clone()),
                },
                span: None,
            })),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "o".to_owned(),
                    ty: order_ty,
                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,
                span: None,
            })),
            ty: set_int_ty,
            span: None,
        };
        let property = IRExpr::Index {
            map: Box::new(status_set),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 7 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        };

        let encoded = encode_prop_expr_with_ctx(&pool, &vctx, &defs, &ctx, &property, 0)
            .expect("store-sourced projection set-comprehension should encode");
        let solver = AbideSolver::new();
        solver.assert(pool.active_at("Order", 0, 0).unwrap().to_bool().unwrap());
        solver.assert(pool.active_at("Order", 1, 0).unwrap().to_bool().unwrap());
        solver.assert(
            smt::smt_eq(
                pool.field_at("Order", 0, "status", 0).unwrap(),
                &smt::int_val(7),
            )
            .unwrap(),
        );
        solver.assert(
            smt::smt_eq(
                pool.field_at("Order", 1, "status", 0).unwrap(),
                &smt::int_val(3),
            )
            .unwrap(),
        );
        solver.assert(smt::bool_not(&encoded));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn normalize_verifier_choose_hoists_independent_setcomp_projection_choices() {
        let int_ty = IRType::Int;
        let set_int_ty = IRType::Set {
            element: Box::new(int_ty.clone()),
        };
        let expr = IRExpr::SetComp {
            var: "x".to_owned(),
            domain: int_ty.clone(),
            source: Some(Box::new(IRExpr::SetLit {
                elements: vec![IRExpr::Lit {
                    ty: int_ty.clone(),
                    value: LitVal::Int { value: 0 },
                    span: None,
                }],
                ty: set_int_ty.clone(),
                span: None,
            })),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            projection: Some(Box::new(IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: int_ty.clone(),
                predicate: None,
                ty: int_ty,
                span: None,
            })),
            ty: set_int_ty,
            span: None,
        };

        let (bindings, normalized) =
            normalize_verifier_choose_term(&expr).expect("setcomp projection choose");
        assert_eq!(bindings.len(), 1);
        assert!(matches!(bindings[0].expr, IRExpr::Choose { .. }));
        assert!(matches!(normalized, IRExpr::SetComp { .. }));
    }

    #[test]
    fn encode_prop_expr_respects_store_scoped_entity_quantifiers() {
        let entity = make_order_entity();
        let ir = IRProgram {
            interfaces: vec![],
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
                min_active: 0,
                slot_count: 1,
            },
        );
        ranges.insert(
            "archived".to_owned(),
            crate::verify::scope::VerifyStoreRange {
                entity_type: "Order".to_owned(),
                start_slot: 1,
                min_active: 0,
                slot_count: 1,
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
        let slot_0_ctx = ctx.with_binding("o", "Order", 0);
        let pending_membership = encode_prop_expr(
            &pool,
            &vctx,
            &defs,
            &slot_0_ctx,
            &membership("pending", "o"),
            0,
        )
        .expect("direct pending membership");
        let archived_membership = encode_prop_expr(
            &pool,
            &vctx,
            &defs,
            &slot_0_ctx,
            &membership("archived", "o"),
            0,
        )
        .expect("direct archived membership");

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

        let solver = AbideSolver::new();
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&smt::bool_not(&pending_membership));
        assert_eq!(solver.check(), SatResult::Unsat);

        let solver = AbideSolver::new();
        solver.assert(
            pool.active_at("Order", 0, 0)
                .expect("active0")
                .to_bool()
                .expect("bool"),
        );
        solver.assert(&archived_membership);
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn encode_prop_expr_covers_non_entity_quantifier_branches() {
        let ir = IRProgram {
            interfaces: vec![],
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
