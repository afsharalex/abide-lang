//! IR → Z3 term encoding.
//!
//! Compiles Abide IR expressions to Z3 AST values.
//! Handles literals, variables, binary/unary ops, quantifiers,
//! field access, primed notation, and temporal operators.
//!
//! Uses z3 crate v0.19 API (no explicit Context parameter).

use std::collections::HashMap;

use z3::ast::{Bool, Dynamic, Int, Real};

use crate::ir::types::{IREntity, IRExpr, IRType, LitVal};

use super::context::VerifyContext;
use super::smt::{self, SmtValue};

// ── Entity pool ─────────────────────────────────────────────────────

/// Time-stepped Z3 variables for all fields of all entities in the pool.
///
/// For each entity type × field × time step, there is a Z3 variable.
/// Variables are named `{entity}_{field}_t{step}` to avoid collisions.
/// # Current model (Phase 1): single slot per entity type
///
/// Each entity type has ONE set of field variables across time steps.
/// This is sufficient for Phase 1 expression encoding and unit tests.
///
/// # Phase 2 target: multi-slot pool model
///
/// For actual BMC, each entity type needs N slots (from scope bound):
/// - `Order_slot0_status_t0`, `Order_slot1_status_t0`, ...
/// - Each slot has its own `active` flag
/// - Quantifiers (`all o: Order`) range over slot indices 0..N
///   where `active[slot][step]` is true
/// - Field access `o.status` resolves to `Order_slot{o}_status_t{step}`
/// - `create` activates an inactive slot
///
/// The multi-slot model is required for:
/// - Distinguishing `x.status` vs `y.status` (different slots)
/// - Sound entity quantifiers (range over active slots only)
/// - `create`/`destroy` semantics (activate/deactivate slots)
#[derive(Debug)]
pub struct EntityPool {
    /// (`entity_name`, `field_name`) → vec of time-stepped `SmtValue`s
    ///
    /// Phase 1: one variable per (entity, field, step).
    /// Phase 2: will become (entity, slot, field) → vec per step.
    pub vars: HashMap<(String, String), Vec<SmtValue>>,
    /// `entity_name` → vec of time-stepped `Bool` active flags.
    ///
    /// Phase 1: one active flag per (entity, step) — single slot.
    /// Phase 2: will become (entity, slot) → vec per step.
    pub active: HashMap<String, Vec<SmtValue>>,
    /// Number of time steps (bound + 1)
    pub steps: usize,
}

impl EntityPool {
    /// Look up a field variable at a specific time step.
    /// Returns `None` if the entity/field combination doesn't exist.
    pub fn get(&self, entity: &str, field: &str, step: usize) -> Option<&SmtValue> {
        self.vars
            .get(&(entity.to_owned(), field.to_owned()))
            .and_then(|v| v.get(step))
    }

    /// Look up the active flag for an entity at a specific time step.
    pub fn get_active(&self, entity: &str, step: usize) -> Option<&SmtValue> {
        self.active.get(entity).and_then(|v| v.get(step))
    }
}

/// Create an entity pool with time-stepped Z3 variables for all entities.
///
/// For each entity in the IR, creates `bound + 1` Z3 variables per field
/// (named `{entity}_{field}_t{step}`) plus an `active` boolean per step.
pub fn create_entity_pool(entities: &[IREntity], bound: usize) -> EntityPool {
    let mut vars = HashMap::new();
    let mut active = HashMap::new();

    for entity in entities {
        // Active flag per time step
        let active_vars: Vec<SmtValue> = (0..=bound)
            .map(|step| smt::bool_var(&format!("{}_active_t{}", entity.name, step)))
            .collect();
        active.insert(entity.name.clone(), active_vars);

        // Field variables per time step
        for field in &entity.fields {
            let field_vars: Vec<SmtValue> = (0..=bound)
                .map(|step| {
                    let name = format!("{}_{}_t{}", entity.name, field.name, step);
                    match &field.ty {
                        IRType::Bool => smt::bool_var(&name),
                        IRType::Real | IRType::Float => smt::real_var(&name),
                        _ => smt::int_var(&name),
                    }
                })
                .collect();
            vars.insert((entity.name.clone(), field.name.clone()), field_vars);
        }
    }

    EntityPool {
        vars,
        active,
        steps: bound + 1,
    }
}

// ── Encoding context ────────────────────────────────────────────────

/// Context passed through expression encoding.
///
/// Tracks the entity scope (which entity's fields are in scope),
/// bound variables from quantifiers, and the entity pool.
pub struct EncodeCtx<'a> {
    pub vctx: &'a VerifyContext,
    pub pool: &'a EntityPool,
    /// Current entity scope for bare field name resolution.
    /// Set when encoding within a `choose`/`for` block.
    pub entity_scope: Option<String>,
    /// Variables bound by quantifiers (name → Z3 value).
    pub bound_vars: HashMap<String, SmtValue>,
}

// ── Expression encoding ─────────────────────────────────────────────

/// Encode an IR expression to a Z3 value at a given time step.
///
/// `step` determines which time-stepped variable to use for field references.
/// Primed expressions resolve to `step + 1`.
#[allow(clippy::match_same_arms, clippy::too_many_lines)]
pub fn encode_expr(ctx: &EncodeCtx<'_>, expr: &IRExpr, step: usize) -> SmtValue {
    match expr {
        // ── Literals ────────────────────────────────────────────
        IRExpr::Lit { value, .. } => encode_literal(value),

        // ── Variables ───────────────────────────────────────────
        IRExpr::Var { name, .. } => {
            // 1. Check quantifier-bound variables first
            if let Some(val) = ctx.bound_vars.get(name.as_str()) {
                return val.clone();
            }
            // 2. Check entity pool with current scope (entity-qualified)
            if let Some(ref entity) = ctx.entity_scope {
                if let Some(val) = ctx.pool.get(entity, name, step) {
                    return val.clone();
                }
            }
            // 3. No ambiguous fallback — require entity scope for field refs.
            // Collect all matches to report ambiguity clearly.
            let matches: Vec<_> = ctx
                .pool
                .vars
                .keys()
                .filter(|(_, f)| f == name)
                .map(|(e, _)| e.as_str())
                .collect();
            match matches.len() {
                0 => panic!("variable not found: {name} (entity_scope: {:?})", ctx.entity_scope),
                1 => ctx.pool.get(matches[0], name, step).unwrap().clone(),
                _ => panic!(
                    "ambiguous variable: {name} exists in entities {matches:?} — set entity_scope to disambiguate"
                ),
            }
        }

        // ── Constructors (enum variants) ────────────────────────
        IRExpr::Ctor {
            enum_name, ctor, ..
        } => {
            let id = ctx.vctx.variants.id_of(enum_name, ctor);
            smt::int_val(id)
        }

        // ── Binary operations ───────────────────────────────────
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = encode_expr(ctx, left, step);
            let r = encode_expr(ctx, right, step);
            smt::binop(op, &l, &r)
        }

        // ── Unary operations ────────────────────────────────────
        IRExpr::UnOp { op, operand, .. } => {
            let v = encode_expr(ctx, operand, step);
            smt::unop(op, &v)
        }

        // ── Field access ────────────────────────────────────────
        IRExpr::Field {
            expr: _recv, field, ..
        } => {
            // KNOWN LIMITATION (Phase 1): the receiver expression is not used
            // to determine which entity SLOT to access. In the single-slot model,
            // there's only one variable per (entity, field, step), so x.status
            // and y.status resolve to the same variable.
            //
            // Phase 2 fix: receiver resolves to a slot index, and field access
            // becomes Order_slot{index}_{field}_t{step}.
            let resolved_scope = ctx.entity_scope.clone();
            if let Some(ref entity) = resolved_scope {
                if let Some(val) = ctx.pool.get(entity, field, step) {
                    return val.clone();
                }
            }
            // No ambiguous fallback — require scope
            let matches: Vec<_> = ctx
                .pool
                .vars
                .keys()
                .filter(|(_, f)| f == field)
                .map(|(e, _)| e.as_str())
                .collect();
            match matches.len() {
                0 => panic!("field not found: {field}"),
                1 => ctx.pool.get(matches[0], field, step).unwrap().clone(),
                _ => panic!(
                    "ambiguous field: {field} exists in entities {matches:?} — entity scope required"
                ),
            }
        }

        // ── Primed (next-state) ─────────────────────────────────
        IRExpr::Prime { expr } => encode_expr(ctx, expr, step + 1),

        // ── Temporal operators ──────────────────────────────────
        // For BMC, these are handled at the harness level (unrolling).
        // In expression context, encode the body at the current step.
        IRExpr::Always { body } => encode_expr(ctx, body, step),
        IRExpr::Eventually { body } => encode_expr(ctx, body, step),

        // ── Quantifiers ─────────────────────────────────────────
        // KNOWN LIMITATION (Phase 1): entity quantifiers create an
        // unconstrained Int variable. Phase 2 must:
        // - Constrain to valid slot indices (0..pool_size)
        // - Restrict to active slots (active[slot][step] == true)
        // - Thread slot index into field resolution
        IRExpr::Forall {
            var, domain, body, ..
        } => {
            let (smt_var, dyn_ast) = create_typed_var(var, domain);
            let mut inner_bound = ctx.bound_vars.clone();
            inner_bound.insert(var.clone(), smt_var);
            // If domain is an entity type, set entity_scope for field resolution
            let inner_scope = match domain {
                IRType::Entity { name } => Some(name.clone()),
                _ => ctx.entity_scope.clone(),
            };
            let inner_ctx = EncodeCtx {
                vctx: ctx.vctx,
                pool: ctx.pool,
                entity_scope: inner_scope,
                bound_vars: inner_bound,
            };
            let body_val = encode_expr(&inner_ctx, body, step);
            SmtValue::Bool(z3::ast::forall_const(&[&dyn_ast], &[], body_val.as_bool()))
        }
        IRExpr::Exists {
            var, domain, body, ..
        } => {
            let (smt_var, dyn_ast) = create_typed_var(var, domain);
            let mut inner_bound = ctx.bound_vars.clone();
            inner_bound.insert(var.clone(), smt_var);
            let inner_scope = match domain {
                IRType::Entity { name } => Some(name.clone()),
                _ => ctx.entity_scope.clone(),
            };
            let inner_ctx = EncodeCtx {
                vctx: ctx.vctx,
                pool: ctx.pool,
                entity_scope: inner_scope,
                bound_vars: inner_bound,
            };
            let body_val = encode_expr(&inner_ctx, body, step);
            SmtValue::Bool(z3::ast::exists_const(&[&dyn_ast], &[], body_val.as_bool()))
        }

        // ── Let bindings ────────────────────────────────────────
        IRExpr::Let { body, .. } => {
            // TODO: substitute bindings into body
            encode_expr(ctx, body, step)
        }

        // ── Lambda / Application ────────────────────────────────
        IRExpr::Lam { body, .. } => encode_expr(ctx, body, step),
        IRExpr::App { func, .. } => encode_expr(ctx, func, step),

        // ── Unimplemented expression forms ──────────────────────
        // These panic rather than returning placeholder values to
        // avoid silent false positives in verification.
        IRExpr::Match { .. } => {
            unimplemented!("Match encoding not yet implemented — requires ITE chain translation")
        }
        IRExpr::MapUpdate { .. } => {
            unimplemented!("MapUpdate encoding not yet implemented — requires Z3 array theory")
        }
        IRExpr::Index { .. } => {
            unimplemented!("Index encoding not yet implemented — requires Z3 array select")
        }
        IRExpr::SetLit { .. } => {
            unimplemented!("SetLit encoding not yet implemented — requires Z3 set theory")
        }
        IRExpr::SeqLit { .. } => {
            unimplemented!("SeqLit encoding not yet implemented — requires Z3 sequence theory")
        }
        IRExpr::MapLit { .. } => {
            unimplemented!("MapLit encoding not yet implemented — requires Z3 array theory")
        }
        IRExpr::SetComp { .. } => {
            unimplemented!("SetComp encoding not yet implemented — requires Z3 set comprehension")
        }

        // ── Stubs ───────────────────────────────────────────────
        IRExpr::Sorry | IRExpr::Todo => smt::bool_val(true),
    }
}

// ── Typed variable creation ──────────────────────────────────────────

/// Create a Z3 variable with the correct sort for the given IR type.
///
/// Returns both the `SmtValue` (for use in the encoding context) and
/// a `Dynamic` (for use with `forall_const`/`exists_const`).
fn create_typed_var(name: &str, domain: &IRType) -> (SmtValue, Dynamic) {
    match domain {
        IRType::Bool => {
            let v = Bool::new_const(name);
            (SmtValue::Bool(v.clone()), Dynamic::from(v))
        }
        IRType::Real | IRType::Float => {
            let v = Real::new_const(name);
            (SmtValue::Real(v.clone()), Dynamic::from(v))
        }
        // Int, Id, Enum, Entity, String, and everything else → Int sort
        _ => {
            let v = Int::new_const(name);
            (SmtValue::Int(v.clone()), Dynamic::from(v))
        }
    }
}

// ── Literal encoding ────────────────────────────────────────────────

fn encode_literal(lit: &LitVal) -> SmtValue {
    match lit {
        LitVal::Int { value } => smt::int_val(*value),
        LitVal::Bool { value } => smt::bool_val(*value),
        LitVal::Real { value } | LitVal::Float { value } => {
            // Approximate f64 as rational: multiply by 1_000_000, divide by 1_000_000
            #[allow(clippy::cast_possible_truncation)]
            let scaled = (*value * 1_000_000.0) as i64;
            smt::real_val(scaled, 1_000_000)
        }
        LitVal::Str { .. } => smt::int_val(0), // strings as uninterpreted for now
    }
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::IRField;
    use z3::Solver;

    fn empty_ctx() -> (VerifyContext, EntityPool) {
        let vctx = VerifyContext {
            variants: super::super::context::VariantMap::new(),
            enum_ranges: HashMap::new(),
            entities: HashMap::new(),
        };
        let pool = EntityPool {
            vars: HashMap::new(),
            active: HashMap::new(),
            steps: 1,
        };
        (vctx, pool)
    }

    #[test]
    fn int_literal_encoding() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        let expr = IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 42 },
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Int(_)));
    }

    #[test]
    fn bool_literal_encoding() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        let expr = IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Bool(_)));
    }

    #[test]
    fn binop_int_add() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        let expr = IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 3 },
            }),
            ty: IRType::Int,
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Int(_)));
    }

    #[test]
    fn binop_bool_and() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        let expr = IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
            }),
            ty: IRType::Bool,
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Bool(_)));
    }

    #[test]
    fn unop_not() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        let expr = IRExpr::UnOp {
            op: "OpNot".to_owned(),
            operand: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
            }),
            ty: IRType::Bool,
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Bool(_)));
    }

    #[test]
    fn entity_pool_creation() {
        let entities = vec![IREntity {
            name: "Order".to_owned(),
            fields: vec![
                IRField {
                    name: "id".to_owned(),
                    ty: IRType::Id,
                    default: None,
                },
                IRField {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    default: None,
                },
            ],
            transitions: vec![],
        }];

        let pool = create_entity_pool(&entities, 3);
        assert_eq!(pool.steps, 4);
        assert!(pool.get("Order", "id", 0).is_some());
        assert!(pool.get("Order", "id", 3).is_some());
        assert!(pool.get("Order", "status", 2).is_some());
        assert!(pool.get("Order", "nonexistent", 0).is_none());
        assert!(pool.get("Unknown", "id", 0).is_none());
    }

    #[test]
    fn field_var_lookup_with_entity_scope() {
        let entities = vec![
            IREntity {
                name: "Order".to_owned(),
                fields: vec![IRField {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    default: None,
                }],
                transitions: vec![],
            },
            IREntity {
                name: "Payment".to_owned(),
                fields: vec![IRField {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    default: None,
                }],
                transitions: vec![],
            },
        ];
        let pool = create_entity_pool(&entities, 1);

        // Both entities have "status" — entity_scope disambiguates
        assert!(pool.get("Order", "status", 0).is_some());
        assert!(pool.get("Payment", "status", 0).is_some());
    }

    #[test]
    fn enum_variant_encoding() {
        let mut vctx = VerifyContext {
            variants: super::super::context::VariantMap::new(),
            enum_ranges: HashMap::new(),
            entities: HashMap::new(),
        };
        vctx.variants.register_enum(
            "OrderStatus",
            &[
                "Pending".to_owned(),
                "Confirmed".to_owned(),
                "Shipped".to_owned(),
            ],
        );

        let pool = EntityPool {
            vars: HashMap::new(),
            active: HashMap::new(),
            steps: 1,
        };
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        let expr = IRExpr::Ctor {
            enum_name: "OrderStatus".to_owned(),
            ctor: "Confirmed".to_owned(),
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Int(_)));
    }

    #[test]
    fn z3_satisfiability_check() {
        let solver = Solver::new();

        let x = Int::new_const("x");
        solver.assert(&x.gt(&Int::from_i64(0)));
        assert_eq!(solver.check(), z3::SatResult::Sat);

        solver.assert(&x.lt(&Int::from_i64(0)));
        assert_eq!(solver.check(), z3::SatResult::Unsat);
    }

    #[test]
    fn z3_enum_domain_constraint() {
        let solver = Solver::new();

        let status = Int::new_const("status");
        solver.assert(&status.ge(&Int::from_i64(0)));
        solver.assert(&status.le(&Int::from_i64(2)));

        solver.push();
        solver.assert(&status.eq(Int::from_i64(1)));
        assert_eq!(solver.check(), z3::SatResult::Sat);
        solver.pop(1);

        solver.push();
        solver.assert(&status.eq(Int::from_i64(5)));
        assert_eq!(solver.check(), z3::SatResult::Unsat);
        solver.pop(1);
    }

    #[test]
    fn quantifier_forall_encoding() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        // forall x: Int | x > 0 implies x >= 1
        let expr = IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpImplies".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpGt".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                    }),
                    ty: IRType::Bool,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                    }),
                    ty: IRType::Bool,
                }),
                ty: IRType::Bool,
            }),
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Bool(_)));

        // Check it's valid (tautology): assert NOT(forall ...) and check UNSAT
        let solver = Solver::new();
        solver.assert(&result.as_bool().not());
        assert_eq!(solver.check(), z3::SatResult::Unsat);
    }

    #[test]
    fn quantifier_exists_encoding() {
        let (vctx, pool) = empty_ctx();
        let ectx = EncodeCtx {
            vctx: &vctx,
            pool: &pool,
            entity_scope: None,
            bound_vars: HashMap::new(),
        };

        // exists x: Int | x == 42
        let expr = IRExpr::Exists {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 42 },
                }),
                ty: IRType::Bool,
            }),
        };
        let result = encode_expr(&ectx, &expr, 0);
        assert!(matches!(result, SmtValue::Bool(_)));

        // Check it's satisfiable
        let solver = Solver::new();
        solver.assert(result.as_bool());
        assert_eq!(solver.check(), z3::SatResult::Sat);
    }

    #[test]
    fn entity_pool_has_active_flags() {
        let entities = vec![IREntity {
            name: "Order".to_owned(),
            fields: vec![IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: None,
            }],
            transitions: vec![],
        }];
        let pool = create_entity_pool(&entities, 2);

        // Active flag should exist for each step
        assert!(pool.get_active("Order", 0).is_some());
        assert!(pool.get_active("Order", 1).is_some());
        assert!(pool.get_active("Order", 2).is_some());
        assert!(pool.get_active("Order", 3).is_none()); // out of bounds
        assert!(pool.get_active("Unknown", 0).is_none());
    }
}
