use super::super::smt::{self, AbideSolver, SatResult};
use super::*;
use crate::ir::types::{
    IRAction, IRAssumptionSet, IRCommand, IRCommandRef, IRField, IRFsm, IRFsmTransition, IRProgram,
    IRQuery, IRSystem, IRSystemAction, IRTransRef, IRUpdate, IRVariant, LitVal,
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
        actions: vec![IRSystemAction {
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
        actions: vec![IRSystemAction {
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

fn make_billing_query_program() -> (IRProgram, IRSystem) {
    let system = IRSystem {
        name: "Billing".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![IRQuery {
            name: "payable".to_owned(),
            params: vec![IRTransParam {
                name: "amount".to_owned(),
                ty: IRType::Int,
            }],
            body: IRExpr::BinOp {
                op: "OpGe".to_owned(),
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
        }],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let program = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system.clone()],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    (program, system)
}

fn assert_value_eq(actual: &SmtValue, expected: &SmtValue) {
    let solver = AbideSolver::new();
    solver.assert(&smt::smt_eq(actual, expected).expect("value equality"));
    assert_eq!(solver.check(), SatResult::Sat);
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
            actions: vec![
                IRSystemAction {
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
                IRSystemAction {
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
            actions: vec![
                IRSystemAction {
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
                IRSystemAction {
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
    let event = IRSystemAction {
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
    let tick = IRSystemAction {
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
        actions: vec![tick.clone()],
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

    let tick = IRSystemAction {
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
    let tick = IRSystemAction {
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

#[test]
fn try_eval_expr_with_vars_resolves_params_vars_and_qualified_fields() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let vars = HashMap::from([
        ("status".to_owned(), smt::int_val(5)),
        ("total".to_owned(), smt::int_val(9)),
    ]);
    let params = HashMap::from([
        ("limit".to_owned(), smt::int_val(7)),
        ("other.status".to_owned(), smt::int_val(11)),
    ]);

    let param_val = super::action::try_eval_expr_with_vars(
        &IRExpr::Var {
            name: "limit".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &params,
    )
    .expect("param value");
    assert_value_eq(&param_val, &smt::int_val(7));

    let var_val = super::action::try_eval_expr_with_vars(
        &IRExpr::Var {
            name: "total".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &params,
    )
    .expect("slot var value");
    assert_value_eq(&var_val, &smt::int_val(9));

    let qualified_field = super::action::try_eval_expr_with_vars(
        &IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "other".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "status".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &params,
    )
    .expect("qualified field");
    assert_value_eq(&qualified_field, &smt::int_val(11));
}

#[test]
fn try_eval_expr_with_vars_reports_missing_and_unsupported_inputs() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let vars = HashMap::new();
    let params = HashMap::new();

    let missing = super::action::try_eval_expr_with_vars(
        &IRExpr::Var {
            name: "missing".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &params,
    )
    .expect_err("missing var should fail");
    assert!(missing.contains("variable not found"));

    let unsupported = super::action::try_eval_expr_with_vars(
        &IRExpr::Exists {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &params,
    )
    .expect_err("unsupported expr should fail");
    assert!(unsupported.contains("unsupported expression"));
}

#[test]
fn try_build_apply_params_resolves_refs_from_params_and_pool_fields() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let scopes = HashMap::from([(entity.name.clone(), 1_usize)]);
    let pool = create_slot_pool(std::slice::from_ref(&entity), &scopes, 1);
    let entity_param_types = HashMap::new();
    let store_param_types = HashMap::new();
    let ctx = SlotEncodeCtx {
        pool: &pool,
        vctx: &vctx,
        entity: "Order",
        slot: 0,
        params: HashMap::from([("external".to_owned(), smt::int_val(41))]),
        bindings: HashMap::new(),
        system_name: "",
        entity_param_types: &entity_param_types,
        store_param_types: &store_param_types,
    };
    let action = IRTransition {
        name: "apply".to_owned(),
        refs: vec![
            IRTransRef {
                name: "from_param".to_owned(),
                entity: "Order".to_owned(),
            },
            IRTransRef {
                name: "from_slot".to_owned(),
                entity: "Order".to_owned(),
            },
        ],
        params: vec![IRTransParam {
            name: "amount".to_owned(),
            ty: IRType::Int,
        }],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        updates: vec![],
        postcondition: None,
    };

    let built = super::action::try_build_apply_params(
        &ctx,
        &action,
        &[IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 7 },
            span: None,
        }],
        &["external".to_owned(), "status".to_owned()],
        0,
    )
    .expect("build params");

    assert_value_eq(built.get("amount").expect("amount"), &smt::int_val(7));
    assert_value_eq(
        built.get("from_param").expect("param ref"),
        &smt::int_val(41),
    );
    let status_at_step = pool
        .field_at("Order", 0, "status", 0)
        .expect("status field")
        .clone();
    assert_value_eq(built.get("from_slot").expect("slot ref"), &status_at_step);
}

#[test]
fn fairness_tuple_enumeration_covers_entity_params_and_rejects_non_entity() {
    let entity = make_order_entity();
    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 2_usize)]),
        1,
    );
    let event = IRSystemAction {
        name: "tick".to_owned(),
        params: vec![
            IRTransParam {
                name: "lhs".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
            },
            IRTransParam {
                name: "rhs".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
            },
        ],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![],
        return_expr: None,
    };
    let tuples =
        super::fairness::enumerate_entity_param_tuples(&event, &pool).expect("entity tuples");
    assert_eq!(tuples.len(), 4);

    let mixed_event = IRSystemAction {
        params: vec![IRTransParam {
            name: "count".to_owned(),
            ty: IRType::Int,
        }],
        ..event
    };
    assert!(super::fairness::enumerate_entity_param_tuples(&mixed_event, &pool).is_none());
}

#[test]
fn fairness_constraints_expand_per_tuple_entity_events() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 2_usize)]),
        2,
    );
    let system = IRSystem {
        name: "Shop".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "tick".to_owned(),
            params: vec![IRTransParam {
                name: "o".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![],
            return_expr: None,
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let fire = FireTracking {
        fire_vars: HashMap::from([(
            ("Shop".to_owned(), "tick".to_owned()),
            vec![smt::bool_const(false), smt::bool_const(false)],
        )]),
        clause_fire_vars: HashMap::new(),
        stutter_vars: vec![],
        constraints: vec![],
    };
    let lasso = LassoLoop {
        loop_indicators: vec![smt::bool_const(true), smt::bool_const(true)],
        constraints: vec![],
    };
    let assumption_set = IRAssumptionSet {
        stutter: false,
        weak_fair: vec![IRCommandRef {
            system: "Shop".to_owned(),
            command: "tick".to_owned(),
        }],
        strong_fair: vec![],
        per_tuple: vec![IRCommandRef {
            system: "Shop".to_owned(),
            command: "tick".to_owned(),
        }],
    };

    let constraints = super::fairness::try_fairness_constraints(
        &pool,
        &vctx,
        std::slice::from_ref(&entity),
        std::slice::from_ref(&system),
        &fire,
        &lasso,
        &assumption_set,
    )
    .expect("fairness constraints");

    assert_eq!(constraints.len(), 4);
}

#[test]
fn guard_store_membership_and_store_quant_inference_cover_recursive_paths() {
    let entity = make_order_entity();
    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 2_usize)]),
        1,
    );
    let membership = super::guard::encode_store_membership(&pool, "Order", &smt::int_val(0), 0);
    let solver = AbideSolver::new();
    if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
        solver.assert(active);
    }
    solver.assert(&membership.to_bool().expect("membership bool"));
    assert_eq!(solver.check(), SatResult::Sat);

    let store_param_types = HashMap::from([("orders".to_owned(), "Order".to_owned())]);
    let body = IRExpr::BinOp {
        op: "OpAnd".to_owned(),
        left: Box::new(IRExpr::Index {
            map: Box::new(IRExpr::Var {
                name: "orders".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            key: Box::new(IRExpr::Var {
                name: "i".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        right: Box::new(IRExpr::UnOp {
            op: "OpNot".to_owned(),
            operand: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    assert_eq!(
        super::guard::infer_store_quant_entity("i", &body, &store_param_types),
        Some("Order".to_owned())
    );
}

#[test]
fn try_encode_create_applies_defaults_and_initial_constraints() {
    let entity = IREntity {
        name: "Ticket".to_owned(),
        fields: vec![
            IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 5 },
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "priority".to_owned(),
                ty: IRType::Int,
                default: None,
                initial_constraint: Some(IRExpr::BinOp {
                    op: "OpGt".to_owned(),
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
            },
        ],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let vctx = make_vctx();
    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 1_usize)]),
        1,
    );
    let create = super::action::try_encode_create(
        &pool,
        &vctx,
        "Ticket",
        Some(&entity),
        &[],
        0,
        &HashMap::new(),
    )
    .expect("create encoding");

    let solver = AbideSolver::new();
    solver.assert(&create);
    if let Some(status_next) = pool.field_at("Ticket", 0, "status", 1) {
        solver.assert(&smt::smt_eq(status_next, &smt::int_val(5)).expect("status eq"));
    }
    if let Some(priority_next) = pool.field_at("Ticket", 0, "priority", 1) {
        solver.assert(
            &smt::binop("OpGt", priority_next, &smt::int_val(0))
                .expect("priority gt")
                .to_bool()
                .expect("priority bool"),
        );
    }
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn try_encode_guard_expr_for_system_reads_system_fields_and_empty_quantifiers() {
    let system = make_system_with_int_fields();
    let pool =
        create_slot_pool_with_systems(&[], &HashMap::new(), 1, std::slice::from_ref(&system));
    let vctx = make_vctx();
    let guard = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "screen".to_owned(),
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
    let encoded = super::guard::try_encode_guard_expr_for_system(
        &pool,
        &vctx,
        &guard,
        &HashMap::new(),
        0,
        "Ui",
        &HashMap::new(),
        &HashMap::new(),
    )
    .expect("system guard");

    let solver = AbideSolver::new();
    solver.assert(&encoded);
    if let Some(screen) = pool.system_field_at("Ui", "screen", 0) {
        solver.assert(&smt::smt_eq(screen, &smt::int_val(1)).expect("screen eq"));
    }
    assert_eq!(solver.check(), SatResult::Sat);

    let entity = make_order_entity();
    let empty_pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 0_usize)]),
        1,
    );
    let exists = super::guard::try_encode_guard_expr(
        &empty_pool,
        &vctx,
        &IRExpr::Exists {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        },
        &HashMap::new(),
        &HashMap::new(),
        0,
    )
    .expect("empty exists");
    let forall = super::guard::try_encode_guard_expr(
        &empty_pool,
        &vctx,
        &IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        },
        &HashMap::new(),
        &HashMap::new(),
        0,
    )
    .expect("empty forall");
    let exists_solver = AbideSolver::new();
    exists_solver.assert(&exists);
    assert_eq!(exists_solver.check(), SatResult::Unsat);
    let forall_solver = AbideSolver::new();
    forall_solver.assert(&forall);
    assert_eq!(forall_solver.check(), SatResult::Sat);
}

#[test]
fn try_encode_slot_expr_supports_collections_bindings_and_store_quantifiers() {
    let entity = make_order_entity();
    let system = make_system_with_int_fields();
    let vctx = make_vctx();
    let pool = create_slot_pool_with_systems(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 2_usize)]),
        1,
        std::slice::from_ref(&system),
    );
    let entity_param_types = HashMap::new();
    let store_param_types = HashMap::from([("orders".to_owned(), "Order".to_owned())]);
    let ctx = SlotEncodeCtx {
        pool: &pool,
        vctx: &vctx,
        entity: "Order",
        slot: 0,
        params: HashMap::new(),
        bindings: HashMap::from([("other".to_owned(), ("Order".to_owned(), 1_usize))]),
        system_name: "Ui",
        entity_param_types: &entity_param_types,
        store_param_types: &store_param_types,
    };

    let bound_var = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Var {
            name: "other".to_owned(),
            ty: IRType::Identity,
            span: None,
        },
        0,
    )
    .expect("bound slot var");
    assert_value_eq(&bound_var, &smt::int_val(1));

    let system_field = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Var {
            name: "screen".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        0,
    )
    .expect("system field");
    let screen_at_0 = pool
        .system_field_at("Ui", "screen", 0)
        .expect("screen")
        .clone();
    assert_value_eq(&system_field, &screen_at_0);

    let seq_card = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Card {
            expr: Box::new(IRExpr::SeqLit {
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
            }),
            span: None,
        },
        0,
    )
    .expect("seq card");
    assert_value_eq(&seq_card, &smt::int_val(2));

    let set_card = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Card {
            expr: Box::new(IRExpr::SetLit {
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
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },
                        span: None,
                    },
                ],
                ty: IRType::Set {
                    element: Box::new(IRType::Int),
                },
                span: None,
            }),
            span: None,
        },
        0,
    )
    .expect("set card");
    assert_value_eq(&set_card, &smt::int_val(2));

    let map_card = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Card {
            expr: Box::new(IRExpr::MapLit {
                entries: vec![
                    (
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 7 },
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
                            ty: IRType::Int,
                            value: LitVal::Int { value: 9 },
                            span: None,
                        },
                    ),
                ],
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                span: None,
            }),
            span: None,
        },
        0,
    )
    .expect("map card");
    assert_value_eq(&map_card, &smt::int_val(1));

    let map_domain = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::UnOp {
            op: "OpMapDomain".to_owned(),
            operand: Box::new(IRExpr::MapLit {
                entries: vec![(
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    },
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 7 },
                        span: None,
                    },
                )],
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                span: None,
            }),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        },
        0,
    )
    .expect("map domain");
    assert!(matches!(map_domain, SmtValue::Array(_)));

    let exists = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Exists {
            var: "i".to_owned(),
            domain: IRType::Int,
            body: Box::new(IRExpr::Index {
                map: Box::new(IRExpr::Var {
                    name: "orders".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                key: Box::new(IRExpr::Var {
                    name: "i".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        },
        0,
    )
    .expect("exists membership");
    let exists_solver = AbideSolver::new();
    if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
        exists_solver.assert(active);
    }
    exists_solver.assert(&exists.to_bool().expect("exists bool"));
    assert_eq!(exists_solver.check(), SatResult::Sat);

    let forall = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Forall {
            var: "i".to_owned(),
            domain: IRType::Int,
            body: Box::new(IRExpr::Index {
                map: Box::new(IRExpr::Var {
                    name: "orders".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                key: Box::new(IRExpr::Var {
                    name: "i".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        },
        0,
    )
    .expect("forall membership");
    let forall_solver = AbideSolver::new();
    for slot in 0..2 {
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", slot, 0) {
            forall_solver.assert(active);
        }
    }
    forall_solver.assert(&forall.to_bool().expect("forall bool"));
    assert_eq!(forall_solver.check(), SatResult::Sat);

    assert_value_eq(
        &super::expr::encode_slot_literal(&LitVal::Real { value: 1.25 }),
        &smt::real_val(1_250_000, 1_000_000),
    );
}

#[test]
fn guard_helpers_cover_wrappers_unary_values_and_non_empty_forall() {
    let entity = make_order_entity();
    let system = make_system_with_int_fields();
    let vctx = make_vctx();
    let pool = create_slot_pool_with_systems(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 1_usize)]),
        1,
        std::slice::from_ref(&system),
    );
    let store_param_types = HashMap::from([("orders".to_owned(), "Order".to_owned())]);

    let membership_expr = IRExpr::UnOp {
        op: "OpNot".to_owned(),
        operand: Box::new(IRExpr::Index {
            map: Box::new(IRExpr::Var {
                name: "orders".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            key: Box::new(IRExpr::Var {
                name: "i".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    assert_eq!(
        super::guard::infer_store_quant_entity("i", &membership_expr, &store_param_types),
        Some("Order".to_owned())
    );

    let empty_membership =
        super::guard::encode_store_membership(&pool, "Missing", &smt::int_val(0), 0);
    assert_value_eq(&empty_membership, &smt::bool_val(false));

    let forall = IRExpr::Forall {
        var: "o".to_owned(),
        domain: IRType::Entity {
            name: "Order".to_owned(),
        },
        body: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        span: None,
    };
    let forall_guard =
        super::guard::encode_guard_expr(&pool, &vctx, &forall, &HashMap::new(), &HashMap::new(), 0);
    let forall_solver = AbideSolver::new();
    if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
        forall_solver.assert(active);
    }
    forall_solver.assert(&forall_guard);
    assert_eq!(forall_solver.check(), SatResult::Sat);

    let unary_value_guard = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::UnOp {
            op: "OpNeg".to_owned(),
            operand: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        }),
        right: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: -1 },
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let unary_guard = super::guard::try_encode_guard_expr(
        &pool,
        &vctx,
        &unary_value_guard,
        &HashMap::new(),
        &HashMap::new(),
        0,
    )
    .expect("unary value guard");
    let unary_solver = AbideSolver::new();
    unary_solver.assert(&unary_guard);
    assert_eq!(unary_solver.check(), SatResult::Sat);

    let system_guard = super::guard::encode_guard_expr_for_system(
        &pool,
        &vctx,
        &IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        &HashMap::new(),
        0,
        "Ui",
        &HashMap::new(),
        &HashMap::new(),
    );
    let system_solver = AbideSolver::new();
    system_solver.assert(&system_guard);
    assert_eq!(system_solver.check(), SatResult::Sat);
}

#[test]
fn try_encode_action_and_with_vars_enforce_fsm_tables() {
    let mut entity = make_order_entity();
    entity.fsm_decls = vec![IRFsm {
        field: "status".to_owned(),
        enum_name: "OrderStatus".to_owned(),
        transitions: vec![IRFsmTransition {
            from: "Pending".to_owned(),
            to: "Confirmed".to_owned(),
        }],
    }];
    let illegal = IRTransition {
        name: "skip_to_shipped".to_owned(),
        refs: vec![],
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        updates: vec![IRUpdate {
            field: "status".to_owned(),
            value: IRExpr::Ctor {
                enum_name: "OrderStatus".to_owned(),
                ctor: "Shipped".to_owned(),
                args: vec![],
                span: None,
            },
        }],
        postcondition: None,
    };
    let vctx = make_vctx();
    let pending = smt::int_val(vctx.variants.try_id_of("OrderStatus", "Pending").unwrap());
    let confirmed = smt::int_val(vctx.variants.try_id_of("OrderStatus", "Confirmed").unwrap());
    let shipped = smt::int_val(vctx.variants.try_id_of("OrderStatus", "Shipped").unwrap());

    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 1_usize)]),
        1,
    );
    let legal = super::action::try_encode_action(
        &pool,
        &vctx,
        &entity,
        &entity.transitions[0],
        0,
        0,
        &HashMap::new(),
    )
    .expect("legal action");
    let legal_solver = AbideSolver::new();
    if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
        legal_solver.assert(active);
    }
    if let Some(curr) = pool.field_at("Order", 0, "status", 0) {
        legal_solver.assert(&smt::smt_eq(curr, &pending).expect("pending"));
    }
    if let Some(next) = pool.field_at("Order", 0, "status", 1) {
        legal_solver.assert(&smt::smt_eq(next, &confirmed).expect("confirmed"));
    }
    legal_solver.assert(&legal);
    assert_eq!(legal_solver.check(), SatResult::Sat);

    let illegal_formula =
        super::action::try_encode_action(&pool, &vctx, &entity, &illegal, 0, 0, &HashMap::new())
            .expect("illegal action formula");
    let illegal_solver = AbideSolver::new();
    if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
        illegal_solver.assert(active);
    }
    if let Some(curr) = pool.field_at("Order", 0, "status", 0) {
        illegal_solver.assert(&smt::smt_eq(curr, &pending).expect("pending"));
    }
    if let Some(next) = pool.field_at("Order", 0, "status", 1) {
        illegal_solver.assert(&smt::smt_eq(next, &shipped).expect("shipped"));
    }
    illegal_solver.assert(&illegal_formula);
    assert_eq!(illegal_solver.check(), SatResult::Unsat);

    let read_vars = HashMap::from([
        ("id".to_owned(), smt::int_val(0)),
        ("status".to_owned(), pending.clone()),
        ("total".to_owned(), smt::int_val(0)),
    ]);
    let write_vars = HashMap::from([
        ("id".to_owned(), smt::int_val(0)),
        ("status".to_owned(), shipped),
        ("total".to_owned(), smt::int_val(0)),
    ]);
    let chained = super::action::try_encode_action_with_vars(
        &entity,
        &illegal,
        0,
        &read_vars,
        &write_vars,
        &vctx,
        &HashMap::new(),
    )
    .expect("chained action");
    let chained_solver = AbideSolver::new();
    chained_solver.assert(&chained);
    assert_eq!(chained_solver.check(), SatResult::Unsat);
}

#[test]
fn try_eval_expr_with_vars_supports_field_fallback_and_map_ops() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let int_sort = smt::ir_type_to_sort(&IRType::Int);
    let base = smt::const_array(&int_sort, &smt::int_val(0).to_dynamic());
    let vars = HashMap::from([
        ("total".to_owned(), smt::int_val(9)),
        ("items".to_owned(), SmtValue::Array(base)),
    ]);
    let params = HashMap::from([("status".to_owned(), smt::int_val(13))]);

    let same_entity_field = super::action::try_eval_expr_with_vars(
        &IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "self".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "total".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &HashMap::new(),
    )
    .expect("same-entity field");
    assert_value_eq(&same_entity_field, &smt::int_val(9));

    let unqualified_param_field = super::action::try_eval_expr_with_vars(
        &IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "self".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "status".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &HashMap::new(),
        &vctx,
        &params,
    )
    .expect("unqualified param field");
    assert_value_eq(&unqualified_param_field, &smt::int_val(13));

    let updated_lookup = super::action::try_eval_expr_with_vars(
        &IRExpr::Index {
            map: Box::new(IRExpr::MapUpdate {
                map: Box::new(IRExpr::Var {
                    name: "items".to_owned(),
                    ty: IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Int),
                    },
                    span: None,
                }),
                key: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },
                    span: None,
                }),
                value: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 17 },
                    span: None,
                }),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                span: None,
            }),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &HashMap::new(),
    )
    .expect("updated map lookup");
    assert_value_eq(&updated_lookup, &smt::int_val(17));

    let negated = super::action::try_eval_expr_with_vars(
        &IRExpr::UnOp {
            op: "OpNot".to_owned(),
            operand: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        },
        &entity,
        &vars,
        &vctx,
        &HashMap::new(),
    )
    .expect("negated bool");
    assert_value_eq(&negated, &smt::bool_val(false));
}

#[test]
fn try_encode_guard_expr_for_system_supports_entity_param_prime_and_logic() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 1_usize)]),
        1,
    );
    let params = HashMap::from([("order".to_owned(), smt::int_val(0))]);
    let entity_param_types = HashMap::from([("order".to_owned(), "Order".to_owned())]);
    let guard = IRExpr::BinOp {
        op: "OpAnd".to_owned(),
        left: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "order".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Enum {
                    name: "OrderStatus".to_owned(),
                    variants: vec![],
                },
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
        }),
        right: Box::new(IRExpr::BinOp {
            op: "OpImplies".to_owned(),
            left: Box::new(IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Prime {
                    expr: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "order".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
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
            ty: IRType::Bool,
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let encoded = super::guard::try_encode_guard_expr_for_system(
        &pool,
        &vctx,
        &guard,
        &params,
        0,
        "",
        &entity_param_types,
        &HashMap::new(),
    )
    .expect("entity-param guard");
    let pending = smt::int_val(vctx.variants.try_id_of("OrderStatus", "Pending").unwrap());
    let solver = AbideSolver::new();
    solver.assert(&encoded);
    if let Some(curr) = pool.field_at("Order", 0, "status", 0) {
        solver.assert(&smt::smt_eq(curr, &pending).expect("pending"));
    }
    if let Some(next) = pool.field_at("Order", 0, "total", 1) {
        solver.assert(
            &smt::binop("OpGe", next, &smt::int_val(0))
                .expect("ge")
                .to_bool()
                .unwrap(),
        );
    }
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn try_encode_slot_expr_supports_seq_map_ops_and_reports_type_errors() {
    let entity = make_order_entity();
    let vctx = make_vctx();
    let pool = create_slot_pool(
        std::slice::from_ref(&entity),
        &HashMap::from([(entity.name.clone(), 1_usize)]),
        1,
    );
    let entity_param_types = HashMap::new();
    let store_param_types = HashMap::new();
    let ctx = SlotEncodeCtx {
        pool: &pool,
        vctx: &vctx,
        entity: "Order",
        slot: 0,
        params: HashMap::new(),
        bindings: HashMap::new(),
        system_name: "",
        entity_param_types: &entity_param_types,
        store_param_types: &store_param_types,
    };

    let seq_ty = IRType::Seq {
        element: Box::new(IRType::Int),
    };
    let seq = IRExpr::SeqLit {
        elements: vec![
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 4 },
                span: None,
            },
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 5 },
                span: None,
            },
        ],
        ty: seq_ty.clone(),
        span: None,
    };
    let seq_head = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::UnOp {
            op: "OpSeqHead".to_owned(),
            operand: Box::new(seq.clone()),
            ty: IRType::Int,
            span: None,
        },
        0,
    )
    .expect("seq head");
    assert_value_eq(&seq_head, &smt::int_val(4));

    let seq_tail_first = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Index {
            map: Box::new(IRExpr::UnOp {
                op: "OpSeqTail".to_owned(),
                operand: Box::new(seq.clone()),
                ty: seq_ty.clone(),
                span: None,
            }),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        },
        0,
    )
    .expect("seq tail");
    assert_value_eq(&seq_tail_first, &smt::int_val(5));

    let concat_card = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::Card {
            expr: Box::new(IRExpr::BinOp {
                op: "OpSeqConcat".to_owned(),
                left: Box::new(seq.clone()),
                right: Box::new(IRExpr::SeqLit {
                    elements: vec![IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 6 },
                        span: None,
                    }],
                    ty: seq_ty.clone(),
                    span: None,
                }),
                ty: seq_ty.clone(),
                span: None,
            }),
            span: None,
        },
        0,
    )
    .expect("concat card");
    assert_value_eq(&concat_card, &smt::int_val(3));

    let seq_empty = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::UnOp {
            op: "OpSeqEmpty".to_owned(),
            operand: Box::new(seq.clone()),
            ty: IRType::Bool,
            span: None,
        },
        0,
    )
    .expect("seq empty");
    assert_value_eq(&seq_empty, &smt::bool_val(false));

    let map_ty = IRType::Map {
        key: Box::new(IRType::Int),
        value: Box::new(IRType::Int),
    };
    let map_expr = IRExpr::MapLit {
        entries: vec![(
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            },
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 7 },
                span: None,
            },
        )],
        ty: map_ty.clone(),
        span: None,
    };
    let has_value = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::BinOp {
            op: "OpMapHas".to_owned(),
            left: Box::new(map_expr.clone()),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        },
        0,
    )
    .expect("map has");
    assert_value_eq(&has_value, &smt::bool_val(true));

    let merged = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::BinOp {
            op: "OpMapMerge".to_owned(),
            left: Box::new(map_expr.clone()),
            right: Box::new(IRExpr::MapLit {
                entries: vec![(
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },
                        span: None,
                    },
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 9 },
                        span: None,
                    },
                )],
                ty: map_ty.clone(),
                span: None,
            }),
            ty: map_ty.clone(),
            span: None,
        },
        0,
    )
    .expect("map merge");
    assert!(matches!(merged, SmtValue::Array(_)));

    let map_range = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::UnOp {
            op: "OpMapRange".to_owned(),
            operand: Box::new(map_expr),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        },
        0,
    )
    .expect("map range");
    assert!(matches!(map_range, SmtValue::Array(_)));

    let bad_concat = super::expr::try_encode_slot_expr(
        &ctx,
        &IRExpr::BinOp {
            op: "OpSeqConcat".to_owned(),
            left: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        },
        0,
    )
    .expect_err("non-seq concat should fail");
    assert!(bad_concat.contains("Seq::concat requires sequence operands"));
}

#[test]
fn try_encode_slot_expr_and_guard_support_query_apps() {
    let (program, system) = make_billing_query_program();
    let vctx = VerifyContext::from_ir(&program);
    let pool =
        create_slot_pool_with_systems(&[], &HashMap::new(), 1, std::slice::from_ref(&system));
    let entity_param_types = HashMap::new();
    let store_param_types = HashMap::new();
    let ctx = SlotEncodeCtx {
        pool: &pool,
        vctx: &vctx,
        entity: "",
        slot: 0,
        params: HashMap::new(),
        bindings: HashMap::new(),
        system_name: "Billing",
        entity_param_types: &entity_param_types,
        store_param_types: &store_param_types,
    };
    let query_app = IRExpr::App {
        func: Box::new(IRExpr::Var {
            name: "payable".to_owned(),
            ty: IRType::Bool,
            span: None,
        }),
        arg: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };

    let query_value = super::expr::try_encode_slot_expr(&ctx, &query_app, 0).expect("query value");
    assert_value_eq(&query_value, &smt::bool_val(true));

    let query_guard = super::guard::try_encode_guard_expr_for_system(
        &pool,
        &vctx,
        &query_app,
        &HashMap::new(),
        0,
        "Billing",
        &HashMap::new(),
        &HashMap::new(),
    )
    .expect("query guard");
    let solver = AbideSolver::new();
    solver.assert(&query_guard);
    assert_eq!(solver.check(), SatResult::Sat);
}
