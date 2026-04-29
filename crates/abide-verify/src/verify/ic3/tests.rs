use super::*;
use crate::ir::types::*;
use crate::verify::context::VerifyContext;

const UNBOUNDED_PROOF_TEST_ENV: &str = "ABIDE_RUN_UNBOUNDED_PROOF_TESTS";

fn should_run_unbounded_proof_tests() -> bool {
    std::env::var_os(UNBOUNDED_PROOF_TEST_ENV).is_some()
}

fn skip_unbounded_proof_test() {
    eprintln!("skipping unbounded proof-backend test; set {UNBOUNDED_PROOF_TEST_ENV}=1 to opt in");
}

macro_rules! require_unbounded_proof_tests {
    () => {
        if !should_run_unbounded_proof_tests() {
            skip_unbounded_proof_test();
            return;
        }
    };
}

/// Test CHC solving through the routed CHC backend with declare-var style
/// variables. Validates the reference CHC API works with a simple
/// unreachable error.
#[test]
fn chc_backend_unreachable_via_string() {
    let chc = "(declare-rel Reach (Int))
             (declare-rel Error ())
             (declare-var x Int)
             (rule (Reach 0) base)
             (rule (=> (and (Reach x) (< x 10)) (Reach (+ x 1))) step)
             (rule (=> (and (Reach x) (< x 0)) Error) error)";

    let result = chc::check_chc(chc, "Error", 5000);

    assert!(
        matches!(result, ChcResult::Proved | ChcResult::Unknown(_)),
        "expected Proved or Unknown, got: {result:?}"
    );
}

fn make_simple_entity() -> (IREntity, Vec<IRTypeEntry>) {
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![
                IRVariant::simple("Pending"),
                IRVariant::simple("Confirmed"),
                IRVariant::simple("Shipped"),
            ],
        },
    };

    let entity = IREntity {
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
                    name: "Status".to_owned(),
                    variants: vec![
                        IRVariant::simple("Pending"),
                        IRVariant::simple("Confirmed"),
                        IRVariant::simple("Shipped"),
                    ],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "total".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![
            IRTransition {
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
                        enum_name: "Status".to_owned(),
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
                        enum_name: "Status".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            },
            IRTransition {
                name: "ship".to_owned(),
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
                        enum_name: "Status".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Shipped".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            },
        ],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    (entity, vec![status_type])
}

fn make_result_entity_with_payload() -> (IREntity, Vec<IRTypeEntry>) {
    let result_ty = IRTypeEntry {
        name: "Result".to_owned(),
        ty: IRType::Enum {
            name: "Result".to_owned(),
            variants: vec![
                IRVariant::simple("Pending"),
                IRVariant {
                    name: "Err".to_owned(),
                    fields: vec![IRVariantField {
                        name: "code".to_owned(),
                        ty: IRType::Int,
                    }],
                },
            ],
        },
    };

    let entity = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: result_ty.ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Result".to_owned(),
                ctor: "Err".to_owned(),
                args: vec![(
                    "code".to_owned(),
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 7 },
                        span: None,
                    },
                )],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    (entity, vec![result_ty])
}

fn make_result_entity_with_dual_payload_variants() -> (IREntity, Vec<IRTypeEntry>) {
    let result_ty = IRTypeEntry {
        name: "Result".to_owned(),
        ty: IRType::Enum {
            name: "Result".to_owned(),
            variants: vec![
                IRVariant {
                    name: "Ok".to_owned(),
                    fields: vec![IRVariantField {
                        name: "ok_code".to_owned(),
                        ty: IRType::Int,
                    }],
                },
                IRVariant {
                    name: "Err".to_owned(),
                    fields: vec![IRVariantField {
                        name: "err_code".to_owned(),
                        ty: IRType::Int,
                    }],
                },
            ],
        },
    };

    let entity = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: result_ty.ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Result".to_owned(),
                ctor: "Err".to_owned(),
                args: vec![(
                    "err_code".to_owned(),
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 7 },
                        span: None,
                    },
                )],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    (entity, vec![result_ty])
}

fn make_ir_for_entity(entity: &IREntity, types: Vec<IRTypeEntry>) -> IRProgram {
    IRProgram {
        types,
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn ic3_int_lit(value: i64) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Int,
        value: LitVal::Int { value },
        span: None,
    }
}

fn ic3_bool_lit(value: bool) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value },
        span: None,
    }
}

fn ic3_var(name: &str, ty: IRType) -> IRExpr {
    IRExpr::Var {
        name: name.to_owned(),
        ty,
        span: None,
    }
}

fn ic3_bin(op: &str, left: IRExpr, right: IRExpr, ty: IRType) -> IRExpr {
    IRExpr::BinOp {
        op: op.to_owned(),
        left: Box::new(left),
        right: Box::new(right),
        ty,
        span: None,
    }
}

fn ic3_field(base: &str, field: &str, base_ty: IRType, field_ty: IRType) -> IRExpr {
    IRExpr::Field {
        expr: Box::new(ic3_var(base, base_ty)),
        field: field.to_owned(),
        ty: field_ty,
        span: None,
    }
}

fn ic3_status_ctor(name: &str) -> IRExpr {
    IRExpr::Ctor {
        enum_name: "Status".to_owned(),
        ctor: name.to_owned(),
        args: vec![],
        span: None,
    }
}

#[test]
fn ic3_proves_valid_safety_property() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    // Property: status != -1 (always valid — status is always a valid enum)
    let property = IRExpr::BinOp {
        op: "OpNEq".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "status".to_owned(),
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

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved, got: {result:?}"
    );
}

#[test]
fn ic3_proves_field_access_property() {
    require_unbounded_proof_tests!();

    // Property: always all o: Order | o.total >= 0
    // total defaults to 0 and no transition modifies it.
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
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
                    field: "total".to_owned(),
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
        }),

        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for o.total >= 0, got: {result:?}"
    );
}

#[test]
fn ic3_detects_violation() {
    require_unbounded_proof_tests!();

    // Property: status == Pending always (false — confirm changes it)
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "status".to_owned(),
            ty: IRType::Int,

            span: None,
        }),
        right: Box::new(IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Pending".to_owned(),
            args: vec![],
            span: None,
        }),
        ty: IRType::Bool,

        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Violated(_)),
        "expected Violated (confirm breaks always-Pending), got: {result:?}"
    );
}

#[test]
fn ic3_violation_extracts_trace() {
    require_unbounded_proof_tests!();

    // Property: status == Pending always (false — confirm changes it)
    // IC3 should find the violation AND extract a trace showing the state change.
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "status".to_owned(),
            ty: IRType::Int,

            span: None,
        }),
        right: Box::new(IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Pending".to_owned(),
            args: vec![],
            span: None,
        }),
        ty: IRType::Bool,

        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    match result {
        Ic3Result::Violated(trace) => {
            assert!(
                trace.len() >= 2,
                "expected at least 2 trace steps, got {}",
                trace.len()
            );

            // Helper: find field value in a step
            let field_val = |step: usize, field: &str| -> String {
                trace[step]
                    .assignments
                    .iter()
                    .find(|(_, f, _)| f == field)
                    .unwrap_or_else(|| {
                        panic!("step {step} missing field {field}: {:?}", trace[step])
                    })
                    .2
                    .clone()
            };

            // Step 0: initial state after create — Pending, total=0
            assert_eq!(
                field_val(0, "status"),
                "0",
                "step 0: status should be Pending (0)"
            );
            assert_eq!(field_val(0, "total"), "0", "step 0: total should be 0");

            // Step 1: after confirm — Confirmed, total unchanged
            assert_eq!(
                field_val(1, "status"),
                "1",
                "step 1: status should be Confirmed (1)"
            );
            assert_eq!(
                field_val(1, "total"),
                "0",
                "step 1: total should still be 0"
            );

            // Entity labels should be "Order" (single slot)
            assert!(
                trace[0].assignments.iter().all(|(e, _, _)| e == "Order"),
                "all assignments should be for Order entity"
            );
        }
        other => panic!("expected Violated with trace, got: {other:?}"),
    }
}

// ── S-expression parser unit tests ─────────────────────────────

#[test]
fn sexpr_parser_handles_nested_negative() {
    // (State 0 (- 1) 0 true) should parse as 4 ground args
    let columns = vec![
        ("E".to_owned(), "a".to_owned(), 0),
        ("E".to_owned(), "b".to_owned(), 1),
        ("E".to_owned(), "c".to_owned(), 2),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(State 0 (- 1) 0 true)";
    let steps = parse_state_snapshots(answer, &columns);
    assert_eq!(steps.len(), 1, "expected 1 trace step");
    let a_val = steps[0].assignments.iter().find(|(_, f, _)| f == "b");
    assert_eq!(
        a_val.unwrap().2,
        "-1",
        "negative literal (- 1) should render as -1"
    );
}

#[test]
fn sexpr_parser_handles_rational_literal() {
    // (State (/ 3 2) true) should be recognized as ground and render as "3/2"
    let columns = vec![
        ("E".to_owned(), "val".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(State (/ 3 2) true)";
    let steps = parse_state_snapshots(answer, &columns);
    assert_eq!(steps.len(), 1, "expected 1 trace step for rational");
    assert_eq!(
        steps[0].assignments[0].2, "3/2",
        "rational (/ 3 2) should render as 3/2"
    );
}

#[test]
fn sexpr_parser_handles_negative_rational() {
    // (State (/ (- 1) 2) true) — negative rational
    let columns = vec![
        ("E".to_owned(), "val".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(State (/ (- 1) 2) true)";
    let steps = parse_state_snapshots(answer, &columns);
    assert_eq!(steps.len(), 1, "negative rational should be ground");
    assert_eq!(steps[0].assignments[0].2, "-1/2");
}

#[test]
fn sexpr_parser_rejects_trailing_garbage() {
    // Trailing tokens after the s-expression should cause parse failure → empty trace
    let columns = vec![
        ("E".to_owned(), "x".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(State 0 true) extra garbage";
    let steps = parse_state_snapshots(answer, &columns);
    assert!(steps.is_empty(), "trailing garbage should invalidate parse");
}

#[test]
fn sexpr_parser_rejects_unbalanced_parens() {
    let columns = vec![
        ("E".to_owned(), "x".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    // Missing closing paren
    let steps = parse_state_snapshots("(State 0 true", &columns);
    assert!(steps.is_empty(), "unclosed paren should invalidate parse");
    // Extra closing paren
    let steps = parse_state_snapshots("(State 0 true))", &columns);
    assert!(
        steps.is_empty(),
        "extra close paren should invalidate parse"
    );
}

#[test]
fn sexpr_parser_skips_non_ground_states() {
    // State applications with variable names (forall context) should be skipped
    let columns = vec![
        ("E".to_owned(), "x".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(and (State A true) (State 5 true))";
    let steps = parse_state_snapshots(answer, &columns);
    assert_eq!(steps.len(), 1, "only ground State should be extracted");
    assert_eq!(steps[0].assignments[0].2, "5");
}

#[test]
fn sexpr_parser_deduplicates_stutter() {
    // Consecutive identical states (from stutter rule) should be collapsed
    let columns = vec![
        ("E".to_owned(), "n".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(and (State 0 true) (State 0 true) (State 1 true))";
    let steps = parse_state_snapshots(answer, &columns);
    assert_eq!(steps.len(), 2, "stuttered duplicate should be removed");
    assert_eq!(steps[0].assignments[0].2, "0");
    assert_eq!(steps[1].assignments[0].2, "1");
}

#[test]
fn sexpr_parser_handles_derivation_tree() {
    // Realistic Spacer answer structure with nested hyper-res/mp
    let columns = vec![
        ("E".to_owned(), "x".to_owned(), 0),
        ("E".to_owned(), "active".to_owned(), usize::MAX),
    ];
    let answer = "(mp ((_ hyper-res 0 0 0 1) \
            (asserted (forall ((A Int)) (! (=> (State A true) query!0) :weight 0))) \
            ((_ hyper-res 0 0) (asserted (State 0 true)) (State 0 true)) \
            (State 1 true)) \
            (asserted (=> query!0 false)) false)";
    let steps = parse_state_snapshots(answer, &columns);
    // Should find: (State 0 true) and (State 1 true) — ground, in order
    assert!(steps.len() >= 2, "expected >= 2 steps, got {}", steps.len());
    assert_eq!(steps[0].assignments[0].2, "0");
    assert_eq!(steps[1].assignments[0].2, "1");
}

#[test]
fn ic3_supports_pure_let_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![LetBinding {
                name: "t".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "t".to_owned(),
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
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for let-bound IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
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
                        right: Box::new(IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_equality_conjunct() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
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
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for conjunctive int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_lower_bound_predicate() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpGt".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "n".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
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
                op: "OpGt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for lower-bound int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_multiple_upper_bounds() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let loose_upper = IRExpr::BinOp {
        op: "OpLt".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "n".to_owned(),
            ty: IRType::Int,
            span: None,
        }),
        right: Box::new(IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "total".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 10 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let tight_upper = IRExpr::BinOp {
        op: "OpLt".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "n".to_owned(),
            ty: IRType::Int,
            span: None,
        }),
        right: Box::new(IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "total".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(loose_upper),
                        right: Box::new(tight_upper),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpLt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for multi-upper-bound int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_disjunctive_bounds() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpOr".to_owned(),
                        left: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpGt".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
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
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for disjunctive int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_conditional_predicate() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::IfElse {
                        cond: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
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
                        then_body: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        else_body: Some(Box::new(IRExpr::BinOp {
                            op: "OpGt".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "n".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for conditional int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_let_in_predicate() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::Let {
                        bindings: vec![crate::ir::types::LetBinding {
                            name: "threshold".to_owned(),
                            ty: IRType::Int,
                            expr: IRExpr::Var {
                                name: "total".to_owned(),
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
                            right: Box::new(IRExpr::Var {
                                name: "threshold".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for let-in-predicate int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_payload_enum_choose_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_result_entity_with_payload();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: status_ty.clone(),
                expr: IRExpr::Choose {
                    var: "r".to_owned(),
                    domain: status_ty.clone(),
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "r".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: status_ty.clone(),
                    span: None,
                },
            }],
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Result::Err".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "code".to_owned(),
                                },
                            }],
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "code".to_owned(),
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
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for payload-enum choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_int_choose_with_match_scoped_predicate() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_result_entity_with_payload();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::Match {
                        scrutinee: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: status_ty,
                            span: None,
                        }),
                        arms: vec![
                            IRMatchArm {
                                pattern: IRPattern::PCtor {
                                    name: "Result::Err".to_owned(),
                                    fields: vec![IRFieldPat {
                                        name: "code".to_owned(),
                                        pattern: IRPattern::PVar {
                                            name: "code".to_owned(),
                                        },
                                    }],
                                },
                                guard: None,
                                body: IRExpr::BinOp {
                                    op: "OpEq".to_owned(),
                                    left: Box::new(IRExpr::Var {
                                        name: "n".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    right: Box::new(IRExpr::Var {
                                        name: "code".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    ty: IRType::Bool,
                                    span: None,
                                },
                            },
                            IRMatchArm {
                                pattern: IRPattern::PWild,
                                guard: None,
                                body: IRExpr::BinOp {
                                    op: "OpEq".to_owned(),
                                    left: Box::new(IRExpr::Var {
                                        name: "n".to_owned(),
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
                            },
                        ],
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
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
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for match-scoped int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_returns_unknown_for_nonlinear_nonconstructive_int_choose() {
    require_unbounded_proof_tests!();

    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "total".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "bump".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "total".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },
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
    };
    let ir = make_ir_for_entity(&entity, vec![]);
    let vctx = VerifyContext::from_ir(&ir);

    let square = |expr: IRExpr| IRExpr::BinOp {
        op: "OpMul".to_owned(),
        left: Box::new(expr.clone()),
        right: Box::new(expr),
        ty: IRType::Int,
        span: None,
    };
    let target = IRExpr::BinOp {
        op: "OpMul".to_owned(),
        left: Box::new(IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "total".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        }),
        right: Box::new(IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "total".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        }),
        ty: IRType::Int,
        span: None,
    };

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "n".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(square(IRExpr::Var {
                            name: "n".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        })),
                        right: Box::new(target.clone()),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: IRType::Int,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(square(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Int,
                    span: None,
                })),
                right: Box::new(target),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(_)),
        "expected Unknown for nonlinear existential int choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_payload_enum_choose_with_shape_predicate() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_result_entity_with_payload();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: status_ty.clone(),
                expr: IRExpr::Choose {
                    var: "r".to_owned(),
                    domain: status_ty.clone(),
                    predicate: Some(Box::new(IRExpr::Match {
                        scrutinee: Box::new(IRExpr::Var {
                            name: "r".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        arms: vec![
                            IRMatchArm {
                                pattern: IRPattern::PCtor {
                                    name: "Result::Err".to_owned(),
                                    fields: vec![IRFieldPat {
                                        name: "code".to_owned(),
                                        pattern: IRPattern::PVar {
                                            name: "code".to_owned(),
                                        },
                                    }],
                                },
                                guard: None,
                                body: IRExpr::BinOp {
                                    op: "OpGe".to_owned(),
                                    left: Box::new(IRExpr::Var {
                                        name: "code".to_owned(),
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
                            },
                            IRMatchArm {
                                pattern: IRPattern::PWild,
                                guard: None,
                                body: IRExpr::Lit {
                                    ty: IRType::Bool,
                                    value: LitVal::Bool { value: false },
                                    span: None,
                                },
                            },
                        ],
                        span: None,
                    })),
                    ty: status_ty.clone(),
                    span: None,
                },
            }],
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Result::Err".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "code".to_owned(),
                                },
                            }],
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "code".to_owned(),
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
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: false },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for payload-enum existential choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_real_choose_with_lower_bound_predicate() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Real,
                expr: IRExpr::Choose {
                    var: "r".to_owned(),
                    domain: IRType::Real,
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpGt".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "r".to_owned(),
                            ty: IRType::Real,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Real,
                            value: LitVal::Real { value: 0.0 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: IRType::Real,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpGt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: IRType::Real,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Real,
                    value: LitVal::Real { value: 0.0 },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for real lower-bound choose IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_bool_choose_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: IRType::Bool,
                expr: IRExpr::Choose {
                    var: "b".to_owned(),
                    domain: IRType::Bool,
                    predicate: Some(Box::new(IRExpr::Var {
                        name: "b".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: IRType::Bool,
                    span: None,
                },
            }],
            body: Box::new(IRExpr::Var {
                name: "picked".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for finite Bool choose in IC3, got: {result:?}"
    );
}

#[test]
fn ic3_supports_fieldless_enum_choose_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[1].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Let {
            bindings: vec![crate::ir::types::LetBinding {
                name: "picked".to_owned(),
                ty: status_ty.clone(),
                expr: IRExpr::Choose {
                    var: "s".to_owned(),
                    domain: status_ty.clone(),
                    predicate: Some(Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "s".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    })),
                    ty: status_ty.clone(),
                    span: None,
                },
            }],
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for finite enum choose in IC3, got: {result:?}"
    );
}

#[test]
fn ic3_supports_bool_exists_quantifier_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Exists {
            var: "b".to_owned(),
            domain: IRType::Bool,
            body: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for finite Bool exists in IC3, got: {result:?}"
    );
}

#[test]
fn ic3_supports_enum_forall_quantifier_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[1].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "s".to_owned(),
            domain: status_ty.clone(),
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "s".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "s".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for finite enum forall in IC3, got: {result:?}"
    );
}

#[test]
fn ic3_supports_one_and_lone_quantifier_expressions() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let one_property = IRExpr::Always {
        body: Box::new(IRExpr::One {
            var: "b".to_owned(),
            domain: IRType::Bool,
            body: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };
    let one_result = try_ic3_single_entity(&entity, &vctx, &one_property, 5000);
    assert!(
        matches!(one_result, Ic3Result::Proved),
        "expected Proved for finite Bool one in IC3, got: {one_result:?}"
    );

    let lone_property = IRExpr::Always {
        body: Box::new(IRExpr::Lone {
            var: "b".to_owned(),
            domain: IRType::Bool,
            body: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };
    let lone_result = try_ic3_single_entity(&entity, &vctx, &lone_property, 5000);
    assert!(
        matches!(lone_result, Ic3Result::Proved),
        "expected Proved for finite Bool lone in IC3, got: {lone_result:?}"
    );
}

#[test]
fn ic3_multi_slot_supports_entity_choose_with_field_access() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let entity_ty = IRType::Entity {
        name: entity.name.clone(),
    };
    let int_lit_zero = || IRExpr::Lit {
        ty: IRType::Int,
        value: LitVal::Int { value: 0 },
        span: None,
    };

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: entity_ty.clone(),
            body: Box::new(IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "picked".to_owned(),
                    ty: entity_ty.clone(),
                    expr: IRExpr::Choose {
                        var: "o".to_owned(),
                        domain: entity_ty.clone(),
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "o".to_owned(),
                                    ty: entity_ty.clone(),
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(int_lit_zero()),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: entity_ty.clone(),
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "picked".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(int_lit_zero()),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for entity choose with field access in multi-slot IC3, got: {result:?}"
    );
}

#[test]
fn ic3_multi_slot_supports_entity_choose_in_inter_entity_property() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let entity_ty = IRType::Entity {
        name: entity.name.clone(),
    };
    let int_lit_zero = || IRExpr::Lit {
        ty: IRType::Int,
        value: LitVal::Int { value: 0 },
        span: None,
    };

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: entity_ty.clone(),
            body: Box::new(IRExpr::Forall {
                var: "b".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::Let {
                    bindings: vec![crate::ir::types::LetBinding {
                        name: "picked".to_owned(),
                        ty: entity_ty.clone(),
                        expr: IRExpr::Choose {
                            var: "o".to_owned(),
                            domain: entity_ty.clone(),
                            predicate: Some(Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "o".to_owned(),
                                        ty: entity_ty.clone(),
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(int_lit_zero()),
                                ty: IRType::Bool,
                                span: None,
                            })),
                            ty: entity_ty.clone(),
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "picked".to_owned(),
                                ty: entity_ty.clone(),
                                span: None,
                            }),
                            field: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(int_lit_zero()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for inter-entity entity choose in multi-slot IC3, got: {result:?}"
    );
}

#[test]
fn ic3_supports_if_without_else_guard_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            then_body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "total".to_owned(),
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
            else_body: None,
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for guard if-without-else IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_match_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            arms: vec![
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PCtor {
                        name: "Pending".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "total".to_owned(),
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
                },
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                },
            ],
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for match-bound IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_match_destructuring_for_constructor_fields() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_result_entity_with_payload();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: status_ty,
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Result::Err".to_owned(),
                        fields: vec![IRFieldPat {
                            name: "code".to_owned(),
                            pattern: IRPattern::PVar {
                                name: "code".to_owned(),
                            },
                        }],
                    },
                    guard: None,
                    body: IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "code".to_owned(),
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
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                },
            ],
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for constructor-field match IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_supports_or_pattern_bindings_when_names_align() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_result_entity_with_dual_payload_variants();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: status_ty,
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::POr {
                        left: Box::new(IRPattern::PCtor {
                            name: "Result::Ok".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "ok_code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "code".to_owned(),
                                },
                            }],
                        }),
                        right: Box::new(IRPattern::PCtor {
                            name: "Result::Err".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "err_code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "code".to_owned(),
                                },
                            }],
                        }),
                    },
                    guard: None,
                    body: IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "code".to_owned(),
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
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                },
            ],
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for aligned or-pattern bindings in IC3, got: {result:?}"
    );
}

#[test]
fn ic3_rejects_or_pattern_bindings_with_mismatched_names() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_result_entity_with_dual_payload_variants();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let status_ty = entity.fields[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: status_ty,
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::POr {
                        left: Box::new(IRPattern::PCtor {
                            name: "Result::Ok".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "ok_code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "left_code".to_owned(),
                                },
                            }],
                        }),
                        right: Box::new(IRPattern::PCtor {
                            name: "Result::Err".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "err_code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "right_code".to_owned(),
                                },
                            }],
                        }),
                    },
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                },
            ],
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("or-pattern bindings in IC3 require both alternatives to bind the same names")),
        "expected Unknown with mismatched or-pattern binder message, got: {result:?}"
    );
}

#[test]
fn ic3_rejects_non_exhaustive_match_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            arms: vec![crate::ir::types::IRMatchArm {
                pattern: crate::ir::types::IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
            }],
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_single_entity(&entity, &vctx, &property, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("non-exhaustive match")),
        "expected Unknown with non-exhaustive match message, got: {result:?}"
    );
}

// ── Multi-slot tests ────────────────────────────────────────────

#[test]
fn ic3_multi_slot_proves_per_entity_property() {
    require_unbounded_proof_tests!();

    // Per-entity property with 2 slots — should still prove
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
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
                    field: "total".to_owned(),
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
        }),

        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for multi-slot per-entity property, got: {result:?}"
    );
}

#[test]
fn ic3_multi_slot_detects_violation() {
    require_unbounded_proof_tests!();

    // Property: all orders always Pending — should fail with 2 slots
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
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
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 2, 5000);
    assert!(
        matches!(result, Ic3Result::Violated(_)),
        "expected Violated for multi-slot always-Pending, got: {result:?}"
    );
}

#[test]
fn ic3_multi_slot_delegates_to_single_for_one_slot() {
    require_unbounded_proof_tests!();

    // With n_slots=1, should delegate to single-entity encoding
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::BinOp {
        op: "OpNEq".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "status".to_owned(),
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

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 1, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved with 1 slot, got: {result:?}"
    );
}

#[test]
fn ic3_multi_slot_inter_entity_property() {
    require_unbounded_proof_tests!();

    // Inter-entity property: all a: Order | all b: Order | a.total >= 0 and b.total >= 0
    // This is trivially true (total defaults to 0, no transition modifies it).
    // Tests the nested quantifier expansion path with 3 slots.
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Forall {
                var: "b".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "a".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },

                                span: None,
                            }),
                            field: "total".to_owned(),
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
                    right: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "b".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },

                                span: None,
                            }),
                            field: "total".to_owned(),
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
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 10000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for inter-entity total >= 0, got: {result:?}"
    );
}

#[test]
fn ic3_multi_slot_supports_inter_entity_let_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Forall {
                var: "b".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Let {
                    bindings: vec![
                        LetBinding {
                            name: "a_total".to_owned(),
                            ty: IRType::Int,
                            expr: IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "a".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            },
                        },
                        LetBinding {
                            name: "b_total".to_owned(),
                            ty: IRType::Int,
                            expr: IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "b".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            },
                        },
                    ],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "a_total".to_owned(),
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
                        right: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "b_total".to_owned(),
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
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for let-bound inter-entity property, got: {result:?}"
    );
}

#[test]
fn ic3_multi_slot_supports_inter_entity_if_expression() {
    require_unbounded_proof_tests!();

    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Forall {
                var: "b".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::IfElse {
                        cond: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "a".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
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
                        then_body: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "b".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                span: None,
                            }),
                            field: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        else_body: Some(Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        })),
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
            }),
            span: None,
        }),
        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 5000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for if/else inter-entity property, got: {result:?}"
    );
}

#[test]
fn ic3_rejects_bare_entity_var_in_inter_entity() {
    require_unbounded_proof_tests!();

    // Property: all a | all b | a == b — bare entity vars, should error
    let (entity, types) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, types);
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Forall {
                var: "b".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },

                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "b".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let result = try_ic3_multi_slot(&entity, &vctx, &property, 3, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("bare entity variable")),
        "expected Unknown with bare entity variable message, got: {result:?}"
    );
}

// ── Cross-system tests ──────────────────────────────────────────

#[test]
fn ic3_system_proves_multi_entity_safety() {
    require_unbounded_proof_tests!();

    // Two entity types: Order (status) and Item (quantity).
    // Property: all o: Order | o.total >= 0
    // No transitions modify total — should prove.
    let order_status = IRTypeEntry {
        name: "OrderStatus".to_owned(),
        ty: IRType::Enum {
            name: "OrderStatus".to_owned(),
            variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
        },
    };

    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![
            IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            },
            IRField {
                name: "total".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "OrderStatus".to_owned(),
                    variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "OrderStatus".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
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
    };

    let item = IREntity {
        name: "Item".to_owned(),
        fields: vec![
            IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            },
            IRField {
                name: "quantity".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let ir = IRProgram {
        types: vec![order_status],
        constants: vec![],
        functions: vec![],
        entities: vec![order, item],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
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
                    field: "total".to_owned(),
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
        }),

        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);
    slots.insert("Item".to_owned(), 1);

    let result = try_ic3_system(&ir, &vctx, &[], &property, &slots, 10000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for multi-entity total >= 0, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_let_bound_property() {
    require_unbounded_proof_tests!();

    let (ir, _) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "t".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "t".to_owned(),
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
            }),
            span: None,
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for let-bound system property, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_if_value_property() {
    require_unbounded_proof_tests!();

    let (ir, _) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::IfElse {
                    cond: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
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
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "Status".to_owned(),
                            ctor: "Pending".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    else_body: Some(Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 0 },
                        span: None,
                    })),
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
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for if/else system property, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_match_property() {
    require_unbounded_proof_tests!();

    let (ir, _) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Field {
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
                arms: vec![
                    crate::ir::types::IRMatchArm {
                        pattern: crate::ir::types::IRPattern::PCtor {
                            name: "Pending".to_owned(),
                            fields: vec![],
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "o".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
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
                    },
                    crate::ir::types::IRMatchArm {
                        pattern: crate::ir::types::IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for match system property, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_match_destructuring_for_constructor_fields() {
    require_unbounded_proof_tests!();

    let result_ty = IRTypeEntry {
        name: "Result".to_owned(),
        ty: IRType::Enum {
            name: "Result".to_owned(),
            variants: vec![
                IRVariant::simple("Pending"),
                IRVariant {
                    name: "Err".to_owned(),
                    fields: vec![IRVariantField {
                        name: "code".to_owned(),
                        ty: IRType::Int,
                    }],
                },
            ],
        },
    };

    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: result_ty.ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Result".to_owned(),
                ctor: "Err".to_owned(),
                args: vec![(
                    "code".to_owned(),
                    IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 7 },
                        span: None,
                    },
                )],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "Commerce".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };

    let ir = IRProgram {
        types: vec![result_ty],
        constants: vec![],
        functions: vec![],
        entities: vec![order],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "o".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: ir.types[0].ty.clone(),
                    span: None,
                }),
                arms: vec![
                    IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Err".to_owned(),
                            fields: vec![IRFieldPat {
                                name: "code".to_owned(),
                                pattern: IRPattern::PVar {
                                    name: "code".to_owned(),
                                },
                            }],
                        },
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "code".to_owned(),
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
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for constructor-field match system IC3 property, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_cross_entity_let_property() {
    require_unbounded_proof_tests!();

    let order_status = IRTypeEntry {
        name: "OrderStatus".to_owned(),
        ty: IRType::Enum {
            name: "OrderStatus".to_owned(),
            variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
        },
    };

    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![
            IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            },
            IRField {
                name: "total".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "status".to_owned(),
                ty: IRType::Enum {
                    name: "OrderStatus".to_owned(),
                    variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "OrderStatus".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let item = IREntity {
        name: "Item".to_owned(),
        fields: vec![
            IRField {
                name: "id".to_owned(),
                ty: IRType::Identity,
                default: None,
                initial_constraint: None,
            },
            IRField {
                name: "quantity".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let ir = IRProgram {
        types: vec![order_status],
        constants: vec![],
        functions: vec![],
        entities: vec![order, item],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Forall {
                var: "i".to_owned(),
                domain: IRType::Entity {
                    name: "Item".to_owned(),
                },
                body: Box::new(IRExpr::Let {
                    bindings: vec![
                        LetBinding {
                            name: "order_total".to_owned(),
                            ty: IRType::Int,
                            expr: IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "o".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            },
                        },
                        LetBinding {
                            name: "item_qty".to_owned(),
                            ty: IRType::Int,
                            expr: IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "i".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Item".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "quantity".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            },
                        },
                    ],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpAnd".to_owned(),
                        left: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "order_total".to_owned(),
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
                        right: Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "item_qty".to_owned(),
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
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);
    slots.insert("Item".to_owned(), 2);

    let result = try_ic3_system(&ir, &vctx, &[], &property, &slots, 10000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for let-bound cross-entity system property, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_entity_choose_with_field_access() {
    require_unbounded_proof_tests!();

    let (ir, _) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "picked".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    expr: IRExpr::Choose {
                        var: "c".to_owned(),
                        domain: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpGe".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "c".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Order".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "total".to_owned(),
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
                        })),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "picked".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "total".to_owned(),
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
            }),
            span: None,
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for entity-choose system property, got: {result:?}"
    );
}

#[test]
fn ic3_system_supports_cross_entity_choose_property() {
    require_unbounded_proof_tests!();

    let (ir, _) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Forall {
                var: "b".to_owned(),
                domain: IRType::Entity {
                    name: "Order".to_owned(),
                },
                body: Box::new(IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "picked".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        expr: IRExpr::Choose {
                            var: "c".to_owned(),
                            domain: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            predicate: Some(Box::new(IRExpr::BinOp {
                                op: "OpGe".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "c".to_owned(),
                                        ty: IRType::Entity {
                                            name: "Order".to_owned(),
                                        },
                                        span: None,
                                    }),
                                    field: "total".to_owned(),
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
                            })),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "picked".to_owned(),
                                ty: IRType::Entity {
                                    name: "Order".to_owned(),
                                },
                                span: None,
                            }),
                            field: "total".to_owned(),
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
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for cross-entity choose system property, got: {result:?}"
    );
}

// ── System event encoding tests ─────────────────────────────────

/// Helper: build an `IRProgram` with system events for testing system-level IC3.
fn make_system_program() -> (IRProgram, IRExpr) {
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![
                IRVariant::simple("Pending"),
                IRVariant::simple("Confirmed"),
                IRVariant::simple("Shipped"),
            ],
        },
    };

    let order = IREntity {
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
                    name: "Status".to_owned(),
                    variants: vec![
                        IRVariant::simple("Pending"),
                        IRVariant::simple("Confirmed"),
                        IRVariant::simple("Shipped"),
                    ],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "total".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![
            IRTransition {
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
                        enum_name: "Status".to_owned(),
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
                        enum_name: "Status".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            },
            IRTransition {
                name: "ship".to_owned(),
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
                        enum_name: "Status".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Shipped".to_owned(),
                        args: vec![],
                        span: None,
                    },
                }],
                postcondition: None,
            },
        ],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    // System with Choose+Apply event
    let commerce = IRSystem {
        name: "Commerce".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "process_order".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "o".to_owned(),
                entity: "Order".to_owned(),
                filter: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "o".to_owned(),
                    transition: "confirm".to_owned(),
                    refs: vec![],
                    args: vec![],
                }],
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
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![],
        entities: vec![order],
        systems: vec![commerce],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    // Property: all o: Order | o.total >= 0
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
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
                    field: "total".to_owned(),
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
        }),

        span: None,
    };

    (ir, property)
}

#[test]
fn ic3_system_with_events_proves_safety() {
    require_unbounded_proof_tests!();

    // Test system-level IC3 with actual system events (not empty systems vec).
    // Commerce system has Choose+Apply(confirm) for Orders.
    // Property: total >= 0 (no transition modifies total).
    let (ir, property) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        10000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved with system events, got: {result:?}"
    );
}

#[test]
fn ic3_system_missing_transition_returns_unknown() {
    require_unbounded_proof_tests!();

    // System event references a non-existent transition — should return Unknown.
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
        },
    };

    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
            },
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![], // no transitions defined
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let sys = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "do_thing".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "o".to_owned(),
                entity: "Order".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "o".to_owned(),
                    transition: "nonexistent".to_owned(), // missing!
                    refs: vec![],
                    args: vec![],
                }],
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
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![],
        entities: vec![order],
        systems: vec![sys],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value: true },

        span: None,
    };
    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 1);

    let result = try_ic3_system(&ir, &vctx, &["S".to_owned()], &property, &slots, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("transition nonexistent not found")),
        "expected Unknown with missing transition message, got: {result:?}"
    );
}

#[test]
fn ic3_system_missing_crosscall_target_returns_unknown() {
    require_unbounded_proof_tests!();

    // System event has CrossCall to non-existent system — should return Unknown.
    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "count".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let sys = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "trigger".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "NonExistent".to_owned(),
                command: "whatever".to_owned(),
                args: vec![],
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
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![order],
        systems: vec![sys],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value: true },

        span: None,
    };
    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 1);

    let result = try_ic3_system(&ir, &vctx, &["S".to_owned()], &property, &slots, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("CrossCall target system NonExistent not found")),
        "expected Unknown with missing CrossCall target, got: {result:?}"
    );
}

#[test]
fn ic3_system_crosscall_create_via_recursion() {
    require_unbounded_proof_tests!();

    // System A has CrossCall to System B which Creates an entity.
    // Tests recursive CrossCall encoding (not just Create scanning).
    let item = IREntity {
        name: "Item".to_owned(),
        fields: vec![IRField {
            name: "qty".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    // System B: event that Creates an Item
    let sys_b = IRSystem {
        name: "Inventory".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Item".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "add_item".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "Item".to_owned(),
                fields: vec![IRCreateField {
                    name: "qty".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 5 },

                        span: None,
                    },
                }],
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
    };

    // System A: event that CrossCalls B.add_item
    let sys_a = IRSystem {
        name: "Commerce".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "place_order".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "Inventory".to_owned(),
                command: "add_item".to_owned(),
                args: vec![],
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
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![item],
        systems: vec![sys_a, sys_b],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    // Property: all i: Item | i.qty >= 0 (Items are created with qty=5)
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "i".to_owned(),
            domain: IRType::Entity {
                name: "Item".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "i".to_owned(),
                        ty: IRType::Entity {
                            name: "Item".to_owned(),
                        },

                        span: None,
                    }),
                    field: "qty".to_owned(),
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
        }),

        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Item".to_owned(), 2);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        10000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for CrossCall-created items qty >= 0, got: {result:?}"
    );
}

#[test]
fn ic3_system_forall_with_apply() {
    require_unbounded_proof_tests!();

    // ForAll iterates all active orders and applies confirm.
    // With event-level encoding (no entity-level rules), transitions
    // are only accessible through system events.
    let (ir, property) = make_system_program();

    // Replace the system with one that uses ForAll instead of Choose
    let forall_sys = IRSystem {
        name: "BatchProcessor".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "confirm_all".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::ForAll {
                var: "o".to_owned(),
                entity: "Order".to_owned(),
                ops: vec![IRAction::Apply {
                    target: "o".to_owned(),
                    transition: "confirm".to_owned(),
                    refs: vec![],
                    args: vec![],
                }],
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
    };

    let ir2 = IRProgram {
        systems: vec![forall_sys],
        ..ir
    };
    let vctx = VerifyContext::from_ir(&ir2);

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir2,
        &vctx,
        &["BatchProcessor".to_owned()],
        &property,
        &slots,
        10000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for ForAll+Apply, got: {result:?}"
    );
}

#[test]
fn ic3_system_forall_with_create() {
    require_unbounded_proof_tests!();

    // ForAll iterates active orders and creates an Item for each.
    // Tests ForAll handling of Create ops (not just Apply).
    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "count".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let item = IREntity {
        name: "Item".to_owned(),
        fields: vec![IRField {
            name: "qty".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let sys = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned(), "Item".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_items".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::ForAll {
                var: "o".to_owned(),
                entity: "Order".to_owned(),
                ops: vec![IRAction::Create {
                    entity: "Item".to_owned(),
                    fields: vec![IRCreateField {
                        name: "qty".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 3 },

                            span: None,
                        },
                    }],
                }],
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
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![order, item],
        systems: vec![sys],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    // Property: all i: Item | i.qty >= 0 (Items created with qty=3)
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "i".to_owned(),
            domain: IRType::Entity {
                name: "Item".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "i".to_owned(),
                        ty: IRType::Entity {
                            name: "Item".to_owned(),
                        },

                        span: None,
                    }),
                    field: "qty".to_owned(),
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
        }),

        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 1);
    slots.insert("Item".to_owned(), 2);

    let result = try_ic3_system(&ir, &vctx, &["S".to_owned()], &property, &slots, 10000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved for ForAll+Create, got: {result:?}"
    );
}

#[test]
fn ic3_system_event_guard_propagation() {
    require_unbounded_proof_tests!();

    // Event guard is false → no transitions can fire → property trivially holds.
    // Verifies that event guard is properly AND'd into generated rules.
    let (ir, _) = make_system_program();

    // Replace system with event that has guard=false
    let guarded_sys = IRSystem {
        name: "Guarded".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "never_fires".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "o".to_owned(),
                entity: "Order".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "o".to_owned(),
                    transition: "confirm".to_owned(),
                    refs: vec![],
                    args: vec![],
                }],
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
    };

    let ir2 = IRProgram {
        systems: vec![guarded_sys],
        ..ir
    };
    let vctx = VerifyContext::from_ir(&ir2);

    // Property: all orders always Pending — true because no event can fire
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
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
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let result = try_ic3_system(
        &ir2,
        &vctx,
        &["Guarded".to_owned()],
        &property,
        &slots,
        10000,
    );
    // With event guard=false, no transitions fire, so always-Pending holds
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved (event guard=false prevents transitions), got: {result:?}"
    );
}

#[test]
fn ic3_system_no_entity_rules_when_systems_present() {
    require_unbounded_proof_tests!();

    // With systems present, entity-level transition rules are NOT emitted.
    // This means transitions can only fire through system events.
    // Test: property that would fail with entity-level rules but succeeds
    // when only system events are available and system has no ship event.
    let (ir, _) = make_system_program();

    // Commerce system only has process_order (which does confirm, not ship).
    // Without entity-level rules, ship can never fire.
    // Property: no order is ever Shipped — should be PROVED.
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpNEq".to_owned(),
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
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Shipped".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 2);

    let vctx = VerifyContext::from_ir(&ir);
    let result = try_ic3_system(
        &ir,
        &vctx,
        &["Commerce".to_owned()],
        &property,
        &slots,
        10000,
    );
    // Commerce only has confirm (Pending→Confirmed), no way to reach Shipped
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected Proved (ship not reachable via system events), got: {result:?}"
    );
}

#[test]
fn ic3_system_unknown_system_name_returns_unknown() {
    require_unbounded_proof_tests!();

    let (ir, property) = make_system_program();
    let vctx = VerifyContext::from_ir(&ir);
    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 1);

    let result = try_ic3_system(
        &ir,
        &vctx,
        &["DoesNotExist".to_owned()],
        &property,
        &slots,
        5000,
    );
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("system DoesNotExist not found")),
        "expected Unknown for missing system name, got: {result:?}"
    );
}

#[test]
fn ic3_system_cyclic_crosscall_returns_unknown() {
    require_unbounded_proof_tests!();

    // System A calls B, system B calls A — cyclic CrossCall.
    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "n".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let sys_a = IRSystem {
        name: "A".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "go".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "B".to_owned(),
                command: "bounce".to_owned(),
                args: vec![],
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
    };

    let sys_b = IRSystem {
        name: "B".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "bounce".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "A".to_owned(),
                command: "go".to_owned(),
                args: vec![],
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
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![order],
        systems: vec![sys_a, sys_b],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);

    let property = IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value: true },

        span: None,
    };
    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 1);

    let result = try_ic3_system(&ir, &vctx, &["A".to_owned()], &property, &slots, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("cyclic CrossCall")),
        "expected Unknown for cyclic CrossCall, got: {result:?}"
    );
}

#[test]
fn ic3_system_apply_target_mismatch_returns_unknown() {
    require_unbounded_proof_tests!();

    // Apply.target doesn't match Choose variable — malformed IR.
    let (ir, _) = make_system_program();

    let bad_sys = IRSystem {
        name: "Bad".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "bad_event".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "o".to_owned(),
                entity: "Order".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "wrong_var".to_owned(), // mismatch!
                    transition: "confirm".to_owned(),
                    refs: vec![],
                    args: vec![],
                }],
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
    };

    let ir2 = IRProgram {
        systems: vec![bad_sys],
        ..ir
    };
    let vctx = VerifyContext::from_ir(&ir2);

    let property = IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value: true },

        span: None,
    };
    let mut slots = HashMap::new();
    slots.insert("Order".to_owned(), 1);

    let result = try_ic3_system(&ir2, &vctx, &["Bad".to_owned()], &property, &slots, 5000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref reason)
                if reason.contains("Apply target wrong_var does not match")),
        "expected Unknown for Apply target mismatch, got: {result:?}"
    );
}

#[test]
fn collect_crosscall_targets_walks_nested_actions_without_duplication() {
    let mut targets = vec!["Billing".to_owned()];
    let actions = vec![
        IRAction::CrossCall {
            system: "Billing".to_owned(),
            command: "capture".to_owned(),
            args: vec![],
        },
        IRAction::Choose {
            var: "o".to_owned(),
            entity: "Order".to_owned(),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            ops: vec![IRAction::ForAll {
                var: "p".to_owned(),
                entity: "Payment".to_owned(),
                ops: vec![IRAction::CrossCall {
                    system: "Shipping".to_owned(),
                    command: "ship".to_owned(),
                    args: vec![],
                }],
            }],
        },
    ];

    collect_crosscall_targets(&actions, &mut targets);

    assert_eq!(targets, vec!["Billing".to_owned(), "Shipping".to_owned()]);
}

#[test]
fn build_liveness_chc_emits_monitor_columns_and_accepting_rule() {
    let (entity, tys) = make_simple_entity();
    let ir = IRProgram {
        types: tys,
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);
    let trigger = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "o".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![],
            },
            span: None,
        }),
        right: Box::new(IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Pending".to_owned(),
            args: vec![],
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let response = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "o".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![],
            },
            span: None,
        }),
        right: Box::new(IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Confirmed".to_owned(),
            args: vec![],
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let slots = HashMap::from([("Order".to_owned(), 1_usize)]);

    let chc = super::liveness::build_liveness_chc(
        &[&entity],
        &[],
        &vctx,
        &trigger,
        false,
        &response,
        Some("o"),
        Some("Order"),
        &[("Shop".to_owned(), "tick".to_owned())],
        &slots,
        Some(0),
    )
    .expect("liveness chc");

    assert!(chc.contains("mon_pending"));
    assert!(chc.contains("mon_saved_Order_0_f0"));
    assert!(chc.contains("mon_justice_0"));
    assert!(chc.contains("accepting"));
}

#[test]
fn try_ic3_liveness_reports_missing_quantified_entity() {
    require_unbounded_proof_tests!();

    let ir = IRProgram {
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
    };
    let vctx = VerifyContext::from_ir(&ir);
    let trigger = IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value: true },
        span: None,
    };
    let response = IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value: false },
        span: None,
    };

    let result = try_ic3_liveness(
        &ir,
        &vctx,
        &[],
        &trigger,
        &response,
        Some("o"),
        Some("Missing"),
        &[],
        &HashMap::new(),
        false,
        Some(0),
        10,
    );

    assert!(
        matches!(result, Ic3Result::Unknown(ref reason) if reason.contains("entity Missing not found")),
        "expected Unknown for missing quantified entity, got: {result:?}"
    );
}

#[test]
fn build_multi_slot_chc_and_system_chc_emit_expected_rules() {
    let (entity, tys) = make_simple_entity();
    let ir = IRProgram {
        types: tys.clone(),
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
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
        }),
        span: None,
    };

    let multi = build_multi_slot_chc(&entity, &vctx, &property, 2).expect("multi-slot chc");
    assert!(multi.contains("create_s0"));
    assert!(multi.contains("create_s1"));
    assert!(multi.contains("stutter"));

    let system_chc = build_system_chc(
        &[&entity],
        &[],
        &vctx,
        &property,
        &HashMap::from([("Order".to_owned(), 1_usize)]),
    )
    .expect("system chc");
    assert!(system_chc.contains("create_Order_0"));
    assert!(system_chc.contains("trans_Order_confirm_0"));
    assert!(system_chc.contains("domain_Order_0_1"));
}

#[test]
fn build_multi_slot_chc_supports_choose_let_and_match_rich_properties() {
    let (entity, tys) = make_simple_entity();
    let ir = IRProgram {
        types: tys.clone(),
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "chosen".to_owned(),
                    ty: status_ty.clone(),
                    expr: IRExpr::Choose {
                        var: "candidate".to_owned(),
                        domain: status_ty.clone(),
                        predicate: Some(Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "candidate".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::Ctor {
                                enum_name: "Status".to_owned(),
                                ctor: "Pending".to_owned(),
                                args: vec![],
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        })),
                        ty: status_ty.clone(),
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::Match {
                    scrutinee: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "o".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    arms: vec![
                        IRMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Pending".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "chosen".to_owned(),
                                    ty: status_ty.clone(),
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Ctor {
                                    enum_name: "Status".to_owned(),
                                    ctor: "Pending".to_owned(),
                                    args: vec![],
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            },
                        },
                        IRMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: true },
                                span: None,
                            },
                        },
                    ],
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };

    let chc = build_multi_slot_chc(&entity, &vctx, &property, 2).expect("rich multi-slot chc");
    assert!(chc.contains("s0_active"));
    assert!(chc.contains("Error"));
}

#[test]
fn build_system_chc_supports_entity_choose_scoped_properties() {
    let (entity, tys) = make_simple_entity();
    let status_ty = tys[0].ty.clone();
    let system = IRSystem {
        name: "Shop".to_owned(),
        store_params: vec![IRStoreParam {
            name: "orders".to_owned(),
            entity_type: "Order".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let ir = IRProgram {
        types: tys.clone(),
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![system.clone()],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "o".to_owned(),
            domain: IRType::Entity {
                name: "Order".to_owned(),
            },
            body: Box::new(IRExpr::Let {
                bindings: vec![LetBinding {
                    name: "selected".to_owned(),
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
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::Ctor {
                                enum_name: "Status".to_owned(),
                                ctor: "Pending".to_owned(),
                                args: vec![],
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
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "selected".to_owned(),
                            ty: IRType::Entity {
                                name: "Order".to_owned(),
                            },
                            span: None,
                        }),
                        field: "total".to_owned(),
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
            }),
            span: None,
        }),
        span: None,
    };

    let chc = build_system_chc(
        &[&entity],
        &[&system],
        &vctx,
        &property,
        &HashMap::from([("Order".to_owned(), 2_usize)]),
    )
    .expect("rich system chc");
    assert!(chc.contains("Order_0_active"));
    assert!(chc.contains("Order_1_active"));
    assert!(chc.contains("Error"));
}

#[test]
fn build_liveness_chc_supports_choose_and_crosscall_event_paths() {
    let (entity, tys) = make_simple_entity();
    let helper = IRSystem {
        name: "Decision".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "decide".to_owned(),
            params: vec![],
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
    let shop = IRSystem {
        name: "Shop".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "tick".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![
                IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "confirm".to_owned(),
                        args: vec![],
                        refs: vec![],
                    }],
                },
                IRAction::CrossCall {
                    system: "Decision".to_owned(),
                    command: "decide".to_owned(),
                    args: vec![],
                },
            ],
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
    let ir = IRProgram {
        types: tys.clone(),
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![shop.clone(), helper.clone()],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);
    let trigger = IRExpr::BinOp {
        op: "OpGe".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "o".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "total".to_owned(),
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
    };
    let response = IRExpr::BinOp {
        op: "OpGe".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "o".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "total".to_owned(),
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
    };

    let chc = super::liveness::build_liveness_chc(
        &[&entity],
        &[&shop, &helper],
        &vctx,
        &trigger,
        false,
        &response,
        Some("o"),
        Some("Order"),
        &[("Shop".to_owned(), "tick".to_owned())],
        &HashMap::from([("Order".to_owned(), 1_usize)]),
        Some(0),
    )
    .expect("liveness choose/crosscall chc");
    assert!(chc.contains("tick_choose_0_s0"));
    assert!(chc.contains("accepting"));
}

#[test]
fn system_scope_translators_cover_scoped_value_guard_and_cross_entity_paths() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();

    let value_expr = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "picked".to_owned(),
            ty: status_ty.clone(),
            expr: IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            },
        }],
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "self".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    span: None,
                }),
                field: "status".to_owned(),
                ty: status_ty.clone(),
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Pending".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    },
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                },
            ],
            span: None,
        }),
        span: None,
    };
    let value_smt =
        expr_to_smt_sys_scoped(&value_expr, &entity, &vctx, "Order", 0, &HashSet::new())
            .expect("system value");
    assert!(value_smt.contains("(let ((picked"));
    assert!(value_smt.contains("(ite "));
    assert!(value_smt.contains("Order_0_f1"));

    let guard_expr = IRExpr::IfElse {
        cond: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "self".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    span: None,
                }),
                field: "status".to_owned(),
                ty: status_ty.clone(),
                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        then_body: Box::new(IRExpr::Forall {
            var: "candidate".to_owned(),
            domain: status_ty.clone(),
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "candidate".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "candidate".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        else_body: Some(Box::new(IRExpr::Exists {
            var: "candidate".to_owned(),
            domain: status_ty.clone(),
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "candidate".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        })),
        span: None,
    };
    let guard_smt =
        guard_to_smt_sys_scoped(&guard_expr, &entity, &vctx, "Order", 0, &HashSet::new())
            .expect("system guard");
    assert!(guard_smt.contains("(ite "));
    assert!(!guard_smt.is_empty());

    let cross_expr = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "picked".to_owned(),
            ty: status_ty.clone(),
            expr: IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                predicate: Some(Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "candidate".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                })),
                ty: status_ty.clone(),
                span: None,
            },
        }],
        body: Box::new(IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "lhs".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "rhs".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "total".to_owned(),
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
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    };
    let cross_smt = guard_to_smt_sys_two_scoped(
        &cross_expr,
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
        &HashSet::new(),
    )
    .expect("cross guard");
    assert!(cross_smt.contains("Order_0_f1"));
    assert!(cross_smt.contains("Order_1_f2"));
    assert!(cross_smt.contains("(let ((picked"));
}

#[test]
fn system_expr_translators_cover_branchy_forms_and_errors() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let entity_ty = IRType::Entity {
        name: "Order".to_owned(),
    };
    let map_ty = IRType::Map {
        key: Box::new(IRType::Int),
        value: Box::new(IRType::Int),
    };

    let value = IRExpr::Let {
        bindings: vec![
            LetBinding {
                name: "ok".to_owned(),
                ty: IRType::Bool,
                expr: ic3_bin("OpLe", ic3_int_lit(1), ic3_int_lit(2), IRType::Bool),
            },
            LetBinding {
                name: "mapped".to_owned(),
                ty: map_ty.clone(),
                expr: IRExpr::MapUpdate {
                    map: Box::new(ic3_var("m", map_ty.clone())),
                    key: Box::new(ic3_int_lit(1)),
                    value: Box::new(ic3_bin(
                        "OpMul",
                        ic3_field("self", "total", entity_ty.clone(), IRType::Int),
                        ic3_int_lit(2),
                        IRType::Int,
                    )),
                    ty: map_ty.clone(),
                    span: None,
                },
            },
        ],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(ic3_var("ok", IRType::Bool)),
            then_body: Box::new(IRExpr::Index {
                map: Box::new(ic3_var("mapped", map_ty.clone())),
                key: Box::new(ic3_int_lit(1)),
                ty: IRType::Int,
                span: None,
            }),
            else_body: Some(Box::new(ic3_bin(
                "OpSub",
                ic3_field("self", "total", entity_ty.clone(), IRType::Int),
                ic3_int_lit(1),
                IRType::Int,
            ))),
            span: None,
        }),
        span: None,
    };
    let value_smt = expr_to_smt_sys_scoped(
        &value,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::from(["m".to_owned()]),
    )
    .expect("system branchy value");
    assert!(value_smt.contains("(store m 1 (* Order_0_f2 2))"));
    assert!(value_smt.contains("(select mapped 1)"));

    let guard = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "picked".to_owned(),
            ty: status_ty.clone(),
            expr: IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                predicate: Some(Box::new(ic3_bin(
                    "OpNEq",
                    ic3_var("candidate", status_ty.clone()),
                    ic3_status_ctor("Shipped"),
                    IRType::Bool,
                ))),
                ty: status_ty.clone(),
                span: None,
            },
        }],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(ic3_bool_lit(false)),
                ty: IRType::Bool,
                span: None,
            }),
            then_body: Box::new(ic3_bin(
                "OpOr",
                ic3_bin(
                    "OpEq",
                    ic3_field("self", "status", entity_ty.clone(), status_ty.clone()),
                    ic3_var("picked", status_ty.clone()),
                    IRType::Bool,
                ),
                IRExpr::One {
                    var: "flag".to_owned(),
                    domain: IRType::Bool,
                    body: Box::new(ic3_var("flag", IRType::Bool)),
                    span: None,
                },
                IRType::Bool,
            )),
            else_body: None,
            span: None,
        }),
        span: None,
    };
    let guard_smt =
        guard_to_smt_sys(&guard, &entity, &vctx, "Order", 0).expect("system branchy guard");
    assert!(guard_smt.contains("(let ((picked"));
    assert!(guard_smt.contains("(=> (not false)"));

    let guard_match = IRExpr::Match {
        scrutinee: Box::new(ic3_field(
            "self",
            "status",
            entity_ty.clone(),
            status_ty.clone(),
        )),
        arms: vec![
            IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: Some(ic3_bool_lit(true)),
                body: ic3_bool_lit(true),
            },
            IRMatchArm {
                pattern: IRPattern::PWild,
                guard: None,
                body: ic3_bool_lit(false),
            },
        ],
        span: None,
    };
    let match_smt =
        guard_to_smt_sys(&guard_match, &entity, &vctx, "Order", 0).expect("system match guard");
    assert!(match_smt.contains("(ite "));
    assert!(match_smt.contains("Order_0_f1"));

    let cross = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "threshold".to_owned(),
            ty: IRType::Int,
            expr: ic3_int_lit(3),
        }],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(ic3_bin(
                "OpAnd",
                ic3_bin(
                    "OpEq",
                    ic3_field("lhs", "status", entity_ty.clone(), status_ty.clone()),
                    ic3_status_ctor("Pending"),
                    IRType::Bool,
                ),
                ic3_bin(
                    "OpGt",
                    ic3_field("rhs", "total", entity_ty.clone(), IRType::Int),
                    ic3_var("threshold", IRType::Int),
                    IRType::Bool,
                ),
                IRType::Bool,
            )),
            then_body: Box::new(IRExpr::Forall {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                body: Box::new(ic3_bin(
                    "OpEq",
                    ic3_var("candidate", status_ty.clone()),
                    ic3_var("candidate", status_ty.clone()),
                    IRType::Bool,
                )),
                span: None,
            }),
            else_body: Some(Box::new(IRExpr::Exists {
                var: "flag".to_owned(),
                domain: IRType::Bool,
                body: Box::new(ic3_var("flag", IRType::Bool)),
                span: None,
            })),
            span: None,
        }),
        span: None,
    };
    let cross_smt = guard_to_smt_sys_two(
        &cross, &entity, &entity, &vctx, "Order", 0, "lhs", "Order", 1, "rhs",
    )
    .expect("system cross branchy guard");
    assert!(cross_smt.contains("(let ((threshold 3))"));
    assert!(cross_smt.contains("Order_0_f1"));
    assert!(cross_smt.contains("Order_1_f2"));

    let cross_match = IRExpr::Match {
        scrutinee: Box::new(ic3_field(
            "lhs",
            "status",
            entity_ty.clone(),
            status_ty.clone(),
        )),
        arms: vec![
            IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: Some(ic3_bin(
                    "OpGe",
                    ic3_field("rhs", "total", entity_ty.clone(), IRType::Int),
                    ic3_int_lit(0),
                    IRType::Bool,
                )),
                body: ic3_bool_lit(true),
            },
            IRMatchArm {
                pattern: IRPattern::PWild,
                guard: None,
                body: ic3_bool_lit(false),
            },
        ],
        span: None,
    };
    let cross_match_smt = guard_to_smt_sys_two(
        &cross_match,
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
    )
    .expect("system cross match");
    assert!(cross_match_smt.contains("(ite "));

    assert!(expr_to_smt_sys(
        &IRExpr::IfElse {
            cond: Box::new(ic3_bool_lit(true)),
            then_body: Box::new(ic3_int_lit(1)),
            else_body: None,
            span: None,
        },
        &entity,
        &vctx,
        "Order",
        0,
    )
    .expect_err("system value if requires else")
    .contains("without else"));
    assert!(
        expr_to_smt_sys(&ic3_var("missing", IRType::Int), &entity, &vctx, "Order", 0)
            .expect_err("missing system var")
            .contains("unknown variable")
    );
    assert!(guard_to_smt_sys(
        &ic3_bin("OpDiv", ic3_int_lit(4), ic3_int_lit(2), IRType::Bool),
        &entity,
        &vctx,
        "Order",
        0,
    )
    .expect_err("unsupported system guard op")
    .contains("unsupported op"));
    assert!(guard_to_smt_sys_two(
        &IRExpr::Field {
            expr: Box::new(ic3_var("local", IRType::Int)),
            field: "total".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
    )
    .expect_err("unknown cross field var")
    .contains("unknown var"));
    assert!(guard_to_smt_sys_two(
        &ic3_var("lhs", entity_ty),
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
    )
    .expect_err("bare cross entity var")
    .contains("bare entity variable"));
}

#[test]
fn system_expr_translators_cover_remaining_let_quantifier_and_error_paths() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let entity_ty = IRType::Entity {
        name: "Order".to_owned(),
    };

    let plain_let = guard_let_to_smt_sys_scoped(
        &[
            LetBinding {
                name: "limit".to_owned(),
                ty: IRType::Int,
                expr: ic3_bin(
                    "OpAdd",
                    ic3_field("self", "total", entity_ty.clone(), IRType::Int),
                    ic3_int_lit(1),
                    IRType::Int,
                ),
            },
            LetBinding {
                name: "ok".to_owned(),
                ty: IRType::Bool,
                expr: ic3_bin(
                    "OpGe",
                    ic3_var("limit", IRType::Int),
                    ic3_int_lit(0),
                    IRType::Bool,
                ),
            },
        ],
        &IRExpr::Assume {
            expr: Box::new(ic3_bin(
                "OpImplies",
                ic3_var("ok", IRType::Bool),
                IRExpr::Lone {
                    var: "candidate".to_owned(),
                    domain: status_ty.clone(),
                    body: Box::new(ic3_bin(
                        "OpNEq",
                        ic3_var("candidate", status_ty.clone()),
                        ic3_status_ctor("Shipped"),
                        IRType::Bool,
                    )),
                    span: None,
                },
                IRType::Bool,
            )),
            span: None,
        },
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
    )
    .expect("plain system let");
    assert!(plain_let.contains("(let ((limit (+ Order_0_f2 1))"));
    assert!(plain_let.contains("(=> ok"));

    assert!(guard_let_to_smt_sys_scoped(
        &[LetBinding {
            name: "picked".to_owned(),
            ty: entity_ty.clone(),
            expr: IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: entity_ty.clone(),
                predicate: None,
                ty: entity_ty.clone(),
                span: None,
            },
        }],
        &ic3_bool_lit(true),
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
    )
    .expect_err("entity choose unsupported in system guard let")
    .contains("choose is not yet supported"));

    assert!(expr_to_smt_sys(
        &IRExpr::Match {
            scrutinee: Box::new(ic3_status_ctor("Pending")),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: ic3_int_lit(1),
            }],
            span: None,
        },
        &entity,
        &vctx,
        "Order",
        0,
    )
    .expect_err("non-exhaustive system value match")
    .contains("non-exhaustive"));
    assert!(expr_to_smt_sys(
        &IRExpr::Card {
            expr: Box::new(ic3_var(
                "values",
                IRType::Set {
                    element: Box::new(IRType::Int),
                },
            )),
            span: None,
        },
        &entity,
        &vctx,
        "Order",
        0,
    )
    .expect_err("system value unsupported shape")
    .contains("unsupported expression"));
    assert!(guard_to_smt_sys(
        &IRExpr::Match {
            scrutinee: Box::new(ic3_status_ctor("Pending")),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: ic3_bool_lit(true),
            }],
            span: None,
        },
        &entity,
        &vctx,
        "Order",
        0,
    )
    .expect_err("non-exhaustive system guard match")
    .contains("non-exhaustive"));

    let cross_choose = guard_let_to_smt_sys_two_scoped(
        &[LetBinding {
            name: "witness".to_owned(),
            ty: IRType::Int,
            expr: IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: IRType::Int,
                predicate: Some(Box::new(ic3_bin(
                    "OpGt",
                    ic3_var("candidate", IRType::Int),
                    ic3_int_lit(2),
                    IRType::Bool,
                ))),
                ty: IRType::Int,
                span: None,
            },
        }],
        &ic3_bin(
            "OpGt",
            ic3_var("witness", IRType::Int),
            ic3_int_lit(2),
            IRType::Bool,
        ),
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
        &HashSet::new(),
    )
    .expect("cross quantified choose");
    assert!(cross_choose.contains("(let ((witness"));

    let cross_more = IRExpr::Assume {
        expr: Box::new(ic3_bin(
            "OpOr",
            IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(ic3_bool_lit(false)),
                ty: IRType::Bool,
                span: None,
            },
            IRExpr::One {
                var: "flag".to_owned(),
                domain: IRType::Bool,
                body: Box::new(ic3_var("flag", IRType::Bool)),
                span: None,
            },
            IRType::Bool,
        )),
        span: None,
    };
    let cross_more_smt = guard_to_smt_sys_two(
        &cross_more,
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
    )
    .expect("cross assert/unary/one");
    assert!(cross_more_smt.contains("(or (not false)"));

    assert!(guard_to_smt_sys_two_scoped(
        &IRExpr::Field {
            expr: Box::new(ic3_var("local", IRType::Int)),
            field: "total".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
        &HashSet::from(["local".to_owned()]),
    )
    .expect_err("cross local field projection")
    .contains("cannot be used for field projection"));
    assert!(guard_to_smt_sys_two(
        &IRExpr::Match {
            scrutinee: Box::new(ic3_status_ctor("Pending")),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: ic3_bool_lit(true),
            }],
            span: None,
        },
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
    )
    .expect_err("non-exhaustive cross match")
    .contains("non-exhaustive"));
}

#[test]
fn system_property_translators_cover_nested_quantifiers_bindings_and_errors() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let entity_ty = IRType::Entity {
        name: "Order".to_owned(),
    };
    let entities = vec![&entity];
    let slots = HashMap::from([("Order".to_owned(), 2_usize)]);

    let nested = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "lhs".to_owned(),
            domain: entity_ty.clone(),
            body: Box::new(IRExpr::Forall {
                var: "rhs".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(ic3_bin(
                    "OpGe",
                    ic3_bin(
                        "OpAdd",
                        ic3_field("lhs", "total", entity_ty.clone(), IRType::Int),
                        ic3_field("rhs", "total", entity_ty.clone(), IRType::Int),
                        IRType::Int,
                    ),
                    ic3_int_lit(0),
                    IRType::Bool,
                )),
                span: None,
            }),
            span: None,
        }),
        span: None,
    };
    let negated =
        negate_property_smt_system(&nested, &entities, &vctx, &slots).expect("nested system prop");
    assert!(negated.contains("Order_0_active Order_1_active"));
    assert!(negated.contains("(not (>= (+ Order_0_f2 Order_1_f2) 0))"));

    assert!(negate_property_smt_system(
        &IRExpr::Forall {
            var: "missing".to_owned(),
            domain: IRType::Entity {
                name: "Missing".to_owned(),
            },
            body: Box::new(ic3_bool_lit(true)),
            span: None,
        },
        &entities,
        &vctx,
        &slots,
    )
    .expect_err("missing entity rejected")
    .contains("not found"));

    let mut entity_locals = Ic3SystemEntityLocals::new();
    entity_locals.insert("bound".to_owned(), ("Order".to_owned(), 1));
    let property_let = IRExpr::Let {
        bindings: vec![
            LetBinding {
                name: "alias".to_owned(),
                ty: entity_ty.clone(),
                expr: ic3_var("bound", entity_ty.clone()),
            },
            LetBinding {
                name: "picked".to_owned(),
                ty: entity_ty.clone(),
                expr: IRExpr::Choose {
                    var: "candidate".to_owned(),
                    domain: entity_ty.clone(),
                    predicate: Some(Box::new(ic3_bin(
                        "OpGe",
                        ic3_field("candidate", "total", entity_ty.clone(), IRType::Int),
                        ic3_int_lit(0),
                        IRType::Bool,
                    ))),
                    ty: entity_ty.clone(),
                    span: None,
                },
            },
            LetBinding {
                name: "threshold".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::Choose {
                    var: "candidate".to_owned(),
                    domain: IRType::Int,
                    predicate: Some(Box::new(ic3_bin(
                        "OpGt",
                        ic3_var("candidate", IRType::Int),
                        ic3_int_lit(1),
                        IRType::Bool,
                    ))),
                    ty: IRType::Int,
                    span: None,
                },
            },
        ],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(ic3_bin(
                "OpAnd",
                ic3_bin(
                    "OpEq",
                    ic3_field("alias", "status", entity_ty.clone(), status_ty.clone()),
                    ic3_status_ctor("Pending"),
                    IRType::Bool,
                ),
                ic3_bin(
                    "OpGt",
                    ic3_field("picked", "total", entity_ty.clone(), IRType::Int),
                    ic3_var("threshold", IRType::Int),
                    IRType::Bool,
                ),
                IRType::Bool,
            )),
            then_body: Box::new(IRExpr::One {
                var: "flag".to_owned(),
                domain: IRType::Bool,
                body: Box::new(ic3_var("flag", IRType::Bool)),
                span: None,
            }),
            else_body: Some(Box::new(IRExpr::Lone {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                body: Box::new(ic3_bin(
                    "OpNEq",
                    ic3_var("candidate", status_ty.clone()),
                    ic3_status_ctor("Shipped"),
                    IRType::Bool,
                )),
                span: None,
            })),
            span: None,
        }),
        span: None,
    };
    let property_smt = guard_to_smt_sys_prop_scoped(
        &property_let,
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("system property let/choose");
    assert!(property_smt.contains("Order_1_f1"));
    assert!(property_smt.contains("Order_0_active"));
    assert!(property_smt.contains("(let ((threshold"));

    let value_expr = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "mapped".to_owned(),
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Int),
            },
            expr: IRExpr::MapUpdate {
                map: Box::new(ic3_var(
                    "m",
                    IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Int),
                    },
                )),
                key: Box::new(ic3_int_lit(1)),
                value: Box::new(ic3_bin(
                    "OpMod",
                    ic3_field("bound", "total", entity_ty.clone(), IRType::Int),
                    ic3_int_lit(2),
                    IRType::Int,
                )),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                span: None,
            },
        }],
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(ic3_field(
                "bound",
                "status",
                entity_ty.clone(),
                status_ty.clone(),
            )),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Pending".to_owned(),
                        fields: vec![],
                    },
                    guard: Some(ic3_bool_lit(true)),
                    body: IRExpr::Index {
                        map: Box::new(ic3_var(
                            "mapped",
                            IRType::Map {
                                key: Box::new(IRType::Int),
                                value: Box::new(IRType::Int),
                            },
                        )),
                        key: Box::new(ic3_int_lit(1)),
                        ty: IRType::Int,
                        span: None,
                    },
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: ic3_int_lit(0),
                },
            ],
            span: None,
        }),
        span: None,
    };
    let value_smt = expr_to_smt_sys_prop_scoped(
        &value_expr,
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::from(["m".to_owned()]),
        &entity_locals,
    )
    .expect("system property value");
    assert!(value_smt.contains("(store m 1 (mod Order_1_f2 2))"));
    assert!(value_smt.contains("(select mapped 1)"));

    let two_smt = guard_to_smt_sys_prop_two_scoped(
        &ic3_bin(
            "OpEq",
            ic3_field("rhs", "status", entity_ty.clone(), status_ty.clone()),
            ic3_status_ctor("Pending"),
            IRType::Bool,
        ),
        &entities,
        &slots,
        &entity,
        &entity,
        &vctx,
        "Order",
        0,
        "lhs",
        "Order",
        1,
        "rhs",
        &HashSet::new(),
        &Ic3SystemEntityLocals::from([
            ("lhs".to_owned(), ("Order".to_owned(), 0)),
            ("rhs".to_owned(), ("Order".to_owned(), 1)),
        ]),
    )
    .expect("system property two scoped");
    assert_eq!(two_smt, "(= Order_1_f1 0)");

    assert!(expr_to_smt_sys_prop_scoped(
        &ic3_var("bound", entity_ty.clone()),
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect_err("bare entity local rejected")
    .contains("bare entity local"));
    assert!(expr_to_smt_sys_prop_scoped(
        &IRExpr::Field {
            expr: Box::new(ic3_var("bound", entity_ty.clone())),
            field: "missing".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect_err("missing field rejected")
    .contains("field missing not found"));
    assert!(expr_to_smt_sys_prop_scoped(
        &IRExpr::IfElse {
            cond: Box::new(ic3_bool_lit(true)),
            then_body: Box::new(ic3_int_lit(1)),
            else_body: None,
            span: None,
        },
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect_err("property value if requires else")
    .contains("without else"));
    assert!(guard_to_smt_sys_prop_scoped(
        &IRExpr::Match {
            scrutinee: Box::new(ic3_status_ctor("Pending")),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: ic3_bool_lit(true),
            }],
            span: None,
        },
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect_err("non-exhaustive property guard")
    .contains("non-exhaustive"));
}

#[test]
fn multi_slot_scoped_translators_cover_locals_match_quantifiers_and_two_slot_paths() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let mut entity_locals = Ic3SlotEntityLocals::new();
    entity_locals.insert("other".to_owned(), 1);

    let value_expr = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "picked".to_owned(),
            ty: status_ty.clone(),
            expr: IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            },
        }],
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "other".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                    span: None,
                }),
                field: "status".to_owned(),
                ty: status_ty.clone(),
                span: None,
            }),
            arms: vec![
                IRMatchArm {
                    pattern: IRPattern::PCtor {
                        name: "Pending".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: IRExpr::Var {
                        name: "picked".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    },
                },
                IRMatchArm {
                    pattern: IRPattern::PWild,
                    guard: None,
                    body: IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Confirmed".to_owned(),
                        args: vec![],
                        span: None,
                    },
                },
            ],
            span: None,
        }),
        span: None,
    };
    let value_smt = expr_to_smt_slot_scoped(
        &value_expr,
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("slot value");
    assert!(value_smt.contains("(let ((picked"));
    assert!(value_smt.contains("(ite "));
    assert!(value_smt.contains("s1_f1"));

    let guard_expr = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "picked".to_owned(),
            ty: status_ty.clone(),
            expr: IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                predicate: Some(Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "candidate".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                })),
                ty: status_ty.clone(),
                span: None,
            },
        }],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "other".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "picked".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            then_body: Box::new(IRExpr::Forall {
                var: "flag".to_owned(),
                domain: IRType::Bool,
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "flag".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "flag".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            else_body: Some(Box::new(IRExpr::Exists {
                var: "flag".to_owned(),
                domain: IRType::Bool,
                body: Box::new(IRExpr::Var {
                    name: "flag".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            })),
            span: None,
        }),
        span: None,
    };
    let guard_smt = guard_to_smt_slot_scoped(
        &guard_expr,
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("slot guard");
    assert!(guard_smt.contains("(let ((picked"));
    assert!(guard_smt.contains("(ite "));

    let two_slot = guard_to_smt_two_slots_scoped(
        &IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "lhs".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "rhs".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "total".to_owned(),
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
            ty: IRType::Bool,
            span: None,
        },
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect("two-slot guard");
    assert!(two_slot.contains("s0_f1"));
    assert!(two_slot.contains("s1_f2"));
}

#[test]
fn multi_slot_value_expr_translator_covers_scalar_collection_and_error_paths() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys);
    let vctx = VerifyContext::from_ir(&ir);
    let map_ty = IRType::Map {
        key: Box::new(IRType::Int),
        value: Box::new(IRType::Int),
    };
    let locals = HashSet::from(["m".to_owned(), "k".to_owned(), "v".to_owned()]);

    assert_eq!(
        expr_to_smt(&ic3_int_lit(-3), &entity, &vctx).unwrap(),
        "(- 3)"
    );
    assert_eq!(
        expr_to_smt(
            &IRExpr::Lit {
                ty: IRType::Real,
                value: LitVal::Real { value: 1.25 },
                span: None,
            },
            &entity,
            &vctx,
        )
        .unwrap(),
        "1.25"
    );
    assert_eq!(
        expr_to_smt(
            &IRExpr::Lit {
                ty: IRType::Float,
                value: LitVal::Float { value: 2.5 },
                span: None,
            },
            &entity,
            &vctx,
        )
        .unwrap(),
        "2.5"
    );
    assert!(expr_to_smt(
        &IRExpr::Lit {
            ty: IRType::String,
            value: LitVal::Str {
                value: "x".to_owned(),
            },
            span: None,
        },
        &entity,
        &vctx,
    )
    .expect_err("strings are unsupported")
    .contains("string literals"));

    let map_update = IRExpr::MapUpdate {
        map: Box::new(ic3_var("m", map_ty.clone())),
        key: Box::new(ic3_var("k", IRType::Int)),
        value: Box::new(ic3_var("v", IRType::Int)),
        ty: map_ty.clone(),
        span: None,
    };
    assert_eq!(
        expr_to_smt_scoped(&map_update, &entity, &vctx, &locals).unwrap(),
        "(store m k v)"
    );

    let index = IRExpr::Index {
        map: Box::new(ic3_var("m", map_ty)),
        key: Box::new(ic3_int_lit(1)),
        ty: IRType::Int,
        span: None,
    };
    assert_eq!(
        expr_to_smt_scoped(&index, &entity, &vctx, &locals).unwrap(),
        "(select m 1)"
    );

    let negated_sum = IRExpr::UnOp {
        op: "OpNeg".to_owned(),
        operand: Box::new(IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(ic3_int_lit(1)),
            right: Box::new(IRExpr::BinOp {
                op: "OpMod".to_owned(),
                left: Box::new(ic3_int_lit(7)),
                right: Box::new(ic3_int_lit(3)),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Int,
            span: None,
        }),
        ty: IRType::Int,
        span: None,
    };
    assert_eq!(
        expr_to_smt(&negated_sum, &entity, &vctx).unwrap(),
        "(- (+ 1 (mod 7 3)))"
    );

    let if_without_else = IRExpr::IfElse {
        cond: Box::new(ic3_bool_lit(true)),
        then_body: Box::new(ic3_int_lit(1)),
        else_body: None,
        span: None,
    };
    assert!(expr_to_smt(&if_without_else, &entity, &vctx)
        .expect_err("value if requires else")
        .contains("without else"));
    assert!(expr_to_smt(
        &IRExpr::Card {
            expr: Box::new(ic3_var(
                "m",
                IRType::Set {
                    element: Box::new(IRType::Int),
                },
            )),
            span: None,
        },
        &entity,
        &vctx,
    )
    .expect_err("cardinality unsupported")
    .contains("cardinality"));
}

#[test]
fn multi_slot_constraint_and_guard_translators_cover_scoped_forms() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let locals = HashSet::from(["limit".to_owned()]);

    let constraint = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "ok".to_owned(),
            ty: IRType::Bool,
            expr: IRExpr::BinOp {
                op: "OpGt".to_owned(),
                left: Box::new(ic3_var("$", IRType::Int)),
                right: Box::new(ic3_int_lit(0)),
                ty: IRType::Bool,
                span: None,
            },
        }],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(IRExpr::UnOp {
                op: "OpNot".to_owned(),
                operand: Box::new(ic3_var("ok", IRType::Bool)),
                ty: IRType::Bool,
                span: None,
            }),
            then_body: Box::new(IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(ic3_var("total", IRType::Int)),
                right: Box::new(ic3_var("limit", IRType::Int)),
                ty: IRType::Bool,
                span: None,
            }),
            else_body: None,
            span: None,
        }),
        span: None,
    };
    let smt =
        constraint_to_smt_with_dollar_scoped(&constraint, "candidate", &entity, &vctx, &locals)
            .expect("constraint");
    assert!(smt.contains("(let ((ok (> candidate 0))"));
    assert!(smt.contains("(=> (not ok) (<= candidate limit))"));

    let unsupported = IRExpr::BinOp {
        op: "OpDiv".to_owned(),
        left: Box::new(ic3_var("$", IRType::Int)),
        right: Box::new(ic3_int_lit(2)),
        ty: IRType::Int,
        span: None,
    };
    assert!(
        constraint_to_smt_with_dollar(&unsupported, "candidate", &entity, &vctx)
            .expect_err("division unsupported in constraint")
            .contains("unsupported op")
    );

    let guard = IRExpr::Let {
        bindings: vec![LetBinding {
            name: "picked".to_owned(),
            ty: status_ty.clone(),
            expr: IRExpr::Choose {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                predicate: Some(Box::new(IRExpr::BinOp {
                    op: "OpNEq".to_owned(),
                    left: Box::new(ic3_var("candidate", status_ty.clone())),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Shipped".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                })),
                ty: status_ty.clone(),
                span: None,
            },
        }],
        body: Box::new(IRExpr::BinOp {
            op: "OpImplies".to_owned(),
            left: Box::new(ic3_bool_lit(true)),
            right: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(ic3_var("picked", status_ty.clone())),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
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
    let guard_smt = guard_to_smt(&guard, &entity, &vctx).expect("guard let choose");
    assert!(guard_smt.contains("(let ((picked"));
    assert!(guard_smt.contains("(=> true"));

    assert_eq!(
        negate_property_smt(
            &IRExpr::Always {
                body: Box::new(ic3_bool_lit(true)),
                span: None,
            },
            &entity,
            &vctx,
        )
        .unwrap(),
        "(not true)"
    );
}

#[test]
fn system_property_scoped_choose_over_entities_expands_active_slot_disjunctions() {
    let (entity, tys) = make_simple_entity();
    let ir = IRProgram {
        types: tys,
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };
    let vctx = VerifyContext::from_ir(&ir);
    let entities = vec![&entity];
    let slots = HashMap::from([("Order".to_owned(), 2_usize)]);
    let bindings = vec![LetBinding {
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
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "candidate".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "total".to_owned(),
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
            })),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        },
    }];
    let body = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "picked".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![],
            },
            span: None,
        }),
        right: Box::new(IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Pending".to_owned(),
            args: vec![],
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let smt = guard_let_to_smt_sys_prop_scoped(
        &bindings,
        &body,
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &Ic3SystemEntityLocals::new(),
    )
    .expect("entity choose property");
    assert!(smt.contains("Order_0_active"));
    assert!(smt.contains("Order_1_active"));
    assert!(smt.contains("Order_0_f2"));
    assert!(smt.contains("Order_0_f1") || smt.contains("Order_1_f1"));
}

#[test]
fn multi_slot_choose_over_entities_expands_active_slot_disjunctions() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys);
    let vctx = VerifyContext::from_ir(&ir);
    let bindings = vec![LetBinding {
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
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "candidate".to_owned(),
                        ty: IRType::Entity {
                            name: "Order".to_owned(),
                        },
                        span: None,
                    }),
                    field: "total".to_owned(),
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
            })),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        },
    }];
    let body = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "picked".to_owned(),
                ty: IRType::Entity {
                    name: "Order".to_owned(),
                },
                span: None,
            }),
            field: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![],
            },
            span: None,
        }),
        right: Box::new(IRExpr::Ctor {
            enum_name: "Status".to_owned(),
            ctor: "Pending".to_owned(),
            args: vec![],
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let smt = guard_let_to_smt_slot_scoped(
        &bindings,
        &body,
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect("entity choose slot");
    assert!(smt.contains("s0_active"));
    assert!(smt.contains("s1_active"));
    assert!(smt.contains("s0_f2"));
    assert!(smt.contains("s0_f1") || smt.contains("s1_f1"));
}

#[test]
fn multi_slot_choose_helpers_cover_finite_quantified_and_direct_witness_paths() {
    let (entity, types) = make_simple_entity();
    let vctx = VerifyContext::from_ir(&make_ir_for_entity(&entity, types));
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![
            IRVariant::simple("Pending"),
            IRVariant::simple("Confirmed"),
            IRVariant::simple("Shipped"),
        ],
    };
    let payload_ty = IRType::Enum {
        name: "MaybeInt".to_owned(),
        variants: vec![IRVariant {
            name: "Some".to_owned(),
            fields: vec![IRVariantField {
                name: "value".to_owned(),
                ty: IRType::Int,
            }],
        }],
    };

    assert_eq!(
        ic3_finite_choose_candidates(&IRType::Bool, &vctx),
        Some(vec!["false".to_owned(), "true".to_owned()])
    );
    assert_eq!(
        ic3_finite_choose_candidates(&status_ty, &vctx),
        Some(vec!["0".to_owned(), "1".to_owned(), "2".to_owned()])
    );
    assert!(ic3_finite_choose_candidates(&payload_ty, &vctx).is_none());
    assert_eq!(
        ic3_quantified_choose_sort(&payload_ty),
        Some("MaybeInt".to_owned())
    );
    assert_eq!(
        default_witness_for_type(&payload_ty),
        Some("(Some 0)".to_owned())
    );

    let locals = HashSet::new();
    let body = IRExpr::Var {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        span: None,
    };
    let formula = ic3_finite_quantifier_formula(
        "flag",
        &IRType::Bool,
        &body,
        &vctx,
        &locals,
        |_, scope| {
            assert!(scope.contains("flag"));
            Ok("flag".to_owned())
        },
        "exists",
    )
    .expect("finite quantifier")
    .expect("finite bool domain");
    assert_eq!(
        formula,
        "(or (let ((flag false)) flag) (let ((flag true)) flag))"
    );
    let err = ic3_finite_quantifier_formula(
        "flag",
        &IRType::Bool,
        &body,
        &vctx,
        &locals,
        |_, _| Ok("true".to_owned()),
        "bad",
    )
    .expect_err("unknown quantifier kind");
    assert!(err.contains("unknown finite quantifier kind"));

    let quantified = ic3_quantified_choose_formula(
        "__x",
        "x",
        &IRType::Int,
        Some(&IRExpr::BinOp {
            op: "OpGt".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 3 },
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        &locals,
        |_, scope| {
            assert!(scope.contains("x"));
            Ok("(> x 3)".to_owned())
        },
        "rest".to_owned(),
    )
    .expect("quantified choose")
    .expect("int quantified choose");
    assert_eq!(
        quantified,
        "(exists ((__x Int)) (let ((x __x)) (and (> x 3) rest)))"
    );

    let lower = IRExpr::BinOp {
        op: "OpGt".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        }),
        right: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 4 },
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let upper = IRExpr::BinOp {
        op: "OpLt".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        }),
        right: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 9 },
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let witness = ic3_direct_choose_witness(
        "x",
        &IRType::Int,
        Some(&IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(lower),
            right: Box::new(upper),
            ty: IRType::Bool,
            span: None,
        }),
        &locals,
        |expr, _| match expr {
            IRExpr::Lit {
                value: LitVal::Int { value },
                ..
            } => Ok(value.to_string()),
            other => Ok(format!("{other:?}")),
        },
        |_, _| Ok("true".to_owned()),
        |_, _, _| Ok(vec![]),
        |_, _, _| Ok("true".to_owned()),
    )
    .expect("direct witness")
    .expect("numeric witness");
    assert_eq!(witness, "(+ 4 1)");
}

#[test]
fn system_expr_and_property_translators_cover_misc_paths_and_errors() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let entities = vec![&entity];
    let slots = HashMap::from([("Order".to_owned(), 2_usize)]);
    let locals = HashSet::from(["m".to_owned()]);
    let entity_locals = Ic3SystemEntityLocals::new();

    let map_ty = IRType::Map {
        key: Box::new(IRType::Int),
        value: Box::new(IRType::Int),
    };
    let map_update = IRExpr::MapUpdate {
        map: Box::new(IRExpr::Var {
            name: "m".to_owned(),
            ty: map_ty.clone(),
            span: None,
        }),
        key: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        }),
        value: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 2 },
            span: None,
        }),
        ty: map_ty.clone(),
        span: None,
    };
    let index = IRExpr::Index {
        map: Box::new(map_update),
        key: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        }),
        ty: IRType::Int,
        span: None,
    };
    let index_smt = expr_to_smt_sys_scoped(&index, &entity, &vctx, "Order", 0, &locals)
        .expect("plain system index");
    assert!(index_smt.contains("(select (store m 1 2) 1)"));

    let index_prop = expr_to_smt_sys_prop_scoped(
        &index,
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &locals,
        &entity_locals,
    )
    .expect("property system index");
    assert_eq!(index_prop, index_smt);

    let one_guard = IRExpr::One {
        var: "candidate".to_owned(),
        domain: status_ty.clone(),
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "candidate".to_owned(),
                ty: status_ty.clone(),
                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    };
    let one_smt = guard_to_smt_sys_prop_scoped(
        &one_guard,
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("one quantifier");
    assert!(one_smt.starts_with("(or "));
    assert!(one_smt.contains("(let ((candidate "));

    let if_without_else = IRExpr::IfElse {
        cond: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        then_body: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        }),
        else_body: None,
        span: None,
    };
    let err = expr_to_smt_sys_prop_scoped(
        &if_without_else,
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &entity_locals,
    )
    .expect_err("value if without else is unsupported");
    assert!(err.contains("without else"));

    let mut scoped_entities = Ic3SystemEntityLocals::new();
    scoped_entities.insert("picked".to_owned(), ("Order".to_owned(), 1));
    let bare_entity_err = expr_to_smt_sys_prop_scoped(
        &IRExpr::Var {
            name: "picked".to_owned(),
            ty: IRType::Entity {
                name: "Order".to_owned(),
            },
            span: None,
        },
        &entities,
        &slots,
        &entity,
        &vctx,
        "Order",
        0,
        &HashSet::new(),
        &scoped_entities,
    )
    .expect_err("bare entity local must be rejected");
    assert!(bare_entity_err.contains("bare entity local"));

    let non_quant_err = negate_property_smt_system(
        &IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        &entities,
        &vctx,
        &slots,
    )
    .expect_err("non-quantified system property unsupported");
    assert!(non_quant_err.contains("non-quantified"));
}

#[test]
fn multi_slot_property_translators_cover_misc_paths_and_errors() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let locals = HashSet::from(["m".to_owned()]);
    let entity_locals = Ic3SlotEntityLocals::new();

    let map_ty = IRType::Map {
        key: Box::new(IRType::Int),
        value: Box::new(IRType::Int),
    };
    let index = IRExpr::Index {
        map: Box::new(IRExpr::MapUpdate {
            map: Box::new(IRExpr::Var {
                name: "m".to_owned(),
                ty: map_ty.clone(),
                span: None,
            }),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            value: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },
                span: None,
            }),
            ty: map_ty,
            span: None,
        }),
        key: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        }),
        ty: IRType::Int,
        span: None,
    };
    let index_smt = expr_to_smt_slot_scoped(&index, &entity, &vctx, 0, 2, &locals, &entity_locals)
        .expect("slot index");
    assert!(index_smt.contains("(select (store m 1 2) 1)"));

    let lone_guard = IRExpr::Lone {
        var: "candidate".to_owned(),
        domain: status_ty.clone(),
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "candidate".to_owned(),
                ty: status_ty.clone(),
                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    };
    let lone_smt = guard_to_smt_slot_scoped(
        &lone_guard,
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("lone quantifier");
    assert!(lone_smt.starts_with("(and "));
    assert!(lone_smt.contains("(not (and "));
    assert!(lone_smt.contains("(let ((candidate "));

    let assert_expr = IRExpr::Assert {
        expr: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
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
    let assert_smt = guard_to_smt_slot_scoped(
        &assert_expr,
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("assert guard");
    assert_eq!(assert_smt, "(= 1 1)");

    let if_without_else = IRExpr::IfElse {
        cond: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        then_body: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 1 },
            span: None,
        }),
        else_body: None,
        span: None,
    };
    let err = expr_to_smt_slot_scoped(
        &if_without_else,
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &entity_locals,
    )
    .expect_err("slot value if without else is unsupported");
    assert!(err.contains("without else"));

    let non_quant_smt = negate_property_smt_multi(
        &IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        &entity,
        &vctx,
        2,
    )
    .expect("non-quantified multi-slot property");
    assert_eq!(
        non_quant_smt,
        "(or (and s0_active (not true)) (and s1_active (not true)))"
    );
}

#[test]
fn multi_slot_two_slot_property_translators_cover_aliases_and_errors() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let entity_ty = IRType::Entity {
        name: "Order".to_owned(),
    };

    let nested_property = IRExpr::Forall {
        var: "lhs".to_owned(),
        domain: entity_ty.clone(),
        body: Box::new(IRExpr::Forall {
            var: "rhs".to_owned(),
            domain: entity_ty.clone(),
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(ic3_var("lhs", entity_ty.clone())),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Field {
                        expr: Box::new(ic3_var("rhs", entity_ty.clone())),
                        field: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(ic3_int_lit(-1)),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    };
    let negated =
        negate_property_smt_multi(&nested_property, &entity, &vctx, 2).expect("nested property");
    assert!(negated.contains("s0_active s1_active"));
    assert!(negated.contains("(not (>= (+ s0_f2 s1_f2) (- 1)))"));

    let alias_body = IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Field {
            expr: Box::new(ic3_var("left_alias", entity_ty.clone())),
            field: "status".to_owned(),
            ty: status_ty.clone(),
            span: None,
        }),
        right: Box::new(IRExpr::Field {
            expr: Box::new(ic3_var("right_alias", entity_ty.clone())),
            field: "status".to_owned(),
            ty: status_ty.clone(),
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    let alias_smt = guard_let_to_smt_two_slots_scoped(
        &[
            LetBinding {
                name: "left_alias".to_owned(),
                ty: entity_ty.clone(),
                expr: ic3_var("lhs", entity_ty.clone()),
            },
            LetBinding {
                name: "right_alias".to_owned(),
                ty: entity_ty.clone(),
                expr: ic3_var("rhs", entity_ty.clone()),
            },
        ],
        &alias_body,
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect("two-slot aliases");
    assert_eq!(alias_smt, "(= s0_f1 s1_f1)");

    let choose_binding = LetBinding {
        name: "picked".to_owned(),
        ty: entity_ty.clone(),
        expr: IRExpr::Choose {
            var: "candidate".to_owned(),
            domain: entity_ty.clone(),
            predicate: None,
            ty: entity_ty.clone(),
            span: None,
        },
    };
    let choose_body = IRExpr::Field {
        expr: Box::new(ic3_var("picked", entity_ty.clone())),
        field: "total".to_owned(),
        ty: IRType::Int,
        span: None,
    };
    let choose_smt = guard_let_to_smt_two_slots_scoped(
        &[choose_binding],
        &choose_body,
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect("entity choose in two-slot property");
    assert!(choose_smt.contains("s0_active"));
    assert!(choose_smt.contains("s1_active"));
    assert!(choose_smt.contains("s0_f2") || choose_smt.contains("s1_f2"));

    let finite_choose = LetBinding {
        name: "picked_status".to_owned(),
        ty: status_ty.clone(),
        expr: IRExpr::Choose {
            var: "candidate".to_owned(),
            domain: status_ty.clone(),
            predicate: None,
            ty: status_ty.clone(),
            span: None,
        },
    };
    let finite_smt = guard_let_to_smt_two_slots_scoped(
        &[finite_choose],
        &IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(ic3_var("picked_status", status_ty.clone())),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        },
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect("finite choose in two-slot property");
    assert!(finite_smt.contains("(let ((picked_status"));

    let mut entity_locals = Ic3SlotEntityLocals::new();
    entity_locals.insert("bound".to_owned(), 1);
    let bound_field = expr_to_smt_slot_scoped(
        &IRExpr::Field {
            expr: Box::new(ic3_var("bound", entity_ty.clone())),
            field: "total".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &entity_locals,
    )
    .expect("slot entity local field");
    assert_eq!(bound_field, "s1_f2");

    assert!(guard_to_smt_two_slots_scoped(
        &IRExpr::Field {
            expr: Box::new(ic3_var("scalar", IRType::Int)),
            field: "total".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::from(["scalar".to_owned()]),
        &Ic3SlotEntityLocals::new(),
    )
    .expect_err("local field projection rejected")
    .contains("cannot be used for field projection"));
    assert!(guard_to_smt_two_slots_scoped(
        &ic3_var("lhs", entity_ty.clone()),
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect_err("bare entity var rejected")
    .contains("bare entity variable"));
    assert!(guard_to_smt_two_slots_scoped(
        &IRExpr::BinOp {
            op: "OpDiv".to_owned(),
            left: Box::new(ic3_int_lit(4)),
            right: Box::new(ic3_int_lit(2)),
            ty: IRType::Int,
            span: None,
        },
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::new(),
    )
    .expect_err("unsupported two-slot op")
    .contains("unsupported op"));
}

#[test]
fn multi_slot_property_translators_cover_branchy_slot_and_two_slot_forms() {
    let (entity, tys) = make_simple_entity();
    let ir = make_ir_for_entity(&entity, tys.clone());
    let vctx = VerifyContext::from_ir(&ir);
    let status_ty = tys[0].ty.clone();
    let entity_ty = IRType::Entity {
        name: "Order".to_owned(),
    };

    let slot_guard = IRExpr::IfElse {
        cond: Box::new(IRExpr::UnOp {
            op: "OpNot".to_owned(),
            operand: Box::new(ic3_bool_lit(false)),
            ty: IRType::Bool,
            span: None,
        }),
        then_body: Box::new(ic3_bin(
            "OpOr",
            ic3_bin(
                "OpEq",
                ic3_field("o", "status", entity_ty.clone(), status_ty.clone()),
                ic3_status_ctor("Pending"),
                IRType::Bool,
            ),
            IRExpr::Exists {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                body: Box::new(ic3_bin(
                    "OpEq",
                    ic3_var("candidate", status_ty.clone()),
                    ic3_status_ctor("Confirmed"),
                    IRType::Bool,
                )),
                span: None,
            },
            IRType::Bool,
        )),
        else_body: Some(Box::new(IRExpr::Forall {
            var: "flag".to_owned(),
            domain: IRType::Bool,
            body: Box::new(ic3_bin(
                "OpImplies",
                ic3_var("flag", IRType::Bool),
                ic3_var("flag", IRType::Bool),
                IRType::Bool,
            )),
            span: None,
        })),
        span: None,
    };
    let slot_smt =
        guard_to_smt_slot(&slot_guard, &entity, &vctx, 1, 2).expect("branchy slot guard");
    assert!(slot_smt.contains("(ite "));
    assert!(slot_smt.contains("s1_f1"));
    assert!(slot_smt.contains("(=> flag flag)"));

    let slot_match_value = IRExpr::Match {
        scrutinee: Box::new(ic3_field(
            "o",
            "status",
            entity_ty.clone(),
            status_ty.clone(),
        )),
        arms: vec![
            IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: Some(ic3_bool_lit(true)),
                body: ic3_int_lit(1),
            },
            IRMatchArm {
                pattern: IRPattern::PWild,
                guard: None,
                body: ic3_int_lit(2),
            },
        ],
        span: None,
    };
    let value_smt =
        expr_to_smt_slot(&slot_match_value, &entity, &vctx, 1, 2).expect("slot match value");
    assert!(value_smt.contains("(ite "));
    assert!(value_smt.contains("s1_f1"));

    let slot_let_value = IRExpr::Let {
        bindings: vec![
            LetBinding {
                name: "ok".to_owned(),
                ty: IRType::Bool,
                expr: ic3_bin("OpLt", ic3_int_lit(1), ic3_int_lit(2), IRType::Bool),
            },
            LetBinding {
                name: "next".to_owned(),
                ty: IRType::Int,
                expr: IRExpr::UnOp {
                    op: "OpNeg".to_owned(),
                    operand: Box::new(ic3_bin(
                        "OpDiv",
                        ic3_field("o", "total", entity_ty.clone(), IRType::Int),
                        ic3_int_lit(2),
                        IRType::Int,
                    )),
                    ty: IRType::Int,
                    span: None,
                },
            },
        ],
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(ic3_var("ok", IRType::Bool)),
            then_body: Box::new(ic3_var("next", IRType::Int)),
            else_body: Some(Box::new(ic3_int_lit(0))),
            span: None,
        }),
        span: None,
    };
    let slot_value_smt =
        expr_to_smt_slot(&slot_let_value, &entity, &vctx, 1, 2).expect("slot let value");
    assert!(slot_value_smt.contains("(let ((ok (< 1 2))"));
    assert!(slot_value_smt.contains("(- (div s1_f2 2))"));

    let slot_assume = IRExpr::Assume {
        expr: Box::new(ic3_bin(
            "OpAnd",
            ic3_bool_lit(true),
            IRExpr::One {
                var: "flag".to_owned(),
                domain: IRType::Bool,
                body: Box::new(ic3_var("flag", IRType::Bool)),
                span: None,
            },
            IRType::Bool,
        )),
        span: None,
    };
    let slot_assume_smt =
        guard_to_smt_slot(&slot_assume, &entity, &vctx, 0, 2).expect("slot assume guard");
    assert!(slot_assume_smt.contains("(and true"));
    assert!(slot_assume_smt.contains("(let ((flag true))"));

    let two_slot_match = IRExpr::Match {
        scrutinee: Box::new(ic3_field(
            "lhs",
            "status",
            entity_ty.clone(),
            status_ty.clone(),
        )),
        arms: vec![
            IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: Some(ic3_bin(
                    "OpGe",
                    ic3_field("rhs", "total", entity_ty.clone(), IRType::Int),
                    ic3_int_lit(0),
                    IRType::Bool,
                )),
                body: ic3_bool_lit(true),
            },
            IRMatchArm {
                pattern: IRPattern::PWild,
                guard: None,
                body: ic3_bool_lit(false),
            },
        ],
        span: None,
    };
    let two_match_smt =
        guard_to_smt_two_slots(&two_slot_match, &entity, &vctx, "lhs", 0, "rhs", 1, 2)
            .expect("two-slot match");
    assert!(two_match_smt.contains("(ite "));
    assert!(two_match_smt.contains("s0_f1"));
    assert!(two_match_smt.contains("s1_f2"));

    let two_slot_if = IRExpr::IfElse {
        cond: Box::new(ic3_bin(
            "OpOr",
            ic3_bool_lit(false),
            ic3_bin(
                "OpEq",
                ic3_field("lhs", "status", entity_ty.clone(), status_ty.clone()),
                ic3_status_ctor("Pending"),
                IRType::Bool,
            ),
            IRType::Bool,
        )),
        then_body: Box::new(ic3_bin(
            "OpImplies",
            ic3_bool_lit(true),
            IRExpr::Lone {
                var: "candidate".to_owned(),
                domain: status_ty.clone(),
                body: Box::new(ic3_bin(
                    "OpNEq",
                    ic3_var("candidate", status_ty.clone()),
                    ic3_status_ctor("Shipped"),
                    IRType::Bool,
                )),
                span: None,
            },
            IRType::Bool,
        )),
        else_body: Some(Box::new(IRExpr::One {
            var: "flag".to_owned(),
            domain: IRType::Bool,
            body: Box::new(ic3_var("flag", IRType::Bool)),
            span: None,
        })),
        span: None,
    };
    let two_if_smt = guard_to_smt_two_slots(&two_slot_if, &entity, &vctx, "lhs", 0, "rhs", 1, 2)
        .expect("two-slot if");
    assert!(two_if_smt.contains("(ite "));
    assert!(two_if_smt.contains("(=> true"));

    let two_slot_assert = IRExpr::Assert {
        expr: Box::new(ic3_bin(
            "OpGt",
            ic3_bin(
                "OpMul",
                ic3_bin(
                    "OpSub",
                    ic3_field("rhs", "total", entity_ty.clone(), IRType::Int),
                    ic3_int_lit(1),
                    IRType::Int,
                ),
                ic3_int_lit(2),
                IRType::Int,
            ),
            ic3_int_lit(-5),
            IRType::Bool,
        )),
        span: None,
    };
    let two_assert_smt =
        guard_to_smt_two_slots(&two_slot_assert, &entity, &vctx, "lhs", 0, "rhs", 1, 2)
            .expect("two-slot assert arithmetic");
    assert_eq!(two_assert_smt, "(> (* (- s1_f2 1) 2) (- 5))");

    assert!(expr_to_smt_slot_scoped(
        &ic3_var("bound", entity_ty.clone()),
        &entity,
        &vctx,
        0,
        2,
        &HashSet::new(),
        &Ic3SlotEntityLocals::from([("bound".to_owned(), 1)]),
    )
    .expect_err("bare slot entity local rejected")
    .contains("bare entity local"));
    assert!(guard_to_smt_slot(
        &IRExpr::BinOp {
            op: "OpDiv".to_owned(),
            left: Box::new(ic3_int_lit(4)),
            right: Box::new(ic3_int_lit(2)),
            ty: IRType::Bool,
            span: None,
        },
        &entity,
        &vctx,
        0,
        2,
    )
    .expect_err("slot guard unsupported op")
    .contains("unsupported binary op"));
    assert!(guard_to_smt_two_slots(
        &IRExpr::Lit {
            ty: IRType::Real,
            value: LitVal::Real { value: 1.5 },
            span: None,
        },
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
    )
    .expect_err("unsupported two-slot literal")
    .contains("unsupported literal"));
    assert!(guard_to_smt_two_slots(
        &IRExpr::Match {
            scrutinee: Box::new(ic3_status_ctor("Pending")),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PCtor {
                    name: "Pending".to_owned(),
                    fields: vec![],
                },
                guard: None,
                body: ic3_bool_lit(true),
            }],
            span: None,
        },
        &entity,
        &vctx,
        "lhs",
        0,
        "rhs",
        1,
        2,
    )
    .expect_err("non-exhaustive two-slot match")
    .contains("non-exhaustive"));
}
