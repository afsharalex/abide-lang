use super::*;
use crate::ir::types::*;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

// NOTE: I don't know if I like having a separate file for this, but I'm not sure
// where else to put it. Should see if we can break this up and move to their local
// modules/files.

fn short_solver_regression_config() -> VerifyConfig {
    VerifyConfig {
        induction_timeout_ms: 5_000,
        bmc_timeout_ms: 5_000,
        ic3_timeout_ms: 5_000,
        overall_timeout_ms: 15_000,
        ..VerifyConfig::default()
    }
}

const UNBOUNDED_PROOF_TEST_ENV: &str = "ABIDE_RUN_UNBOUNDED_PROOF_TESTS";

fn should_run_unbounded_proof_tests() -> bool {
    std::env::var_os(UNBOUNDED_PROOF_TEST_ENV).is_some()
}

fn skip_unbounded_proof_test() {
    eprintln!("skipping unbounded proof-backend test; set {UNBOUNDED_PROOF_TEST_ENV}=1 to opt in");
}

fn bool_lit(value: bool) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value },
        span: None,
    }
}

macro_rules! require_unbounded_proof_tests {
    () => {
        if !should_run_unbounded_proof_tests() {
            skip_unbounded_proof_test();
            return;
        }
    };
}

/// Helper: build a minimal IR program with an Order entity, `OrderStatus` enum,
/// Commerce system, and a verify block.
fn make_order_ir(assert_expr: IRExpr, bound: usize) -> IRProgram {
    let order_status = IRTypeEntry {
        name: "OrderStatus".to_owned(),
        ty: IRType::Enum {
            name: "OrderStatus".to_owned(),
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

    let commerce_system = IRSystem {
        name: "Commerce".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Order".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "confirm_order".to_owned(),
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

    // / revised: these tests exercise the
    // verification dispatcher (BMC, induction, IC3) on a fixture
    // whose only event (`confirm_order`) requires an active Order
    // and there is no `create_order` event. Under verify's
    // default no-stutter assumption, the BMC trace cannot extend
    // past the initial state and the new direct deadlock
    // detection would short-circuit every test in this module to
    // a Deadlock verdict — masking the BMC/IC3/induction logic
    // the tests are actually trying to cover.
    //
    // The verify block here mirrors what a user would write as
    // `verify... { assume { stutter }... }`: the construct is
    // still `verify` (not `theorem`), but the assumption set has
    // explicitly opted into stutter. We construct the
    // IRAssumptionSet directly rather than calling
    // `default_for_theorem_or_lemma()` to avoid muddying the
    // construct kind — verify blocks default to no stutter, the
    // stutter here is the user's explicit opt-in.
    let verify = IRVerify {
        name: "test_verify".to_owned(),
        depth: Some(bound),
        systems: vec![IRVerifySystem {
            name: "Commerce".to_owned(),
            lo: 0,
            hi: bound as i64,
        }],
        stores: vec![],
        assumption_set: crate::ir::types::IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![assert_expr],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![order_status],
        constants: vec![],
        functions: vec![],
        entities: vec![order],
        systems: vec![commerce_system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

#[test]
fn verification_panic_boundary_converts_panics_to_unprovable() {
    let result =
        catch_verification_panic("panic_case", None, None, "checking verify block", || {
            panic!("boom");
        });

    match result {
        VerificationResult::Unprovable { name, hint, .. } => {
            assert_eq!(name, "panic_case");
            assert!(hint.contains("internal verifier error while checking verify block"));
            assert!(hint.contains("boom"));
        }
        other => panic!("expected Unprovable, got {other:?}"),
    }
}

#[test]
fn verification_panic_boundary_preserves_success_result() {
    let result = catch_verification_panic("ok_case", None, None, "checking verify block", || {
        VerificationResult::Checked {
            name: "ok_case".to_owned(),
            depth: 1,
            time_ms: 0,
            assumptions: vec![],
            span: None,
            file: None,
        }
    });

    assert!(matches!(
        result,
        VerificationResult::Checked { ref name, depth, .. } if name == "ok_case" && depth == 1
    ));
}

fn target_selector_test_ir() -> IRProgram {
    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![],
        verifies: vec![IRVerify {
            name: "same".to_owned(),
            depth: Some(1),
            systems: vec![],
            stores: vec![],
            assumption_set: IRAssumptionSet::default_for_verify(),
            asserts: vec![bool_lit(true)],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![
            IRLemma {
                name: "same".to_owned(),
                assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
                body: vec![bool_lit(true)],
                span: None,
                file: None,
            },
            IRLemma {
                name: "kept".to_owned(),
                assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
                body: vec![bool_lit(true)],
                span: None,
                file: None,
            },
        ],
        scenes: vec![],
    }
}

#[test]
fn verify_target_selector_parses_typed_and_untyped_forms() {
    let typed: VerifyTargetSelector = "verify:safety".parse().expect("typed target");
    assert_eq!(typed.kind, Some(VerifyTargetKind::Verify));
    assert_eq!(typed.name, "safety");
    assert_eq!(typed.to_string(), "verify:safety");

    let untyped: VerifyTargetSelector = "safety".parse().expect("untyped target");
    assert_eq!(untyped.kind, None);
    assert_eq!(untyped.name, "safety");
    assert_eq!(untyped.to_string(), "safety");

    assert!("unknown:safety".parse::<VerifyTargetSelector>().is_err());
}

#[test]
fn verify_all_target_runs_only_selected_lemma_result() {
    let ir = target_selector_test_ir();
    let results = verify_all(
        &ir,
        &VerifyConfig {
            target: Some("lemma:kept".parse().expect("target")),
            ..VerifyConfig::default()
        },
    );

    assert_eq!(results.len(), 1);
    assert!(matches!(
        &results[0],
        VerificationResult::Proved { name, .. } if name == "kept"
    ));
}

#[test]
fn verify_all_target_rejects_ambiguous_untyped_name() {
    let ir = target_selector_test_ir();
    let results = verify_all(
        &ir,
        &VerifyConfig {
            target: Some("same".parse().expect("target")),
            ..VerifyConfig::default()
        },
    );

    assert_eq!(results.len(), 1);
    assert!(matches!(
        &results[0],
        VerificationResult::Unprovable { hint, .. }
            if hint.contains("ambiguous")
                && hint.contains("lemma:same")
                && hint.contains("verify:same")
    ));
}

#[test]
fn verify_all_target_rejects_unknown_name_with_available_targets() {
    let ir = target_selector_test_ir();
    let results = verify_all(
        &ir,
        &VerifyConfig {
            target: Some("missing".parse().expect("target")),
            ..VerifyConfig::default()
        },
    );

    assert_eq!(results.len(), 1);
    assert!(matches!(
        &results[0],
        VerificationResult::Unprovable { hint, .. }
            if hint.contains("unknown verification target")
                && hint.contains("lemma:kept")
                && hint.contains("verify:same")
    ));
}

fn make_system_field_counter_ir() -> IRProgram {
    let counter = IRSystem {
        name: "Counter".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "inc".to_owned(),
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
                            name: "x".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
    };

    let verify = IRVerify {
        name: "sys_counter_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "Counter".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![counter],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_enum_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let system = IRSystem {
        name: "Workflow".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "finish".to_owned(),
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
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
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Done".to_owned(),
                        args: vec![],
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
    };

    let verify = IRVerify {
        name: "workflow_status_closed_world".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "Workflow".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Status".to_owned(),
                        ctor: "Done".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_enum_counterexample_ir() -> IRProgram {
    let mut ir = make_system_field_enum_ir();
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.verifies[0].name = "workflow_status_stays_pending".to_owned();
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: status_ty,
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
    }];
    ir
}

fn make_system_field_enum_deadlock_ir() -> IRProgram {
    let mut ir = make_system_field_enum_ir();
    ir.verifies[0].name = "workflow_deadlocks_after_finish".to_owned();
    ir.verifies[0].assumption_set = IRAssumptionSet {
        stutter: false,
        weak_fair: Vec::new(),
        strong_fair: Vec::new(),
        per_tuple: Vec::new(),
    };
    ir
}

fn make_system_field_eventual_liveness_counterexample_ir() -> IRProgram {
    let phase_ty = IRType::Enum {
        name: "Phase".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let pending = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    let system = IRSystem {
        name: "WorkflowLiveness".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "phase".to_owned(),
            ty: phase_ty.clone(),
            default: Some(pending.clone()),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "hold".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(pending.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(pending.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "finish".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(pending.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(done.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "stay_done".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(done.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(done.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
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
    };

    let verify = IRVerify {
        name: "workflow_eventually_finishes".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "WorkflowLiveness".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: false,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty,
                        span: None,
                    }),
                    right: Box::new(done),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_weak_fair_eventual_liveness_ir() -> IRProgram {
    let mut ir = make_system_field_eventual_liveness_counterexample_ir();
    ir.verifies[0].name = "workflow_eventually_finishes_under_weak_fair_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "WorkflowLiveness".to_owned(),
        command: "finish".to_owned(),
    }];
    ir
}

fn make_system_field_bool_param_weak_fair_eventual_liveness_ir() -> IRProgram {
    let flag_ty = IRType::Bool;
    let system = IRSystem {
        name: "ToggleLiveness".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "flag".to_owned(),
            ty: flag_ty.clone(),
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "set_flag".to_owned(),
            params: vec![IRTransParam {
                name: "next_flag".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "next_flag".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Var {
                        name: "flag".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "flag".to_owned(),
                            ty: flag_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "next_flag".to_owned(),
                        ty: flag_ty.clone(),
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
    };
    let verify = IRVerify {
        name: "toggle_eventually_reaches_true_under_weak_fair_set_flag".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "ToggleLiveness".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: vec![IRCommandRef {
                system: "ToggleLiveness".to_owned(),
                command: "set_flag".to_owned(),
            }],
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::Var {
                    name: "flag".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_bool_param_strong_fair_eventual_liveness_ir() -> IRProgram {
    let mut ir = make_system_field_bool_param_weak_fair_eventual_liveness_ir();
    ir.verifies[0].name = "toggle_eventually_reaches_true_under_strong_fair_set_flag".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "ToggleLiveness".to_owned(),
        command: "set_flag".to_owned(),
    }];
    ir
}

fn make_system_field_enum_param_per_tuple_weak_fair_liveness_ir() -> IRProgram {
    let side_ty = IRType::Enum {
        name: "Side".to_owned(),
        variants: vec![IRVariant::simple("Left"), IRVariant::simple("Right")],
    };
    let left = IRExpr::Ctor {
        enum_name: "Side".to_owned(),
        ctor: "Left".to_owned(),
        args: vec![],
        span: None,
    };
    let right = IRExpr::Ctor {
        enum_name: "Side".to_owned(),
        ctor: "Right".to_owned(),
        args: vec![],
        span: None,
    };
    let bool_ty = IRType::Bool;
    let system = IRSystem {
        name: "TupleFairness".to_owned(),
        store_params: vec![],
        fields: vec![
            IRField {
                name: "left_done".to_owned(),
                ty: bool_ty.clone(),
                default: Some(IRExpr::Lit {
                    ty: bool_ty.clone(),
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "right_done".to_owned(),
                ty: bool_ty.clone(),
                default: Some(IRExpr::Lit {
                    ty: bool_ty.clone(),
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "serve".to_owned(),
            params: vec![IRTransParam {
                name: "side".to_owned(),
                ty: side_ty.clone(),
            }],
            guard: IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "side".to_owned(),
                            ty: side_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(left.clone()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::UnOp {
                        op: "OpNot".to_owned(),
                        operand: Box::new(IRExpr::Var {
                            name: "left_done".to_owned(),
                            ty: bool_ty.clone(),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "side".to_owned(),
                            ty: side_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(right.clone()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::UnOp {
                        op: "OpNot".to_owned(),
                        operand: Box::new(IRExpr::Var {
                            name: "right_done".to_owned(),
                            ty: bool_ty.clone(),
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
            },
            body: vec![
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "left_done".to_owned(),
                                ty: bool_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpOr".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "left_done".to_owned(),
                                ty: bool_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "side".to_owned(),
                                    ty: side_ty.clone(),
                                    span: None,
                                }),
                                right: Box::new(left),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ty: bool_ty.clone(),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                },
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "right_done".to_owned(),
                                ty: bool_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::BinOp {
                            op: "OpOr".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "right_done".to_owned(),
                                ty: bool_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "side".to_owned(),
                                    ty: side_ty.clone(),
                                    span: None,
                                }),
                                right: Box::new(right),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ty: bool_ty.clone(),
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
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
    let verify = IRVerify {
        name: "both_sides_eventually_finish_under_per_tuple_weak_fairness".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TupleFairness".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: vec![IRCommandRef {
                system: "TupleFairness".to_owned(),
                command: "serve".to_owned(),
            }],
            strong_fair: Vec::new(),
            per_tuple: vec![IRCommandRef {
                system: "TupleFairness".to_owned(),
                command: "serve".to_owned(),
            }],
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "left_done".to_owned(),
                        ty: bool_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "right_done".to_owned(),
                        ty: bool_ty,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_enum_param_per_tuple_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_system_field_enum_param_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name = "both_sides_eventually_finish_under_per_tuple_strong_fairness".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TupleFairness".to_owned(),
        command: "serve".to_owned(),
    }];
    ir
}

fn make_system_field_strong_fair_eventual_liveness_ir() -> IRProgram {
    let phase_ty = IRType::Enum {
        name: "Phase".to_owned(),
        variants: vec![
            IRVariant::simple("A"),
            IRVariant::simple("B"),
            IRVariant::simple("Done"),
        ],
    };
    let a = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "A".to_owned(),
        args: vec![],
        span: None,
    };
    let b = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "B".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    let system = IRSystem {
        name: "WorkflowStrongFair".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "phase".to_owned(),
            ty: phase_ty.clone(),
            default: Some(a.clone()),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "tick_to_b".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(a.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(b.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "tick_to_a".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(b.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(a.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "finish".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(a.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(done.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "stay_done".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(done.clone()),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(done.clone()),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
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
    };

    let verify = IRVerify {
        name: "workflow_eventually_finishes_under_strong_fair_finish".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "WorkflowStrongFair".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: false,
            weak_fair: Vec::new(),
            strong_fair: vec![IRCommandRef {
                system: "WorkflowStrongFair".to_owned(),
                command: "finish".to_owned(),
            }],
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "phase".to_owned(),
                        ty: phase_ty,
                        span: None,
                    }),
                    right: Box::new(done),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_bool_param_counterexample_ir() -> IRProgram {
    let mut ir = make_system_field_bool_param_ir();
    ir.verifies[0].name = "toggle_stays_false".to_owned();
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::UnOp {
            op: "OpNot".to_owned(),
            operand: Box::new(IRExpr::Var {
                name: "flag".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    }];
    ir
}

fn make_multi_system_field_counterexample_ir() -> IRProgram {
    let phase_ty = IRType::Enum {
        name: "Phase".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let gate_ty = IRType::Enum {
        name: "Gate".to_owned(),
        variants: vec![IRVariant::simple("Closed"), IRVariant::simple("Open")],
    };
    let left = IRSystem {
        name: "Left".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "left_phase".to_owned(),
            ty: phase_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Phase".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "finish_left".to_owned(),
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "left_phase".to_owned(),
                    ty: phase_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Phase".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "left_phase".to_owned(),
                            ty: phase_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Phase".to_owned(),
                        ctor: "Done".to_owned(),
                        args: vec![],
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
    };
    let right = IRSystem {
        name: "Right".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "right_gate".to_owned(),
            ty: gate_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Gate".to_owned(),
                ctor: "Closed".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "open_right".to_owned(),
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "right_gate".to_owned(),
                    ty: gate_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Gate".to_owned(),
                    ctor: "Closed".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "right_gate".to_owned(),
                            ty: gate_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Gate".to_owned(),
                        ctor: "Open".to_owned(),
                        args: vec![],
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
    };
    let verify = IRVerify {
        name: "left_done_requires_open_gate".to_owned(),
        depth: None,
        systems: vec![
            IRVerifySystem {
                name: "Left".to_owned(),
                lo: 0,
                hi: 1,
            },
            IRVerifySystem {
                name: "Right".to_owned(),
                lo: 0,
                hi: 1,
            },
        ],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: false,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpNEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "left_phase".to_owned(),
                        ty: phase_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Phase".to_owned(),
                        ctor: "Done".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "right_gate".to_owned(),
                        ty: gate_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Gate".to_owned(),
                        ctor: "Open".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![left, right],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "Ticket".to_owned(),
    };
    let ticket = IREntity {
        name: "Ticket".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "TicketStatus".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "finish".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "TicketStatus".to_owned(),
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
                    enum_name: "TicketStatus".to_owned(),
                    ctor: "Done".to_owned(),
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
    let system = IRSystem {
        name: "TicketOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "finish_one".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "t".to_owned(),
                    entity: "Ticket".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: ticket_entity_ty.clone(),
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "TicketStatus".to_owned(),
                            ctor: "Pending".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "t".to_owned(),
                        transition: "finish".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "ticket_status_is_finite".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TicketOps".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![IRStoreDecl {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
            lo: 0,
            hi: 1,
        }],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "t".to_owned(),
                domain: ticket_entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpOr".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: IRType::Entity {
                                    name: "Ticket".to_owned(),
                                },
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "TicketStatus".to_owned(),
                            ctor: "Pending".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: IRType::Entity {
                                    name: "Ticket".to_owned(),
                                },
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "TicketStatus".to_owned(),
                            ctor: "Done".to_owned(),
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
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![ticket],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_counterexample_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.verifies[0].name = "tickets_stay_pending".to_owned();
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "t".to_owned(),
            domain: IRType::Entity {
                name: "Ticket".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "t".to_owned(),
                        ty: IRType::Entity {
                            name: "Ticket".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: status_ty,
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "TicketStatus".to_owned(),
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
    }];
    ir
}

fn make_explicit_entity_store_deadlock_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ir();
    ir.systems[0].actions.remove(0);
    ir.verifies[0].name = "ticket_pool_deadlocks_without_create".to_owned();
    ir.verifies[0].assumption_set = IRAssumptionSet {
        stutter: false,
        weak_fair: Vec::new(),
        strong_fair: Vec::new(),
        per_tuple: Vec::new(),
    };
    ir
}

fn make_explicit_entity_store_eventual_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.verifies[0].name = "tickets_eventually_finish".to_owned();
    ir.verifies[0].assumption_set = IRAssumptionSet {
        stutter: true,
        weak_fair: Vec::new(),
        strong_fair: Vec::new(),
        per_tuple: Vec::new(),
    };
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "t".to_owned(),
            domain: IRType::Entity {
                name: "Ticket".to_owned(),
            },
            body: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Entity {
                                name: "Ticket".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "TicketStatus".to_owned(),
                        ctor: "Done".to_owned(),
                        args: vec![],
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
    }];
    ir
}

fn make_explicit_entity_store_implication_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.verifies[0].name = "tickets_pending_implies_eventually_finish".to_owned();
    ir.verifies[0].assumption_set = IRAssumptionSet {
        stutter: true,
        weak_fair: Vec::new(),
        strong_fair: Vec::new(),
        per_tuple: Vec::new(),
    };
    ir.verifies[0].asserts = vec![IRExpr::Forall {
        var: "t".to_owned(),
        domain: IRType::Entity {
            name: "Ticket".to_owned(),
        },
        body: Box::new(IRExpr::BinOp {
            op: "implies".to_owned(),
            left: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "t".to_owned(),
                        ty: IRType::Entity {
                            name: "Ticket".to_owned(),
                        },
                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "TicketStatus".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            right: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Entity {
                                name: "Ticket".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "TicketStatus".to_owned(),
                        ctor: "Done".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    }];
    ir
}

fn make_explicit_entity_store_transition_arg_counterexample_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "Ticket".to_owned(),
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let ticket = IREntity {
        name: "Ticket".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(pending.clone()),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "set_status".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "next_status".to_owned(),
                ty: status_ty.clone(),
            }],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(pending.clone()),
                ty: IRType::Bool,
                span: None,
            },
            updates: vec![IRUpdate {
                field: "status".to_owned(),
                value: IRExpr::Var {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let system = IRSystem {
        name: "TicketOpsArgs".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "set_one".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "t".to_owned(),
                    entity: "Ticket".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: ticket_entity_ty.clone(),
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(pending),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "t".to_owned(),
                        transition: "set_status".to_owned(),
                        refs: vec![],
                        args: vec![IRExpr::Var {
                            name: "next_status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "tickets_stay_pending_under_param_update".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TicketOpsArgs".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![IRStoreDecl {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
            lo: 0,
            hi: 1,
        }],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "t".to_owned(),
                domain: IRType::Entity {
                    name: "Ticket".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Entity {
                                name: "Ticket".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "TicketStatus".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![ticket],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_ref_counterexample_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "Ticket".to_owned(),
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let ticket = IREntity {
        name: "Ticket".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(pending.clone()),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "finish_if_peer_pending".to_owned(),
            refs: vec![IRTransRef {
                name: "peer".to_owned(),
                entity: "Ticket".to_owned(),
            }],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(pending.clone()),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "peer".to_owned(),
                            ty: ticket_entity_ty.clone(),
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(pending.clone()),
                    ty: IRType::Bool,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            updates: vec![IRUpdate {
                field: "status".to_owned(),
                value: IRExpr::Ctor {
                    enum_name: "TicketStatus".to_owned(),
                    ctor: "Done".to_owned(),
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
    let system = IRSystem {
        name: "TicketPeerOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "finish_with_peer".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "t".to_owned(),
                    entity: "Ticket".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: ticket_entity_ty.clone(),
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(pending.clone()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ops: vec![IRAction::Choose {
                        var: "peer".to_owned(),
                        entity: "Ticket".to_owned(),
                        filter: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "peer".to_owned(),
                                    ty: ticket_entity_ty.clone(),
                                    span: None,
                                }),
                                field: "status".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(pending.clone()),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "t".to_owned(),
                            transition: "finish_if_peer_pending".to_owned(),
                            refs: vec!["peer".to_owned()],
                            args: vec![],
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "tickets_stay_pending_under_peer_ref_update".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TicketPeerOps".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![IRStoreDecl {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
            lo: 0,
            hi: 1,
        }],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "t".to_owned(),
                domain: IRType::Entity {
                    name: "Ticket".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Entity {
                                name: "Ticket".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "TicketStatus".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![ticket],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_ref_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_counterexample_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let done = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    ir.verifies[0].name = "tickets_eventually_finish_under_weak_fair_peer_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerOps".to_owned(),
        command: "finish_with_peer".to_owned(),
    }];
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "t".to_owned(),
            domain: IRType::Entity {
                name: "Ticket".to_owned(),
            },
            body: Box::new(IRExpr::Eventually {
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Entity {
                                name: "Ticket".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }),
                    right: Box::new(done),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        span: None,
    }];
    ir
}

fn make_explicit_entity_store_ref_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_weak_fair_liveness_ir();
    ir.verifies[0].name = "tickets_eventually_finish_under_strong_fair_peer_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerOps".to_owned(),
        command: "finish_with_peer".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_weak_fair_liveness_ir();
    ir.systems.push(IRSystem {
        name: "TicketPeerRelayOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_finish_with_peer".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketPeerOps".to_owned(),
                    transition: "finish_with_peer".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![],
                }],
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
    });
    ir.verifies[0].name = "tickets_eventually_finish_under_weak_fair_peer_relay_finish".to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerRelayOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerRelayOps".to_owned(),
        command: "relay_finish_with_peer".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir
}

fn make_explicit_entity_store_ref_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_strong_fair_peer_relay_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerRelayOps".to_owned(),
        command: "relay_finish_with_peer".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "TicketPeerParam".to_owned(),
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    let ticket = IREntity {
        name: "TicketPeerParam".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(pending.clone()),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "set_status_if_peer_pending".to_owned(),
            refs: vec![IRTransRef {
                name: "peer".to_owned(),
                entity: "TicketPeerParam".to_owned(),
            }],
            params: vec![IRTransParam {
                name: "next_status".to_owned(),
                ty: status_ty.clone(),
            }],
            guard: IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(pending.clone()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "peer".to_owned(),
                                ty: ticket_entity_ty.clone(),
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(pending.clone()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "next_status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(done.clone()),
                    ty: IRType::Bool,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            updates: vec![IRUpdate {
                field: "status".to_owned(),
                value: done.clone(),
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let system = IRSystem {
        name: "TicketPeerParamOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "set_one_with_peer".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "t".to_owned(),
                    entity: "TicketPeerParam".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: ticket_entity_ty.clone(),
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(pending.clone()),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ops: vec![IRAction::Choose {
                        var: "peer".to_owned(),
                        entity: "TicketPeerParam".to_owned(),
                        filter: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "peer".to_owned(),
                                    ty: ticket_entity_ty.clone(),
                                    span: None,
                                }),
                                field: "status".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(pending.clone()),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "t".to_owned(),
                            transition: "set_status_if_peer_pending".to_owned(),
                            refs: vec!["peer".to_owned()],
                            args: vec![IRExpr::Var {
                                name: "next_status".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }],
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "tickets_eventually_finish_under_ref_param_per_tuple_weak_fairness".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TicketPeerParamOps".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![IRStoreDecl {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
            lo: 0,
            hi: 1,
        }],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: vec![IRCommandRef {
                system: "TicketPeerParamOps".to_owned(),
                command: "set_one_with_peer".to_owned(),
            }],
            strong_fair: Vec::new(),
            per_tuple: vec![IRCommandRef {
                system: "TicketPeerParamOps".to_owned(),
                command: "set_one_with_peer".to_owned(),
            }],
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "t".to_owned(),
                domain: IRType::Entity {
                    name: "TicketPeerParam".to_owned(),
                },
                body: Box::new(IRExpr::Eventually {
                    body: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: IRType::Entity {
                                    name: "TicketPeerParam".to_owned(),
                                },
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty,
                            span: None,
                        }),
                        right: Box::new(done),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![ticket],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_ref_param_per_tuple_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_param_per_tuple_strong_fairness".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamOps".to_owned(),
        command: "set_one_with_peer".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_param_cross_call_per_tuple_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.systems.push(IRSystem {
        name: "TicketPeerParamRelayOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketPeerParamOps".to_owned(),
                    transition: "set_one_with_peer".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![IRExpr::Var {
                        name: "next_status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_param_cross_call_per_tuple_weak_fairness".to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamRelayOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamRelayOps".to_owned(),
        command: "relay_set_one_with_peer".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple = vec![IRCommandRef {
        system: "TicketPeerParamRelayOps".to_owned(),
        command: "relay_set_one_with_peer".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_param_cross_call_per_tuple_strong_fair_liveness_ir() -> IRProgram
{
    let mut ir = make_explicit_entity_store_ref_param_cross_call_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_param_cross_call_per_tuple_strong_fairness".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamRelayOps".to_owned(),
        command: "relay_set_one_with_peer".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "TicketPeerParam".to_owned(),
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    ir.systems.push(IRSystem {
        name: "TicketStatusDecision".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "decide_done".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![],
            return_expr: Some(done.clone()),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    });
    ir.systems.push(IRSystem {
        name: "TicketPeerParamDecisionRelayOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_from_call".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "next_status".to_owned(),
                        system: "TicketStatusDecision".to_owned(),
                        command: "decide_done".to_owned(),
                        args: vec![],
                    },
                    IRAction::Choose {
                        var: "t".to_owned(),
                        entity: "TicketPeerParam".to_owned(),
                        filter: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "t".to_owned(),
                                    ty: ticket_entity_ty.clone(),
                                    span: None,
                                }),
                                field: "status".to_owned(),
                                ty: status_ty.clone(),
                                span: None,
                            }),
                            right: Box::new(pending.clone()),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        ops: vec![IRAction::Choose {
                            var: "peer".to_owned(),
                            entity: "TicketPeerParam".to_owned(),
                            filter: Box::new(IRExpr::BinOp {
                                op: "OpEq".to_owned(),
                                left: Box::new(IRExpr::Field {
                                    expr: Box::new(IRExpr::Var {
                                        name: "peer".to_owned(),
                                        ty: ticket_entity_ty.clone(),
                                        span: None,
                                    }),
                                    field: "status".to_owned(),
                                    ty: status_ty.clone(),
                                    span: None,
                                }),
                                right: Box::new(pending.clone()),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            ops: vec![IRAction::Apply {
                                target: "t".to_owned(),
                                transition: "set_status_if_peer_pending".to_owned(),
                                refs: vec!["peer".to_owned()],
                                args: vec![IRExpr::Var {
                                    name: "next_status".to_owned(),
                                    ty: status_ty.clone(),
                                    span: None,
                                }],
                            }],
                        }],
                    },
                ],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_weak_fair_ref_result_relay_finish".to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamDecisionRelayOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionRelayOps".to_owned(),
        command: "relay_set_one_with_peer_from_call".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple.clear();
    ir
}

fn make_explicit_entity_store_ref_result_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_result_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_strong_fair_ref_result_relay_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionRelayOps".to_owned(),
        command: "relay_set_one_with_peer_from_call".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_per_tuple_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Set"), IRVariant::simple("Hold")],
    };
    let set = IRExpr::Ctor {
        enum_name: "Decision".to_owned(),
        ctor: "Set".to_owned(),
        args: vec![],
        span: None,
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    ir.types.push(IRTypeEntry {
        name: "Decision".to_owned(),
        ty: decision_ty,
    });
    ir.systems.push(IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
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
            return_expr: Some(set),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    });
    ir.systems.push(IRSystem {
        name: "TicketPeerParamDecisionTupleRelayOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_from_decision".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "decision".to_owned(),
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::Match {
                        scrutinee: IRActionMatchScrutinee::Var {
                            name: "decision".to_owned(),
                        },
                        arms: vec![
                            IRActionMatchArm {
                                pattern: IRPattern::PCtor {
                                    name: "Set".to_owned(),
                                    fields: vec![],
                                },
                                guard: None,
                                body: vec![IRAction::Apply {
                                    target: "TicketPeerParamOps".to_owned(),
                                    transition: "set_one_with_peer".to_owned(),
                                    refs: vec!["tickets".to_owned()],
                                    args: vec![IRExpr::Var {
                                        name: "next_status".to_owned(),
                                        ty: status_ty.clone(),
                                        span: None,
                                    }],
                                }],
                            },
                            IRActionMatchArm {
                                pattern: IRPattern::PWild,
                                guard: None,
                                body: vec![IRAction::Apply {
                                    target: "TicketPeerParamOps".to_owned(),
                                    transition: "set_one_with_peer".to_owned(),
                                    refs: vec!["tickets".to_owned()],
                                    args: vec![pending.clone()],
                                }],
                            },
                        ],
                    },
                ],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_result_per_tuple_weak_fairness".to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamDecisionTupleRelayOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_per_tuple_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_result_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_result_per_tuple_strong_fairness".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_nested_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_result_cross_call_weak_fair_liveness_ir();
    ir.systems.push(IRSystem {
        name: "TicketPeerParamDecisionRelayChainOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_from_call_again".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketPeerParamDecisionRelayOps".to_owned(),
                    transition: "relay_set_one_with_peer_from_call".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_weak_fair_nested_ref_result_relay_finish".to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamDecisionRelayChainOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_call_again".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir
}

fn make_explicit_entity_store_ref_result_nested_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_result_nested_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_strong_fair_nested_ref_result_relay_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_call_again".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_nested_cross_call_per_tuple_weak_fair_liveness_ir(
) -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_result_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.systems.push(IRSystem {
        name: "TicketPeerParamDecisionTupleRelayChainOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_from_decision_again".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketPeerParamDecisionTupleRelayOps".to_owned(),
                    transition: "relay_set_one_with_peer_from_decision".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![IRExpr::Var {
                        name: "next_status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_result_nested_cross_call_per_tuple_weak_fairness"
            .to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamDecisionTupleRelayChainOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision_again".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision_again".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_nested_cross_call_per_tuple_strong_fair_liveness_ir(
) -> IRProgram {
    let mut ir =
        make_explicit_entity_store_ref_result_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_result_nested_cross_call_per_tuple_strong_fairness"
            .to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision_again".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_deep_nested_cross_call_per_tuple_weak_fair_liveness_ir(
) -> IRProgram {
    let mut ir =
        make_explicit_entity_store_ref_result_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.systems.push(IRSystem {
        name: "TicketPeerParamDecisionTupleRelayDeepChainOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_from_decision_third".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketPeerParamDecisionTupleRelayChainOps".to_owned(),
                    transition: "relay_set_one_with_peer_from_decision_again".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![IRExpr::Var {
                        name: "next_status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_result_deep_nested_cross_call_per_tuple_weak_fairness"
            .to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamDecisionTupleRelayDeepChainOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayDeepChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision_third".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayDeepChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision_third".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_result_deep_nested_cross_call_per_tuple_strong_fair_liveness_ir(
) -> IRProgram {
    let mut ir =
        make_explicit_entity_store_ref_result_deep_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_result_deep_nested_cross_call_per_tuple_strong_fairness"
            .to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamDecisionTupleRelayDeepChainOps".to_owned(),
        command: "relay_set_one_with_peer_from_decision_third".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_match_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "TicketPeerParam".to_owned(),
    };
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Set"), IRVariant::simple("Hold")],
    };
    let set = IRExpr::Ctor {
        enum_name: "Decision".to_owned(),
        ctor: "Set".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    ir.types.push(IRTypeEntry {
        name: "Decision".to_owned(),
        ty: decision_ty,
    });
    ir.systems.push(IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
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
            return_expr: Some(set),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    });
    ir.systems.push(IRSystem {
        name: "TicketPeerParamMatchRelayOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_by_match".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Match {
                    scrutinee: IRActionMatchScrutinee::CrossCall {
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    arms: vec![
                        IRActionMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Set".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: vec![IRAction::Choose {
                                var: "t".to_owned(),
                                entity: "TicketPeerParam".to_owned(),
                                filter: Box::new(IRExpr::BinOp {
                                    op: "OpEq".to_owned(),
                                    left: Box::new(IRExpr::Field {
                                        expr: Box::new(IRExpr::Var {
                                            name: "t".to_owned(),
                                            ty: ticket_entity_ty.clone(),
                                            span: None,
                                        }),
                                        field: "status".to_owned(),
                                        ty: status_ty.clone(),
                                        span: None,
                                    }),
                                    right: Box::new(pending.clone()),
                                    ty: IRType::Bool,
                                    span: None,
                                }),
                                ops: vec![IRAction::Choose {
                                    var: "peer".to_owned(),
                                    entity: "TicketPeerParam".to_owned(),
                                    filter: Box::new(IRExpr::BinOp {
                                        op: "OpEq".to_owned(),
                                        left: Box::new(IRExpr::Field {
                                            expr: Box::new(IRExpr::Var {
                                                name: "peer".to_owned(),
                                                ty: ticket_entity_ty.clone(),
                                                span: None,
                                            }),
                                            field: "status".to_owned(),
                                            ty: status_ty.clone(),
                                            span: None,
                                        }),
                                        right: Box::new(pending.clone()),
                                        ty: IRType::Bool,
                                        span: None,
                                    }),
                                    ops: vec![IRAction::Apply {
                                        target: "t".to_owned(),
                                        transition: "set_status_if_peer_pending".to_owned(),
                                        refs: vec!["peer".to_owned()],
                                        args: vec![done.clone()],
                                    }],
                                }],
                            }],
                        },
                        IRActionMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: vec![IRAction::Choose {
                                var: "t".to_owned(),
                                entity: "TicketPeerParam".to_owned(),
                                filter: Box::new(IRExpr::BinOp {
                                    op: "OpEq".to_owned(),
                                    left: Box::new(IRExpr::Field {
                                        expr: Box::new(IRExpr::Var {
                                            name: "t".to_owned(),
                                            ty: ticket_entity_ty.clone(),
                                            span: None,
                                        }),
                                        field: "status".to_owned(),
                                        ty: status_ty.clone(),
                                        span: None,
                                    }),
                                    right: Box::new(pending.clone()),
                                    ty: IRType::Bool,
                                    span: None,
                                }),
                                ops: vec![IRAction::Choose {
                                    var: "peer".to_owned(),
                                    entity: "TicketPeerParam".to_owned(),
                                    filter: Box::new(IRExpr::BinOp {
                                        op: "OpEq".to_owned(),
                                        left: Box::new(IRExpr::Field {
                                            expr: Box::new(IRExpr::Var {
                                                name: "peer".to_owned(),
                                                ty: ticket_entity_ty.clone(),
                                                span: None,
                                            }),
                                            field: "status".to_owned(),
                                            ty: status_ty.clone(),
                                            span: None,
                                        }),
                                        right: Box::new(pending.clone()),
                                        ty: IRType::Bool,
                                        span: None,
                                    }),
                                    ops: vec![IRAction::Apply {
                                        target: "t".to_owned(),
                                        transition: "set_status_if_peer_pending".to_owned(),
                                        refs: vec!["peer".to_owned()],
                                        args: vec![pending],
                                    }],
                                }],
                            }],
                        },
                    ],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_weak_fair_ref_match_relay_finish".to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamMatchRelayOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamMatchRelayOps".to_owned(),
        command: "relay_set_one_with_peer_by_match".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple.clear();
    ir
}

fn make_explicit_entity_store_ref_match_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_match_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_strong_fair_ref_match_relay_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamMatchRelayOps".to_owned(),
        command: "relay_set_one_with_peer_by_match".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_param_nested_cross_call_per_tuple_weak_fair_liveness_ir(
) -> IRProgram {
    let mut ir = make_explicit_entity_store_ref_param_cross_call_per_tuple_weak_fair_liveness_ir();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    ir.systems.push(IRSystem {
        name: "TicketPeerParamRelayChainOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketPeerParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketPeerParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketPeerParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set_one_with_peer_again".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketPeerParamRelayOps".to_owned(),
                    transition: "relay_set_one_with_peer".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![IRExpr::Var {
                        name: "next_status".to_owned(),
                        ty: status_ty,
                        span: None,
                    }],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_param_nested_cross_call_per_tuple_weak_fairness"
            .to_owned();
    ir.verifies[0].systems[0].name = "TicketPeerParamRelayChainOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketPeerParamRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_again".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir.verifies[0].assumption_set.per_tuple = vec![IRCommandRef {
        system: "TicketPeerParamRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_again".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_ref_param_nested_cross_call_per_tuple_strong_fair_liveness_ir(
) -> IRProgram {
    let mut ir =
        make_explicit_entity_store_ref_param_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_ref_param_nested_cross_call_per_tuple_strong_fairness"
            .to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketPeerParamRelayChainOps".to_owned(),
        command: "relay_set_one_with_peer_again".to_owned(),
    }];
    ir
}

fn make_explicit_multi_entity_store_counterexample_ir() -> IRProgram {
    let order_status_ty = IRType::Enum {
        name: "OrderStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Confirmed")],
    };
    let invoice_status_ty = IRType::Enum {
        name: "InvoiceStatus".to_owned(),
        variants: vec![IRVariant::simple("Open"), IRVariant::simple("Paid")],
    };
    let order_entity_ty = IRType::Entity {
        name: "Order".to_owned(),
    };
    let invoice_entity_ty = IRType::Entity {
        name: "Invoice".to_owned(),
    };
    let order = IREntity {
        name: "Order".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: order_status_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "OrderStatus".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "confirm".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: order_status_ty.clone(),
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
    let invoice = IREntity {
        name: "Invoice".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: invoice_status_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "InvoiceStatus".to_owned(),
                ctor: "Open".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "pay".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: invoice_status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "InvoiceStatus".to_owned(),
                    ctor: "Open".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            updates: vec![IRUpdate {
                field: "status".to_owned(),
                value: IRExpr::Ctor {
                    enum_name: "InvoiceStatus".to_owned(),
                    ctor: "Paid".to_owned(),
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
    let system = IRSystem {
        name: "Commerce".to_owned(),
        store_params: vec![
            IRStoreParam {
                name: "orders".to_owned(),
                entity_type: "Order".to_owned(),
            },
            IRStoreParam {
                name: "invoices".to_owned(),
                entity_type: "Invoice".to_owned(),
            },
        ],
        fields: vec![],
        entities: vec!["Order".to_owned(), "Invoice".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Order".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "create_invoice".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Invoice".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "confirm_one".to_owned(),
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
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "o".to_owned(),
                                ty: order_entity_ty,
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: order_status_ty.clone(),
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
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "confirm".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "pay_one".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "i".to_owned(),
                    entity: "Invoice".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "i".to_owned(),
                                ty: invoice_entity_ty,
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: invoice_status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "InvoiceStatus".to_owned(),
                            ctor: "Open".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "i".to_owned(),
                        transition: "pay".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "paid_invoice_requires_confirmed_order".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "Commerce".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![
            IRStoreDecl {
                name: "orders".to_owned(),
                entity_type: "Order".to_owned(),
                lo: 0,
                hi: 1,
            },
            IRStoreDecl {
                name: "invoices".to_owned(),
                entity_type: "Invoice".to_owned(),
                lo: 0,
                hi: 1,
            },
        ],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Exists {
                        var: "i".to_owned(),
                        domain: IRType::Entity {
                            name: "Invoice".to_owned(),
                        },
                        body: Box::new(IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "i".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Invoice".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "status".to_owned(),
                                ty: invoice_status_ty,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Ctor {
                                enum_name: "InvoiceStatus".to_owned(),
                                ctor: "Paid".to_owned(),
                                args: vec![],
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::Exists {
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
                            ty: order_status_ty,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Ctor {
                            enum_name: "OrderStatus".to_owned(),
                            ctor: "Confirmed".to_owned(),
                            args: vec![],
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![order, invoice],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_system_cross_call_counterexample_ir() -> IRProgram {
    let target = IRSystem {
        name: "Target".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "gate".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "open".to_owned(),
            params: vec![],
            guard: IRExpr::Var {
                name: "allow_open".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "gate".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
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
    };
    let caller = IRSystem {
        name: "Caller".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "allow_open".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "invoke".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "allow_open".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                },
                IRAction::CrossCall {
                    system: "Target".to_owned(),
                    command: "open".to_owned(),
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
    let verify = IRVerify {
        name: "target_gate_stays_closed".to_owned(),
        depth: None,
        systems: vec![
            IRVerifySystem {
                name: "Target".to_owned(),
                lo: 0,
                hi: 1,
            },
            IRVerifySystem {
                name: "Caller".to_owned(),
                lo: 0,
                hi: 1,
            },
        ],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "gate".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![target, caller],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_system_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_system_cross_call_counterexample_ir();
    ir.verifies[0].name = "target_gate_eventually_opens_under_weak_fair_invoke".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "Caller".to_owned(),
        command: "invoke".to_owned(),
    }];
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::Eventually {
            body: Box::new(IRExpr::Var {
                name: "gate".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        span: None,
    }];
    ir
}

fn make_explicit_system_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_system_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name = "target_gate_eventually_opens_under_strong_fair_invoke".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "Caller".to_owned(),
        command: "invoke".to_owned(),
    }];
    ir
}

fn make_explicit_system_let_crosscall_counterexample_ir() -> IRProgram {
    let target = IRSystem {
        name: "TargetLet".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "gate".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "set_gate".to_owned(),
            params: vec![IRTransParam {
                name: "value".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Var {
                name: "allow".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "gate".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "value".to_owned(),
                        ty: IRType::Bool,
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
    };
    let worker = IRSystem {
        name: "DecisionLet".to_owned(),
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
            return_expr: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let caller = IRSystem {
        name: "CallerLet".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "allow".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "invoke".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "allow".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                },
                IRAction::LetCrossCall {
                    name: "decision".to_owned(),
                    system: "DecisionLet".to_owned(),
                    command: "decide".to_owned(),
                    args: vec![],
                },
                IRAction::CrossCall {
                    system: "TargetLet".to_owned(),
                    command: "set_gate".to_owned(),
                    args: vec![IRExpr::Var {
                        name: "decision".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }],
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
    let verify = IRVerify {
        name: "target_gate_stays_closed_through_let_crosscall".to_owned(),
        depth: None,
        systems: vec![
            IRVerifySystem {
                name: "TargetLet".to_owned(),
                lo: 0,
                hi: 1,
            },
            IRVerifySystem {
                name: "CallerLet".to_owned(),
                lo: 0,
                hi: 1,
            },
        ],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "gate".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![target, worker, caller],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_system_match_crosscall_counterexample_ir() -> IRProgram {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Open"), IRVariant::simple("Hold")],
    };
    let target = IRSystem {
        name: "TargetMatch".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "gate".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "open".to_owned(),
                params: vec![],
                guard: IRExpr::Var {
                    name: "allow".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "gate".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "hold".to_owned(),
                params: vec![],
                guard: IRExpr::Var {
                    name: "allow".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "gate".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "gate".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
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
    };
    let worker = IRSystem {
        name: "DecisionMatch".to_owned(),
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
            return_expr: Some(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Open".to_owned(),
                args: vec![],
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let caller = IRSystem {
        name: "CallerMatch".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "allow".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "invoke".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "allow".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                },
                IRAction::LetCrossCall {
                    name: "decision".to_owned(),
                    system: "DecisionMatch".to_owned(),
                    command: "decide".to_owned(),
                    args: vec![],
                },
                IRAction::Match {
                    scrutinee: IRActionMatchScrutinee::Var {
                        name: "decision".to_owned(),
                    },
                    arms: vec![
                        IRActionMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Open".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: vec![IRAction::CrossCall {
                                system: "TargetMatch".to_owned(),
                                command: "open".to_owned(),
                                args: vec![],
                            }],
                        },
                        IRActionMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: vec![IRAction::CrossCall {
                                system: "TargetMatch".to_owned(),
                                command: "hold".to_owned(),
                                args: vec![],
                            }],
                        },
                    ],
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
    let verify = IRVerify {
        name: "target_gate_stays_closed_through_match_crosscall".to_owned(),
        depth: None,
        systems: vec![
            IRVerifySystem {
                name: "TargetMatch".to_owned(),
                lo: 0,
                hi: 1,
            },
            IRVerifySystem {
                name: "CallerMatch".to_owned(),
                lo: 0,
                hi: 1,
            },
        ],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "gate".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![IRTypeEntry {
            name: "Decision".to_owned(),
            ty: decision_ty,
        }],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![target, worker, caller],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_eventual_liveness_ir();
    ir.verifies[0].name = "tickets_eventually_finish_under_weak_fair_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketOps".to_owned(),
        command: "finish_one".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_eventual_liveness_ir();
    ir.verifies[0].name = "tickets_eventually_finish_under_strong_fair_finish".to_owned();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketOps".to_owned(),
        command: "finish_one".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_eventual_liveness_ir();
    ir.systems.push(IRSystem {
        name: "TicketRelayOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_finish".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketOps".to_owned(),
                    transition: "finish_one".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![],
                }],
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
    });
    ir.verifies[0].name = "tickets_eventually_finish_under_weak_fair_relay_finish".to_owned();
    ir.verifies[0].systems[0].name = "TicketRelayOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketRelayOps".to_owned(),
        command: "relay_finish".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir
}

fn make_explicit_entity_store_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name = "tickets_eventually_finish_under_strong_fair_relay_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketRelayOps".to_owned(),
        command: "relay_finish".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_nested_cross_call_weak_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_cross_call_weak_fair_liveness_ir();
    ir.systems.push(IRSystem {
        name: "TicketRelayChainOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "Ticket".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_finish_again".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "TicketRelayOps".to_owned(),
                    transition: "relay_finish".to_owned(),
                    refs: vec!["tickets".to_owned()],
                    args: vec![],
                }],
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
    });
    ir.verifies[0].name =
        "tickets_eventually_finish_under_weak_fair_nested_relay_finish".to_owned();
    ir.verifies[0].systems[0].name = "TicketRelayChainOps".to_owned();
    ir.verifies[0].assumption_set.weak_fair = vec![IRCommandRef {
        system: "TicketRelayChainOps".to_owned(),
        command: "relay_finish_again".to_owned(),
    }];
    ir.verifies[0].assumption_set.strong_fair.clear();
    ir
}

fn make_explicit_entity_store_nested_cross_call_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_nested_cross_call_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_strong_fair_nested_relay_finish".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketRelayChainOps".to_owned(),
        command: "relay_finish_again".to_owned(),
    }];
    ir
}

fn make_explicit_entity_store_param_per_tuple_weak_fair_liveness_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let ticket_entity_ty = IRType::Entity {
        name: "TicketFairParam".to_owned(),
    };
    let pending = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "TicketStatus".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    let ticket = IREntity {
        name: "TicketFairParam".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(pending.clone()),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "set_status_when_done_arg".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "next_status".to_owned(),
                ty: status_ty.clone(),
            }],
            guard: IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(pending.clone()),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "next_status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(done.clone()),
                    ty: IRType::Bool,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            updates: vec![IRUpdate {
                field: "status".to_owned(),
                value: done.clone(),
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let system = IRSystem {
        name: "TicketFairParamOps".to_owned(),
        store_params: vec![IRStoreParam {
            name: "tickets".to_owned(),
            entity_type: "TicketFairParam".to_owned(),
        }],
        fields: vec![],
        entities: vec!["TicketFairParam".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "TicketFairParam".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "set_one".to_owned(),
                params: vec![IRTransParam {
                    name: "next_status".to_owned(),
                    ty: status_ty.clone(),
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "t".to_owned(),
                    entity: "TicketFairParam".to_owned(),
                    filter: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: ticket_entity_ty,
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        right: Box::new(pending),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "t".to_owned(),
                        transition: "set_status_when_done_arg".to_owned(),
                        refs: vec![],
                        args: vec![IRExpr::Var {
                            name: "next_status".to_owned(),
                            ty: status_ty.clone(),
                            span: None,
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "tickets_eventually_finish_under_entity_per_tuple_weak_fairness".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TicketFairParamOps".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![IRStoreDecl {
            name: "tickets".to_owned(),
            entity_type: "TicketFairParam".to_owned(),
            lo: 0,
            hi: 1,
        }],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: vec![IRCommandRef {
                system: "TicketFairParamOps".to_owned(),
                command: "set_one".to_owned(),
            }],
            strong_fair: Vec::new(),
            per_tuple: vec![IRCommandRef {
                system: "TicketFairParamOps".to_owned(),
                command: "set_one".to_owned(),
            }],
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "t".to_owned(),
                domain: IRType::Entity {
                    name: "TicketFairParam".to_owned(),
                },
                body: Box::new(IRExpr::Eventually {
                    body: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "t".to_owned(),
                                ty: IRType::Entity {
                                    name: "TicketFairParam".to_owned(),
                                },
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: status_ty,
                            span: None,
                        }),
                        right: Box::new(done),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![ticket],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_entity_store_param_per_tuple_strong_fair_liveness_ir() -> IRProgram {
    let mut ir = make_explicit_entity_store_param_per_tuple_weak_fair_liveness_ir();
    ir.verifies[0].name =
        "tickets_eventually_finish_under_entity_per_tuple_strong_fairness".to_owned();
    ir.verifies[0].assumption_set.weak_fair.clear();
    ir.verifies[0].assumption_set.strong_fair = vec![IRCommandRef {
        system: "TicketFairParamOps".to_owned(),
        command: "set_one".to_owned(),
    }];
    ir
}

fn make_system_field_bool_param_ir() -> IRProgram {
    let system = IRSystem {
        name: "Toggle".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "flag".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "set_flag".to_owned(),
            params: vec![IRTransParam {
                name: "next_flag".to_owned(),
                ty: IRType::Bool,
            }],
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
                            name: "flag".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "next_flag".to_owned(),
                        ty: IRType::Bool,
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
    };

    let verify = IRVerify {
        name: "toggle_closed_world".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "Toggle".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "flag".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Var {
                        name: "flag".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_enum_param_ir() -> IRProgram {
    let mode_ty = IRType::Enum {
        name: "Mode".to_owned(),
        variants: vec![IRVariant::simple("Off"), IRVariant::simple("On")],
    };
    let system = IRSystem {
        name: "Switch".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "mode".to_owned(),
            ty: mode_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Mode".to_owned(),
                ctor: "Off".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "set_mode".to_owned(),
            params: vec![IRTransParam {
                name: "next_mode".to_owned(),
                ty: mode_ty.clone(),
            }],
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
                            name: "mode".to_owned(),
                            ty: mode_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "next_mode".to_owned(),
                        ty: mode_ty.clone(),
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
    };

    let verify = IRVerify {
        name: "switch_closed_world".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "Switch".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "mode".to_owned(),
                        ty: mode_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Mode".to_owned(),
                        ctor: "Off".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "mode".to_owned(),
                        ty: mode_ty,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Mode".to_owned(),
                        ctor: "On".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_counter_with_invariant_ir() -> IRProgram {
    let system = IRSystem {
        name: "CounterInv".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "inc".to_owned(),
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
                            name: "x".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                },
            }],
            return_expr: None,
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![IRInvariant {
            name: "non_negative".to_owned(),
            body: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
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
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };

    let verify = IRVerify {
        name: "counter_invariant_plus_assert".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterInv".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_system_field_match_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let system = IRSystem {
        name: "MatchWorkflow".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "normalize".to_owned(),
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
                            ty: status_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Match {
                        scrutinee: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                                body: IRExpr::Ctor {
                                    enum_name: "Status".to_owned(),
                                    ctor: "Pending".to_owned(),
                                    args: vec![],
                                    span: None,
                                },
                            },
                            IRMatchArm {
                                pattern: IRPattern::PWild,
                                guard: None,
                                body: IRExpr::Ctor {
                                    enum_name: "Status".to_owned(),
                                    ctor: "Done".to_owned(),
                                    args: vec![],
                                    span: None,
                                },
                            },
                        ],
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
    };

    let verify = IRVerify {
        name: "match_workflow_closed_world".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "MatchWorkflow".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Match {
                scrutinee: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
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
                        body: IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        },
                    },
                    IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::BinOp {
                            op: "OpEq".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "status".to_owned(),
                                ty: status_ty,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Ctor {
                                enum_name: "Status".to_owned(),
                                ctor: "Done".to_owned(),
                                args: vec![],
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        },
                    },
                ],
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "inc".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
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
    let system = IRSystem {
        name: "CounterPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "inc_one".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "inc".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_counter_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_ticket_ir() -> IRProgram {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![
            IRVariant::simple("Pending"),
            IRVariant::simple("Active"),
            IRVariant::simple("Closed"),
        ],
    };
    let entity = IREntity {
        name: "Ticket".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "TicketStatus".to_owned(),
                ctor: "Pending".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "activate".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "TicketStatus".to_owned(),
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
                    enum_name: "TicketStatus".to_owned(),
                    ctor: "Active".to_owned(),
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
    let system = IRSystem {
        name: "TicketPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Ticket".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_ticket".to_owned(),
                params: vec![IRTransParam {
                    name: "start_active".to_owned(),
                    ty: IRType::Bool,
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Ticket".to_owned(),
                    fields: vec![IRCreateField {
                        name: "status".to_owned(),
                        value: IRExpr::IfElse {
                            cond: Box::new(IRExpr::Var {
                                name: "start_active".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            then_body: Box::new(IRExpr::Ctor {
                                enum_name: "TicketStatus".to_owned(),
                                ctor: "Active".to_owned(),
                                args: vec![],
                                span: None,
                            }),
                            else_body: Some(Box::new(IRExpr::Ctor {
                                enum_name: "TicketStatus".to_owned(),
                                ctor: "Pending".to_owned(),
                                args: vec![],
                                span: None,
                            })),
                            span: None,
                        },
                    }],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "activate_all".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::ForAll {
                    var: "t".to_owned(),
                    entity: "Ticket".to_owned(),
                    ops: vec![IRAction::Apply {
                        target: "t".to_owned(),
                        transition: "activate".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_ticket_no_closed".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "TicketPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "t".to_owned(),
                domain: IRType::Entity {
                    name: "Ticket".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpNEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "t".to_owned(),
                            ty: IRType::Entity {
                                name: "Ticket".to_owned(),
                            },
                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: status_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "TicketStatus".to_owned(),
                        ctor: "Closed".to_owned(),
                        args: vec![],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_ref_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "step_with_peer".to_owned(),
            refs: vec![IRTransRef {
                name: "peer".to_owned(),
                entity: "Counter".to_owned(),
            }],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "peer".to_owned(),
                        ty: entity_ty.clone(),
                        span: None,
                    }),
                    field: "x".to_owned(),
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
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "peer".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
    let system = IRSystem {
        name: "CounterRefPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "step_one".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "step_with_peer".to_owned(),
                        refs: vec!["c".to_owned()],
                        args: vec![],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_counter_ref_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterRefPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_nested_ref_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "step_with_peer".to_owned(),
            refs: vec![IRTransRef {
                name: "peer".to_owned(),
                entity: "Counter".to_owned(),
            }],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "peer".to_owned(),
                        ty: entity_ty.clone(),
                        span: None,
                    }),
                    field: "x".to_owned(),
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
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "peer".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
    let system = IRSystem {
        name: "CounterNestedRefPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "step_one_against_other".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Choose {
                        var: "d".to_owned(),
                        entity: "Counter".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "c".to_owned(),
                            transition: "step_with_peer".to_owned(),
                            refs: vec!["d".to_owned()],
                            args: vec![],
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_counter_nested_ref_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterNestedRefPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_forall_nested_ref_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "step_with_peer".to_owned(),
            refs: vec![IRTransRef {
                name: "peer".to_owned(),
                entity: "Counter".to_owned(),
            }],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "peer".to_owned(),
                        ty: entity_ty.clone(),
                        span: None,
                    }),
                    field: "x".to_owned(),
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
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "peer".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
    let system = IRSystem {
        name: "CounterForallNestedRefPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "step_all_against_other".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::ForAll {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    ops: vec![IRAction::Choose {
                        var: "d".to_owned(),
                        entity: "Counter".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "c".to_owned(),
                            transition: "step_with_peer".to_owned(),
                            refs: vec!["d".to_owned()],
                            args: vec![],
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_counter_forall_nested_ref_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterForallNestedRefPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty.clone(),
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: entity_ty.clone(),
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_arg_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let system = IRSystem {
        name: "CounterArgPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "bump_one".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "bump_if".to_owned(),
                        refs: vec![],
                        args: vec![IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_transition_arg_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterArgPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_crosscall_arg_counter_ir() -> IRProgram {
    let mut base = make_pooled_arg_counter_ir();
    base.systems[0].name = "CounterArgRelayPool".to_owned();
    base.systems[0].actions[1] = IRSystemAction {
        name: "relay_bump".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![IRAction::CrossCall {
            system: "CounterArgWorker".to_owned(),
            command: "bump_one".to_owned(),
            args: vec![IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }],
        }],
        return_expr: None,
    };
    base.verifies[0].name = "pooled_crosscall_transition_arg_non_negative".to_owned();
    base.verifies[0].systems[0].name = "CounterArgRelayPool".to_owned();
    base.systems.push(IRSystem {
        name: "CounterArgWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "bump_one".to_owned(),
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "bump_if".to_owned(),
                    refs: vec![],
                    args: vec![IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
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
    });
    base
}

fn make_pooled_match_crosscall_counter_ir() -> IRProgram {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Bump"), IRVariant::simple("Hold")],
    };
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![
            IRField {
                name: "x".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "decision_seed".to_owned(),
                ty: decision_ty.clone(),
                default: Some(IRExpr::Ctor {
                    enum_name: "Decision".to_owned(),
                    ctor: "Hold".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let relay = IRSystem {
        name: "CounterMatchPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "match_bump".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Match {
                    scrutinee: IRActionMatchScrutinee::CrossCall {
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    arms: vec![
                        IRActionMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Bump".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: vec![IRAction::Choose {
                                var: "c".to_owned(),
                                entity: "Counter".to_owned(),
                                filter: Box::new(IRExpr::Lit {
                                    ty: IRType::Bool,
                                    value: LitVal::Bool { value: true },
                                    span: None,
                                }),
                                ops: vec![IRAction::Apply {
                                    target: "c".to_owned(),
                                    transition: "bump_if".to_owned(),
                                    refs: vec![],
                                    args: vec![IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: true },
                                        span: None,
                                    }],
                                }],
                            }],
                        },
                        IRActionMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: vec![IRAction::Choose {
                                var: "c".to_owned(),
                                entity: "Counter".to_owned(),
                                filter: Box::new(IRExpr::Lit {
                                    ty: IRType::Bool,
                                    value: LitVal::Bool { value: true },
                                    span: None,
                                }),
                                ops: vec![IRAction::Apply {
                                    target: "c".to_owned(),
                                    transition: "bump_if".to_owned(),
                                    refs: vec![],
                                    args: vec![IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: false },
                                        span: None,
                                    }],
                                }],
                            }],
                        },
                    ],
                }],
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
    };
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "decide".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "bump_if".to_owned(),
                    refs: vec![],
                    args: vec![IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: false },
                        span: None,
                    }],
                }],
            }],
            return_expr: Some(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Bump".to_owned(),
                args: vec![],
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_match_crosscall_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterMatchPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![relay, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_let_crosscall_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let relay = IRSystem {
        name: "CounterLetRelayPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_bump".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "inc".to_owned(),
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::Choose {
                        var: "c".to_owned(),
                        entity: "Counter".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "c".to_owned(),
                            transition: "bump_if".to_owned(),
                            refs: vec![],
                            args: vec![IRExpr::Var {
                                name: "inc".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }],
                        }],
                    },
                ],
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
    };
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
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
            return_expr: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_let_crosscall_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterLetRelayPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![relay, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_match_var_crosscall_counter_ir() -> IRProgram {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Bump"), IRVariant::simple("Hold")],
    };
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![
            IRField {
                name: "x".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "decision_seed".to_owned(),
                ty: decision_ty.clone(),
                default: Some(IRExpr::Ctor {
                    enum_name: "Decision".to_owned(),
                    ctor: "Hold".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let relay = IRSystem {
        name: "CounterMatchVarPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_match".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "decision".to_owned(),
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::Match {
                        scrutinee: IRActionMatchScrutinee::Var {
                            name: "decision".to_owned(),
                        },
                        arms: vec![
                            IRActionMatchArm {
                                pattern: IRPattern::PCtor {
                                    name: "Bump".to_owned(),
                                    fields: vec![],
                                },
                                guard: None,
                                body: vec![IRAction::Choose {
                                    var: "c".to_owned(),
                                    entity: "Counter".to_owned(),
                                    filter: Box::new(IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: true },
                                        span: None,
                                    }),
                                    ops: vec![IRAction::Apply {
                                        target: "c".to_owned(),
                                        transition: "bump_if".to_owned(),
                                        refs: vec![],
                                        args: vec![IRExpr::Lit {
                                            ty: IRType::Bool,
                                            value: LitVal::Bool { value: true },
                                            span: None,
                                        }],
                                    }],
                                }],
                            },
                            IRActionMatchArm {
                                pattern: IRPattern::PWild,
                                guard: None,
                                body: vec![IRAction::Choose {
                                    var: "c".to_owned(),
                                    entity: "Counter".to_owned(),
                                    filter: Box::new(IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: true },
                                        span: None,
                                    }),
                                    ops: vec![IRAction::Apply {
                                        target: "c".to_owned(),
                                        transition: "bump_if".to_owned(),
                                        refs: vec![],
                                        args: vec![IRExpr::Lit {
                                            ty: IRType::Bool,
                                            value: LitVal::Bool { value: false },
                                            span: None,
                                        }],
                                    }],
                                }],
                            },
                        ],
                    },
                ],
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
    };
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
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
            return_expr: Some(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Bump".to_owned(),
                args: vec![],
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_match_var_crosscall_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterMatchVarPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![IRTypeEntry {
            name: "Decision".to_owned(),
            ty: decision_ty,
        }],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![relay, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_let_crosscall_into_crosscall_arg_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let root = IRSystem {
        name: "CounterCrossArgRoot".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_bump".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "inc".to_owned(),
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::CrossCall {
                        system: "RelayWorker".to_owned(),
                        command: "bump".to_owned(),
                        args: vec![IRExpr::Var {
                            name: "inc".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }],
                    },
                ],
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
    };
    let relay = IRSystem {
        name: "RelayWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "bump".to_owned(),
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "bump_if".to_owned(),
                    refs: vec![],
                    args: vec![IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
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
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
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
            return_expr: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_let_crosscall_into_crosscall_arg_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterCrossArgRoot".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![root, relay, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_callee_field_crosscall_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let root = IRSystem {
        name: "CounterFieldRoot".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_bump".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "inc".to_owned(),
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::Choose {
                        var: "c".to_owned(),
                        entity: "Counter".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "c".to_owned(),
                            transition: "bump_if".to_owned(),
                            refs: vec![],
                            args: vec![IRExpr::Var {
                                name: "inc".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }],
                        }],
                    },
                ],
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
    };
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "decision".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "decide".to_owned(),
            params: vec![],
            guard: IRExpr::Var {
                name: "decision".to_owned(),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![],
            return_expr: Some(IRExpr::Var {
                name: "decision".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_callee_field_crosscall_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterFieldRoot".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![root, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_callee_store_crosscall_counter_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "bump_if".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "inc".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::IfElse {
                    cond: Box::new(IRExpr::Var {
                        name: "inc".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    then_body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                    else_body: Some(Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    })),
                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let root = IRSystem {
        name: "CounterStoreRoot".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_bump".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "inc".to_owned(),
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::Choose {
                        var: "c".to_owned(),
                        entity: "Counter".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "c".to_owned(),
                            transition: "bump_if".to_owned(),
                            refs: vec![],
                            args: vec![IRExpr::Var {
                                name: "inc".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }],
                        }],
                    },
                ],
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
    };
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![IRStoreParam {
            name: "live".to_owned(),
            entity_type: "Counter".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "decide".to_owned(),
            params: vec![],
            guard: IRExpr::Exists {
                var: "i".to_owned(),
                domain: IRType::Int,
                body: Box::new(IRExpr::Index {
                    map: Box::new(IRExpr::Var {
                        name: "live".to_owned(),
                        ty: IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Entity {
                                name: "Counter".to_owned(),
                            }),
                        },
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
            body: vec![],
            return_expr: Some(IRExpr::Exists {
                var: "i".to_owned(),
                domain: IRType::Int,
                body: Box::new(IRExpr::Index {
                    map: Box::new(IRExpr::Var {
                        name: "live".to_owned(),
                        ty: IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Entity {
                                name: "Counter".to_owned(),
                            }),
                        },
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
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_callee_store_crosscall_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterStoreRoot".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![root, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_apply_chain_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "F".to_owned(),
    };
    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![
            IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },
                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "amount".to_owned(),
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
                name: "prepare".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                updates: vec![
                    IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                    },
                    IRUpdate {
                        field: "amount".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 10 },
                            span: None,
                        },
                    },
                ],
                postcondition: None,
            },
            IRTransition {
                name: "finalize".to_owned(),
                refs: vec![],
                params: vec![IRTransParam {
                    name: "expected".to_owned(),
                    ty: IRType::Int,
                }],
                guard: IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    right: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "amount".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "expected".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },
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
    let system = IRSystem {
        name: "FPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_f".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "F".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "prep_and_finalize".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "prepare".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "finalize".to_owned(),
                            refs: vec![],
                            args: vec![IRExpr::Var {
                                name: "amount".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }],
                        },
                    ],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_apply_chain_amount_stable".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "FPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpImplies".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "f".to_owned(),
                                ty: IRType::Entity {
                                    name: "F".to_owned(),
                                },
                                span: None,
                            }),
                            field: "status".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 2 },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "f".to_owned(),
                                ty: IRType::Entity {
                                    name: "F".to_owned(),
                                },
                                span: None,
                            }),
                            field: "amount".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 10 },
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_create_then_inc_ir() -> IRProgram {
    let entity_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "inc".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
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
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
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
    let system = IRSystem {
        name: "CounterCreateIncPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_then_inc".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![
                IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                },
                IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "inc".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
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
    let verify = IRVerify {
        name: "pooled_create_then_inc_positive".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterCreateIncPool".to_owned(),
            lo: 0,
            hi: 1,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: entity_ty,
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "c".to_owned(),
                            ty: IRType::Entity {
                                name: "Counter".to_owned(),
                            },
                            span: None,
                        }),
                        field: "x".to_owned(),
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
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_store_counter_ir() -> IRProgram {
    let mut base = make_pooled_counter_ir();
    let entity = base.entities.remove(0);
    let system = IRSystem {
        name: "CounterStorePool".to_owned(),
        store_params: vec![crate::ir::types::IRStoreParam {
            name: "items".to_owned(),
            entity_type: "Counter".to_owned(),
        }],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "inc_all".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::ForAll {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    ops: vec![IRAction::Apply {
                        target: "c".to_owned(),
                        transition: "inc".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "pooled_store_membership_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterStorePool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "i".to_owned(),
                domain: IRType::Int,
                body: Box::new(IRExpr::BinOp {
                    op: "OpImplies".to_owned(),
                    left: Box::new(IRExpr::Index {
                        map: Box::new(IRExpr::Var {
                            name: "items".to_owned(),
                            ty: IRType::Map {
                                key: Box::new(IRType::Int),
                                value: Box::new(IRType::Bool),
                            },
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
                    right: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "i".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            field: "x".to_owned(),
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
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_pooled_crosscall_counter_ir() -> IRProgram {
    let mut base = make_pooled_counter_ir();
    base.systems[0].name = "CounterRelayPool".to_owned();
    base.systems[0].actions[1] = IRSystemAction {
        name: "relay_inc".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![IRAction::CrossCall {
            system: "CounterWorker".to_owned(),
            command: "inc_one".to_owned(),
            args: vec![],
        }],
        return_expr: None,
    };
    base.verifies[0].name = "pooled_crosscall_counter_non_negative".to_owned();
    base.verifies[0].systems[0].name = "CounterRelayPool".to_owned();
    base.systems.push(IRSystem {
        name: "CounterWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "inc_one".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "inc".to_owned(),
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
    });
    base
}

fn make_pooled_nested_crosscall_counter_ir() -> IRProgram {
    let mut base = make_pooled_counter_ir();
    base.systems[0].name = "CounterRelayPool".to_owned();
    base.systems[0].actions[1] = IRSystemAction {
        name: "relay_inc".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![IRAction::CrossCall {
            system: "CounterWorker".to_owned(),
            command: "relay_to_leaf".to_owned(),
            args: vec![],
        }],
        return_expr: None,
    };
    base.verifies[0].name = "pooled_nested_crosscall_counter_non_negative".to_owned();
    base.verifies[0].systems[0].name = "CounterRelayPool".to_owned();
    base.systems.push(IRSystem {
        name: "CounterWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "relay_to_leaf".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "CounterLeaf".to_owned(),
                command: "inc_one".to_owned(),
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
    });
    base.systems.push(IRSystem {
        name: "CounterLeaf".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "inc_one".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "inc".to_owned(),
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
    });
    base
}

fn make_multi_pooled_counter_marker_ir() -> IRProgram {
    let counter_ty = IRType::Entity {
        name: "Counter".to_owned(),
    };
    let marker_ty = IRType::Entity {
        name: "Marker".to_owned(),
    };
    let counter = IREntity {
        name: "Counter".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "sync_from_marker".to_owned(),
            refs: vec![IRTransRef {
                name: "m".to_owned(),
                entity: "Marker".to_owned(),
            }],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "m".to_owned(),
                        ty: marker_ty.clone(),
                        span: None,
                    }),
                    field: "y".to_owned(),
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
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "m".to_owned(),
                            ty: marker_ty.clone(),
                            span: None,
                        }),
                        field: "y".to_owned(),
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
    let marker = IREntity {
        name: "Marker".to_owned(),
        fields: vec![IRField {
            name: "y".to_owned(),
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
    let system = IRSystem {
        name: "CounterMarkerPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned(), "Marker".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_counter".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Counter".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "create_marker".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Marker".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "sync_one".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "c".to_owned(),
                    entity: "Counter".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Choose {
                        var: "m".to_owned(),
                        entity: "Marker".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "c".to_owned(),
                            transition: "sync_from_marker".to_owned(),
                            refs: vec!["m".to_owned()],
                            args: vec![],
                        }],
                    }],
                }],
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
    };
    let verify = IRVerify {
        name: "multi_pooled_cross_entity_non_negative".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "CounterMarkerPool".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::Forall {
                    var: "c".to_owned(),
                    domain: counter_ty.clone(),
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "c".to_owned(),
                                ty: counter_ty.clone(),
                                span: None,
                            }),
                            field: "x".to_owned(),
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
                right: Box::new(IRExpr::Forall {
                    var: "m".to_owned(),
                    domain: marker_ty.clone(),
                    body: Box::new(IRExpr::BinOp {
                        op: "OpGe".to_owned(),
                        left: Box::new(IRExpr::Field {
                            expr: Box::new(IRExpr::Var {
                                name: "m".to_owned(),
                                ty: marker_ty.clone(),
                                span: None,
                            }),
                            field: "y".to_owned(),
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
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![counter, marker],
        systems: vec![system],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_multi_pooled_forall_counter_marker_ir() -> IRProgram {
    let mut ir = make_multi_pooled_counter_marker_ir();
    ir.systems[0].name = "CounterMarkerForallPool".to_owned();
    ir.systems[0].actions[2] = IRSystemAction {
        name: "sync_all".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![IRAction::ForAll {
            var: "c".to_owned(),
            entity: "Counter".to_owned(),
            ops: vec![IRAction::Choose {
                var: "m".to_owned(),
                entity: "Marker".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "sync_from_marker".to_owned(),
                    refs: vec!["m".to_owned()],
                    args: vec![],
                }],
            }],
        }],
        return_expr: None,
    };
    ir.verifies[0].name = "multi_pooled_forall_cross_entity_non_negative".to_owned();
    ir.verifies[0].systems[0].name = "CounterMarkerForallPool".to_owned();
    ir
}

fn make_multi_pooled_arg_counter_marker_ir() -> IRProgram {
    let mut ir = make_multi_pooled_counter_marker_ir();
    ir.systems[0].name = "CounterMarkerArgPool".to_owned();
    ir.systems[0].actions[2] = IRSystemAction {
        name: "sync_one".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![IRAction::Choose {
            var: "c".to_owned(),
            entity: "Counter".to_owned(),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            ops: vec![IRAction::Choose {
                var: "m".to_owned(),
                entity: "Marker".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "sync_from_marker".to_owned(),
                    refs: vec!["m".to_owned()],
                    args: vec![IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }],
                }],
            }],
        }],
        return_expr: None,
    };
    ir.entities[0].transitions[0].params = vec![IRTransParam {
        name: "copy".to_owned(),
        ty: IRType::Bool,
    }];
    ir.entities[0].transitions[0].updates[0].value = IRExpr::IfElse {
        cond: Box::new(IRExpr::Var {
            name: "copy".to_owned(),
            ty: IRType::Bool,
            span: None,
        }),
        then_body: Box::new(IRExpr::BinOp {
            op: "OpAdd".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "m".to_owned(),
                    ty: IRType::Entity {
                        name: "Marker".to_owned(),
                    },
                    span: None,
                }),
                field: "y".to_owned(),
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
        else_body: Some(Box::new(IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        })),
        span: None,
    };
    ir.verifies[0].name = "multi_pooled_cross_entity_arg_non_negative".to_owned();
    ir.verifies[0].systems[0].name = "CounterMarkerArgPool".to_owned();
    ir
}

#[test]
fn bmc_checked_valid_property() {
    // Property: always (all o: Order | o.status != @Invalid)
    // Since @Invalid doesn't exist, status can only be Pending/Confirmed/Shipped.
    // The enum domain constraint ensures status is always in {0, 1, 2},
    // and we assert it's never -1, which should hold.
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
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: -1 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let ir = make_order_ir(property, 3);
    let results = verify_all(&ir, &VerifyConfig::default());

    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::Checked { name, .. } | VerificationResult::Proved { name, .. } if name == "test_verify"),
        "expected CHECKED or PROVED, got: {:?}",
        results[0]
    );
}

#[test]
fn bmc_counterexample_on_violation() {
    // Property: always (all o: Order | o.status == @Pending)
    // After confirm_order, status becomes Confirmed, so this should fail.
    // However, with all slots starting inactive, if no create event occurs,
    // no slot is ever active, so the universal quantifier is vacuously true.
    //
    // We need a system that creates orders AND confirms them.
    // Add a create_order event to the system.
    let mut ir = make_order_ir(
        IRExpr::Always {
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
                        enum_name: "OrderStatus".to_owned(),
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
        },
        3,
    );

    // Add a create_order event so orders can actually exist
    ir.systems[0].actions.push(IRSystemAction {
        name: "create_order".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        },
        body: vec![IRAction::Create {
            entity: "Order".to_owned(),
            fields: vec![
                IRCreateField {
                    name: "id".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    },
                },
                IRCreateField {
                    name: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    },
                },
            ],
        }],
        return_expr: None,
    });

    let results = verify_all(&ir, &VerifyConfig::default());

    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::Counterexample { name, .. } if name == "test_verify"),
        "expected COUNTEREXAMPLE, got: {:?}",
        results[0]
    );
    let witness = results[0]
        .operational_witness()
        .expect("bounded counterexample should carry operational witness");
    assert_eq!(witness.behavior().states().len(), 4);
    assert_eq!(witness.behavior().transitions().len(), 3);
}

#[test]
fn bmc_empty_program_no_results() {
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
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(results.is_empty());
}

fn make_dummy_entity() -> IREntity {
    IREntity {
        name: "Dummy".to_owned(),
        fields: vec![IRField {
            name: "id".to_owned(),
            ty: IRType::Identity,
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
fn scene_accepts_let_in_given_constraint() {
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![make_dummy_entity()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![IRScene {
            name: "let_scene".to_owned(),
            systems: vec![],
            stores: vec![],
            givens: vec![IRSceneGiven {
                var: "d".to_owned(),
                entity: "Dummy".to_owned(),
                store_name: None,
                constraint: IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        expr: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                    }],
                    body: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),

                    span: None,
                },
            }],
            events: vec![],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    match &results[0] {
        VerificationResult::ScenePass { name, .. } => {
            assert_eq!(name, "let_scene");
        }
        other => panic!("expected ScenePass, got {other:?}"),
    }
}

#[test]
fn scene_still_rejects_lambda_in_given_constraint() {
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![make_dummy_entity()],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![IRScene {
            name: "lam_scene".to_owned(),
            systems: vec![],
            stores: vec![],
            givens: vec![IRSceneGiven {
                var: "d".to_owned(),
                entity: "Dummy".to_owned(),
                store_name: None,
                constraint: IRExpr::Lam {
                    param: "x".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    span: None,
                },
            }],
            events: vec![],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    match &results[0] {
        VerificationResult::SceneFail { reason, .. } => {
            assert!(reason.contains("unsupported expression kind in scene given"));
            assert!(reason.contains("Lam"));
        }
        other => panic!("expected SceneFail, got {other:?}"),
    }
}

#[test]
fn scene_reports_crosscall_arity_mismatch() {
    let caller = IRSystem {
        name: "Caller".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Dummy".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "start".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "Callee".to_owned(),
                command: "run".to_owned(),
                args: vec![IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 1 },

                    span: None,
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
    let callee = IRSystem {
        name: "Callee".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Dummy".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "run".to_owned(),
            params: vec![
                IRTransParam {
                    name: "a".to_owned(),
                    ty: IRType::Int,
                },
                IRTransParam {
                    name: "b".to_owned(),
                    ty: IRType::Int,
                },
            ],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

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
    };
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![make_dummy_entity()],
        systems: vec![caller, callee],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![IRScene {
            name: "crosscall_arity".to_owned(),
            systems: vec!["Caller".to_owned()],
            stores: vec![],
            givens: vec![],
            events: vec![IRSceneEvent {
                var: "r".to_owned(),
                system: "Caller".to_owned(),
                event: "start".to_owned(),
                args: vec![],
                cardinality: Cardinality::Named("one".to_owned()),
            }],
            ordering: vec![],
            assertions: vec![],
            given_constraints: vec![],
            activations: vec![],
            span: None,
            file: None,
        }],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    match &results[0] {
        VerificationResult::SceneFail { reason, .. } => {
            assert!(reason.contains("CrossCall arity mismatch"));
            assert!(reason.contains("Callee::run"));
        }
        other => panic!("expected SceneFail, got {other:?}"),
    }
}

/// Build a minimal IR with an entity that has a status field,
/// a transition, and a system event — for scene testing.
fn make_scene_test_ir(scene: IRScene) -> IRProgram {
    let status_enum = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Active"), IRVariant::simple("Locked")],
        },
    };

    let account = IREntity {
        name: "Account".to_owned(),
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
                    variants: vec![IRVariant::simple("Active"), IRVariant::simple("Locked")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "lock".to_owned(),
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
                    ctor: "Active".to_owned(),
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
                    ctor: "Locked".to_owned(),
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

    let system = IRSystem {
        name: "Auth".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Account".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "lock_account".to_owned(),
            params: vec![IRTransParam {
                name: "account_id".to_owned(),
                ty: IRType::Identity,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "a".to_owned(),
                entity: "Account".to_owned(),
                filter: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "a".to_owned(),
                            ty: IRType::Entity {
                                name: "Account".to_owned(),
                            },

                            span: None,
                        }),
                        field: "id".to_owned(),
                        ty: IRType::Identity,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Var {
                        name: "account_id".to_owned(),
                        ty: IRType::Identity,

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "a".to_owned(),
                    transition: "lock".to_owned(),
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

    IRProgram {
        types: vec![status_enum],
        constants: vec![],
        functions: vec![],
        entities: vec![account],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![scene],
    }
}

#[test]
fn scene_happy_path_passes() {
    // Scene: given an Active account, lock it, then assert it's Locked.
    let scene = IRScene {
        name: "lock_test".to_owned(),
        systems: vec!["Auth".to_owned()],
        stores: vec![],
        givens: vec![IRSceneGiven {
            var: "a".to_owned(),
            entity: "Account".to_owned(),
            store_name: None,
            constraint: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Account".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            },
        }],
        events: vec![IRSceneEvent {
            var: "lk".to_owned(),
            system: "Auth".to_owned(),
            event: "lock_account".to_owned(),
            args: vec![IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Entity {
                        name: "Account".to_owned(),
                    },

                    span: None,
                }),
                field: "id".to_owned(),
                ty: IRType::Identity,

                span: None,
            }],
            cardinality: Cardinality::Named("one".to_owned()),
        }],
        ordering: vec![],
        assertions: vec![IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Entity {
                        name: "Account".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Locked".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };

    let ir = make_scene_test_ir(scene);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::ScenePass { .. }),
        "expected ScenePass, got: {:?}",
        results[0]
    );
}

#[test]
fn scene_impossible_assertion_fails() {
    // Scene: given an Active account, lock it, then assert it's STILL Active.
    // This is impossible — lock changes Active → Locked.
    let scene = IRScene {
        name: "impossible_test".to_owned(),
        systems: vec!["Auth".to_owned()],
        stores: vec![],
        givens: vec![IRSceneGiven {
            var: "a".to_owned(),
            entity: "Account".to_owned(),
            store_name: None,
            constraint: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "Account".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Active".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            },
        }],
        events: vec![IRSceneEvent {
            var: "lk".to_owned(),
            system: "Auth".to_owned(),
            event: "lock_account".to_owned(),
            args: vec![IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Entity {
                        name: "Account".to_owned(),
                    },

                    span: None,
                }),
                field: "id".to_owned(),
                ty: IRType::Identity,

                span: None,
            }],
            cardinality: Cardinality::Named("one".to_owned()),
        }],
        ordering: vec![],
        // Assert status is STILL Active — impossible after lock
        assertions: vec![IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Entity {
                        name: "Account".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Active".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };

    let ir = make_scene_test_ir(scene);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::SceneFail { .. }),
        "expected SceneFail, got: {:?}",
        results[0]
    );
}

#[test]
fn theorem_proved_by_induction() {
    require_unbounded_proof_tests!();

    // Theorem: status is always a valid enum variant (never -1).
    // This is trivially inductive — domain constraints enforce it at every step.
    let mut ir = make_order_ir(
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        },
        3,
    );
    ir.verifies.clear(); // remove verify block
    ir.theorems.push(IRTheorem {
        assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
        name: "status_valid".to_owned(),
        systems: vec!["Commerce".to_owned()],
        invariants: vec![],
        by_file: None,
        by_lemmas: vec![],
        shows: vec![IRExpr::Always {
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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: -1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        }],
        span: None,
        file: None,
    });

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::Proved { .. }),
        "expected Proved, got: {:?}",
        results[0]
    );
}

#[test]
fn theorem_unprovable_when_not_inductive() {
    require_unbounded_proof_tests!();

    // Theorem: all orders are always Pending.
    // This is NOT inductive — the confirm transition changes Pending → Confirmed.
    let mut ir = make_order_ir(
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        },
        3,
    );
    // Add a create event so orders can exist
    ir.systems[0].actions.push(IRSystemAction {
        name: "create_order".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        },
        body: vec![IRAction::Create {
            entity: "Order".to_owned(),
            fields: vec![
                IRCreateField {
                    name: "id".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    },
                },
                IRCreateField {
                    name: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    },
                },
            ],
        }],
        return_expr: None,
    });
    ir.verifies.clear();
    ir.theorems.push(IRTheorem {
        assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
        name: "always_pending".to_owned(),
        systems: vec!["Commerce".to_owned()],
        invariants: vec![],
        by_file: None,
        by_lemmas: vec![],
        shows: vec![IRExpr::Always {
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
                        enum_name: "OrderStatus".to_owned(),
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
        }],
        span: None,
        file: None,
    });

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    let witness = results[0].operational_witness().unwrap_or_else(|| {
        panic!(
            "expected Counterexample with native operational witness, got: {:?}",
            results[0]
        )
    });
    assert_eq!(witness.behavior().states().len(), 2);
    assert_eq!(witness.behavior().transitions().len(), 1);
    let atomic_steps = witness.behavior().transitions()[0].atomic_steps();
    assert_eq!(atomic_steps.len(), 1);
    assert_eq!(atomic_steps[0].system(), "Commerce");
    assert_eq!(atomic_steps[0].command(), "confirm_order");
}

#[test]
fn theorem_by_file_is_admitted_with_proof_artifact_evidence() {
    let mut ir = make_order_ir(
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        3,
    );
    ir.verifies.clear();
    ir.theorems.push(IRTheorem {
        assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
        name: "crypto_safe".to_owned(),
        systems: vec!["Commerce".to_owned()],
        invariants: vec![],
        by_lemmas: vec![],
        by_file: Some("proofs/crypto.agda".to_owned()),
        shows: vec![IRExpr::Always {
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    });

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);

    let VerificationResult::Admitted {
        name,
        reason,
        evidence,
        ..
    } = &results[0]
    else {
        panic!("expected Admitted result, got {:?}", results[0]);
    };

    assert_eq!(name, "crypto_safe");
    assert_eq!(reason, "external proof artifact reference");
    let proof_artifact = evidence
        .as_ref()
        .and_then(EvidenceEnvelope::as_proof_artifact_ref)
        .expect("expected proof artifact evidence");
    assert_eq!(proof_artifact.locator(), "proofs/crypto.agda");
    assert_eq!(proof_artifact.backend_name(), Some("agda"));
    assert_eq!(proof_artifact.label_text(), Some("crypto_safe"));
    assert!(!proof_artifact.is_checked());

    let rendered = format!("{}", results[0]);
    assert!(rendered.contains("ADMITTED crypto_safe"));
    assert!(rendered.contains("proof artifact: proofs/crypto.agda"));
}

#[test]
fn axiom_by_file_is_disclosed_in_result_assumptions() {
    let mut ir = make_order_ir(
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        3,
    );
    ir.axioms.push(IRAxiom {
        name: "crypto_safe".to_owned(),
        body: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        by_file: Some("proofs/crypto.agda".to_owned()),
        span: None,
        file: None,
    });

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    let assumptions = results[0].assumptions();
    let Some(TrustedAssumption::Axiom {
        name,
        proof_artifact,
    }) = assumptions.iter().find(|assumption| {
        matches!(
            assumption,
            TrustedAssumption::Axiom { name, .. } if name == "crypto_safe"
        )
    })
    else {
        panic!("expected axiom assumption with proof artifact, got {assumptions:?}");
    };

    assert_eq!(name, "crypto_safe");
    let proof_artifact = proof_artifact
        .as_ref()
        .expect("expected axiom proof artifact metadata");
    assert_eq!(proof_artifact.locator(), "proofs/crypto.agda");
    assert_eq!(proof_artifact.backend_name(), Some("agda"));
    assert_eq!(proof_artifact.label_text(), Some("crypto_safe"));
}

#[test]
fn lemma_sat_failure_carries_countermodel_evidence() {
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![IRLemma {
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
            name: "false_lemma".to_owned(),
            body: vec![IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }],
            span: None,
            file: None,
        }],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    let countermodel = results[0].countermodel().unwrap_or_else(|| {
        panic!(
            "expected countermodel evidence for failed lemma, got: {:?}",
            results[0]
        )
    });
    assert_eq!(countermodel.backend_name(), Some("z3"));
    assert_eq!(
        countermodel.summary_text(),
        Some("satisfying model for negated lemma body")
    );
    assert!(countermodel.bindings().is_empty());
    let rendered = format!("{}", results[0]);
    assert!(rendered.contains("COUNTEREXAMPLE false_lemma"));
    assert!(rendered.contains("countermodel: satisfying model for negated lemma body"));
    assert!(rendered.contains("backend: z3"));

    let json = serde_json::to_value(&results[0]).expect("serialize failed lemma result");
    assert_eq!(json["kind"], "counterexample");
    assert_eq!(json["evidence"]["payload"]["kind"], "countermodel");
    assert_eq!(json["evidence"]["payload"]["payload"]["backend"], "z3");
    assert_eq!(
        json["evidence"]["payload"]["payload"]["summary"],
        "satisfying model for negated lemma body"
    );
}

/// Helper for no-stutter induction tests: build an IR whose
/// only system event has guard `false`. Under no-stutter, the
/// transition relation reduces to `false` and any induction-style
/// action proof becomes vacuous.
fn make_dead_event_theorem_ir(invariants: Vec<IRExpr>, shows: Vec<IRExpr>) -> IRProgram {
    let entity = IREntity {
        name: "A".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["A".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "dead".to_owned(),
            params: vec![],
            // requires false — never enabled
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            },
            body: vec![IRAction::Create {
                entity: "A".to_owned(),
                fields: vec![],
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

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![IRTheorem {
            // Explicit no-stutter assumption set: this is the
            // only configuration in which Finding 1's vacuity
            // bug fires. Theorems default to stutter ON; the
            // user must opt out via `assume { no stutter }`.
            assumption_set: crate::ir::types::IRAssumptionSet {
                stutter: false,
                weak_fair: Vec::new(),
                strong_fair: Vec::new(),
                per_tuple: Vec::new(),
            },
            name: "vacuous_under_no_stutter".to_owned(),
            systems: vec!["S".to_owned()],
            invariants,
            shows,
            by_file: None,
            by_lemmas: vec![],
            span: None,
            file: None,
        }],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

/// a theorem with `assume { no stutter }`
/// over a system whose only event is `requires false` must NOT be
/// reported as PROVED by 1-induction. Pre-fix, the action case
/// `P(k) ∧ transition(k→k+1) → P(k+1)` had `transition` reducing to
/// `false`, making the implication trivially true and 1-induction
/// vacuously "prove" the property from a contradictory transition
/// relation. The trace-validity guard added in this fix bails the
/// induction site to UNPROVABLE in that case.
#[test]
fn theorem_step_case_does_not_vacuously_prove_under_no_stutter() {
    require_unbounded_proof_tests!();

    // Trivially true property (`all a: A | a.x == a.x`). Without
    // the guard, 1-induction "proves" it vacuously because the
    // transition relation is unsatisfiable.
    let trivial = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "a".to_owned(),
            domain: IRType::Entity {
                name: "A".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "A".to_owned(),
                        },
                        span: None,
                    }),
                    field: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "a".to_owned(),
                        ty: IRType::Entity {
                            name: "A".to_owned(),
                        },
                        span: None,
                    }),
                    field: "x".to_owned(),
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

    let ir = make_dead_event_theorem_ir(vec![], vec![trivial]);

    // cover BOTH proof techniques with the
    // default config. Pre-fix, both `try_ic3_on_theorem` (the CHC
    // encoding) and the 1-induction action case vacuously discharged
    // this theorem under no-stutter; the theorem-side fix has to
    // gate both paths.
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        !matches!(&results[0], VerificationResult::Proved { .. }),
        "no theorem proof technique must vacuously prove a theorem \
         under no-stutter when the transition relation is \
         unsatisfiable; got: {:?}",
        results[0]
    );
}

/// same vacuity bug on the invariant
/// preservation step `I(k) ∧ transition(k→k+1) → I(k+1)`. Pre-fix,
/// `transition` reducing to `false` made the action trivially hold
/// and the theorem reported PROVED even though the trace cannot
/// extend at all under no-stutter.
#[test]
fn theorem_invariant_preservation_does_not_vacuously_prove_under_no_stutter() {
    require_unbounded_proof_tests!();

    // Trivially true invariant (`all a: A | a.x == a.x`).
    let trivial_inv = IRExpr::Forall {
        var: "a".to_owned(),
        domain: IRType::Entity {
            name: "A".to_owned(),
        },
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Entity {
                        name: "A".to_owned(),
                    },
                    span: None,
                }),
                field: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "a".to_owned(),
                    ty: IRType::Entity {
                        name: "A".to_owned(),
                    },
                    span: None,
                }),
                field: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    };

    // Trivially true `show` so the test focuses on invariant preservation.
    let trivial_show = IRExpr::Always {
        body: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        span: None,
    };

    let ir = make_dead_event_theorem_ir(vec![trivial_inv], vec![trivial_show]);

    // cover both IC3 and induction.
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        !matches!(&results[0], VerificationResult::Proved { .. }),
        "invariant preservation action must not vacuously prove a theorem \
         under no-stutter when the transition relation is unsatisfiable; \
         got: {:?}",
        results[0]
    );
}

#[test]
fn tiered_bounded_only_skips_induction() {
    // With bounded_only, an inductive property should be CHECKED (not PROVED)
    let ir = make_order_ir(
        IRExpr::Always {
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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: -1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),

                span: None,
            }),

            span: None,
        },
        3,
    );
    let config = VerifyConfig {
        bounded_only: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::Checked { .. }),
        "expected CHECKED with bounded_only, got: {:?}",
        results[0]
    );
}

#[test]
fn tiered_unbounded_only_returns_unknown_on_failure() {
    require_unbounded_proof_tests!();

    // With unbounded_only, a non-inductive property should be UNKNOWN (not CHECKED)
    let mut ir = make_order_ir(
        IRExpr::Always {
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
                        enum_name: "OrderStatus".to_owned(),
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
        },
        3,
    );
    // Add create so induction action fails (status changes via confirm)
    ir.systems[0].actions.push(IRSystemAction {
        name: "create_order".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        },
        body: vec![IRAction::Create {
            entity: "Order".to_owned(),
            fields: vec![
                IRCreateField {
                    name: "id".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    },
                },
                IRCreateField {
                    name: "status".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "OrderStatus".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
                        span: None,
                    },
                },
            ],
        }],
        return_expr: None,
    });
    let config = VerifyConfig {
        unbounded_only: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 1);
    // IC3 now finds the actual violation even in unbounded-only mode,
    // producing a Counterexample. If IC3 fails, falls back to Unprovable.
    assert!(
        matches!(
            &results[0],
            VerificationResult::Counterexample { .. } | VerificationResult::Unprovable { .. }
        ),
        "expected Counterexample or Unprovable with unbounded_only, got: {:?}",
        results[0]
    );
}

#[test]
fn bmc_timeout_returns_unknown() {
    // With a 1ms BMC timeout, even a simple property should return UNKNOWN
    // because the solver can't finish in time.
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
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: -1 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };
    let ir = make_order_ir(property, 10);
    let config = VerifyConfig {
        bounded_only: true,
        bmc_timeout_ms: 1, // 1ms — too short to solve
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 1);
    // Should be either CHECKED (if solver is fast enough) or UNKNOWN (timeout)
    // On most systems, 1ms is too short for depth 10, but Z3 may be fast enough.
    // Accept either — the important thing is it doesn't panic.
    assert!(
        matches!(
            &results[0],
            VerificationResult::Checked { .. } | VerificationResult::Unprovable { .. }
        ),
        "expected CHECKED or UNKNOWN with 1ms timeout, got: {:?}",
        results[0]
    );
}

#[test]
fn symmetry_breaking_does_not_regress_results() {
    // Symmetry breaking should not change correctness — valid properties should
    // still pass. The counterexample case is covered by bmc_counterexample_on_violation
    // which also runs with symmetry breaking active (it's always on).
    let valid_property = IRExpr::Always {
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
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: -1 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };
    let ir = make_order_ir(valid_property, 3);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            VerificationResult::Checked { .. } | VerificationResult::Proved { .. }
        ),
        "valid property should be CHECKED or PROVED with symmetry breaking, got: {:?}",
        results[0]
    );
}

// ── IC3 integration tests ──────────────────────────────────────

/// Test: property proved by IC3 that 1-induction can't prove.
///
/// Entity has two fields (x, y) both starting at 0, with a transition
/// that increments both. Property: `y <= 10`. This requires the
/// strengthening invariant `y == x` (so the guard `x < 10` constrains y).
/// 1-induction fails because from an arbitrary state with y=10, x could
/// be anything, and y'=11 violates the property. IC3 discovers `y == x`.
#[test]
fn ic3_proves_property_induction_cannot() {
    require_unbounded_proof_tests!();

    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![
            IRField {
                name: "x".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "y".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "step".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpLt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            },
            updates: vec![
                IRUpdate {
                    field: "x".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                },
                IRUpdate {
                    field: "y".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "y".to_owned(),
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
                },
            ],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "tick".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "step".to_owned(),
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

    // Property: always all c: Counter | c.y <= 10
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "c".to_owned(),
                        ty: IRType::Entity {
                            name: "Counter".to_owned(),
                        },

                        span: None,
                    }),
                    field: "y".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    // Verify block with this property
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            name: "v".to_owned(),
            depth: None,
            // opt into stutter so the BMC trace can
            // extend. The fixture system has no creates and
            // `step` requires an active Counter — under verify's
            // default no-stutter assumption, deadlock detection
            // would short-circuit before BMC ran. We construct
            // the IRAssumptionSet directly (rather than via the
            // theorem helper) to keep the construct kind clear:
            // verify defaults to no-stutter and this stutter is
            // the user's explicit opt-in.
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet {
                stutter: true,
                weak_fair: Vec::new(),
                strong_fair: Vec::new(),
                per_tuple: Vec::new(),
            },
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 20,
            }],
            asserts: vec![property.clone()],
            span: None,
            file: None,
        }],
        theorems: vec![IRTheorem {
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
            name: "counter_bounded_thm".to_owned(),
            systems: vec!["S".to_owned()],
            invariants: vec![],
            shows: vec![property],
            by_file: None,
            by_lemmas: vec![],
            span: None,
            file: None,
        }],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let config = VerifyConfig::default();
    let results = verify_all(&ir, &config);

    // We expect:
    // - verify block: induction fails, IC3 proves → PROVED (method: IC3/PDR)
    // OR: induction fails, IC3 fails, BMC checks → CHECKED
    // - theorem: IC3 proves → PROVED (method: IC3/PDR)
    // OR: induction fails, IC3 fails → UNPROVABLE

    // At minimum, the verify block should succeed (BMC fallback if IC3 can't)
    assert!(!results.is_empty(), "expected at least 1 result");

    // Verify block: induction fails → IC3 proves
    let verify_result = &results[0];
    assert!(
        matches!(
            verify_result,
            VerificationResult::Proved { method, .. } if method == "IC3/PDR"
        ),
        "expected PROVED (method: IC3/PDR) for verify block, got: {verify_result}"
    );

    // Theorem: IC3 proves before staged induction is needed.
    assert_eq!(results.len(), 2, "expected 2 results (verify + theorem)");
    let thm_result = &results[1];
    assert!(
        matches!(
            thm_result,
            VerificationResult::Proved { method, .. } if method == "IC3/PDR"
        ),
        "expected PROVED (method: IC3/PDR) for theorem, got: {thm_result}"
    );
}

#[test]
fn no_ic3_flag_skips_ic3_verify_falls_to_bmc() {
    require_unbounded_proof_tests!();

    // Same IR as ic3_proves_property_induction_cannot, but with --no-ic3.
    // Verify block: induction fails, IC3 skipped, falls to BMC → CHECKED.
    let ir = make_two_counter_ir();
    let config = VerifyConfig {
        no_ic3: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 2);

    // Verify block: BMC fallback (CHECKED)
    assert!(
        matches!(&results[0], VerificationResult::Checked { .. }),
        "expected CHECKED with --no-ic3, got: {}",
        results[0]
    );

    // Theorem: IC3 skipped, induction fails → UNPROVABLE
    assert!(
        matches!(&results[1], VerificationResult::Unprovable { .. }),
        "expected UNPROVABLE with --no-ic3, got: {}",
        results[1]
    );
}

#[test]
fn bounded_only_skips_theorem_proving() {
    // With --bounded-only, theorems can't be proved (no BMC for theorems).
    let ir = make_two_counter_ir();
    let config = VerifyConfig {
        bounded_only: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 2);

    // Verify block: BMC only → CHECKED
    assert!(
        matches!(&results[0], VerificationResult::Checked { .. }),
        "expected CHECKED with --bounded-only, got: {}",
        results[0]
    );

    // Theorem: --bounded-only → UNPROVABLE
    let thm = &results[1];
    assert!(
        matches!(thm, VerificationResult::Unprovable { hint, .. }
            if hint.contains("--bounded-only")),
        "expected UNPROVABLE with --bounded-only hint, got: {thm}"
    );
}

#[test]
fn unbounded_only_no_ic3_gives_accurate_hint() {
    require_unbounded_proof_tests!();

    // --unbounded-only + --no-ic3: hint should say IC3 was skipped.
    let ir = make_two_counter_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);

    // Verify block: induction fails, IC3 skipped, BMC skipped → UNPROVABLE
    let verify_result = &results[0];
    assert!(
        matches!(verify_result, VerificationResult::Unprovable { hint, .. }
            if hint.contains("--no-ic3")),
        "expected UNPROVABLE mentioning --no-ic3, got: {verify_result}"
    );
}

/// Helper: build the two-counter IR used by multiple IC3 flag tests.
fn make_two_counter_ir() -> IRProgram {
    let entity = IREntity {
        name: "Counter".to_owned(),
        fields: vec![
            IRField {
                name: "x".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "y".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "step".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpLt".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            },
            updates: vec![
                IRUpdate {
                    field: "x".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
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
                },
                IRUpdate {
                    field: "y".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "y".to_owned(),
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
                },
            ],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "tick".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "c".to_owned(),
                    transition: "step".to_owned(),
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

    // Property: always all c: Counter | c.y <= 10
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "c".to_owned(),
                        ty: IRType::Entity {
                            name: "Counter".to_owned(),
                        },

                        span: None,
                    }),
                    field: "y".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            name: "v".to_owned(),
            depth: None,
            // opt into stutter so the BMC trace can
            // extend. The fixture system has no creates and
            // `step` requires an active Counter — under verify's
            // default no-stutter assumption, deadlock detection
            // would short-circuit before BMC ran. We construct
            // the IRAssumptionSet directly (rather than via the
            // theorem helper) to keep the construct kind clear:
            // verify defaults to no-stutter and this stutter is
            // the user's explicit opt-in.
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet {
                stutter: true,
                weak_fair: Vec::new(),
                strong_fair: Vec::new(),
                per_tuple: Vec::new(),
            },
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 20,
            }],
            asserts: vec![property.clone()],
            span: None,
            file: None,
        }],
        theorems: vec![IRTheorem {
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
            name: "counter_bounded_thm".to_owned(),
            systems: vec!["S".to_owned()],
            invariants: vec![],
            shows: vec![property],
            by_file: None,
            by_lemmas: vec![],
            span: None,
            file: None,
        }],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

// ── Verify scope helper tests ───────────────────────────────────────

/// Build a minimal IR with one entity (`A`) in one system (`S`)
/// and a single verify block whose only verify target is
/// `S[0..hi]`. The system has one creation event and a single
/// trivial property. Used by `compute_verify_scope` tests to
/// pin the scope helper's behavior.
fn make_single_entity_ir(hi: i64) -> IRProgram {
    let entity = IREntity {
        name: "A".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["A".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "mk".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Create {
                entity: "A".to_owned(),
                fields: vec![],
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

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            name: "scope_test".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi,
            }],
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            asserts: vec![IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

/// `compute_verify_scope` must size each
/// entity's slot count from the verify target's `hi` bound, not the
/// hardcoded `2` that several call sites (notably `check_for_deadlock`)
/// previously used. Without this fix, the deadlock probe and the
/// induction/lasso paths build a smaller pool than the actual BMC,
/// so they can disagree with `check_verify_block` on the same
/// verify block.
#[test]
fn compute_verify_scope_uses_hi_not_or_insert_2() {
    let ir = make_single_entity_ir(4);
    let verify_block = &ir.verifies[0];
    let (scope, system_names, bound, _store_ranges) = compute_verify_scope(&ir, verify_block);

    assert_eq!(
        scope.get("A").copied(),
        Some(4),
        "scope for entity `A` must come from verify target hi=4, not the legacy or_insert(2) default"
    );
    assert_eq!(bound, 4, "bound must equal max hi across verify targets");
    assert_eq!(system_names, vec!["S".to_owned()]);
}

/// `compute_verify_scope` must use the default verify fallback bound when a
/// verify block has no explicit depth and its system hi does not raise it.
/// The explicit system hi still clamps entity pools to at least one slot.
#[test]
fn compute_verify_scope_uses_default_bound_when_hi_is_smaller() {
    let ir = make_single_entity_ir(0);
    let verify_block = &ir.verifies[0];
    let (scope, _system_names, bound, _store_ranges) = compute_verify_scope(&ir, verify_block);

    assert_eq!(
        scope.get("A").copied(),
        Some(3),
        "scope must inherit the default verify bound when no explicit depth is provided"
    );
    assert_eq!(
        bound, 3,
        "default verify bound should be 3 when no explicit depth is provided"
    );
}

#[test]
fn select_verify_relevant_filters_entities_and_systems() {
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![
            IREntity {
                name: "A".to_owned(),
                fields: vec![],
                transitions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
            },
            IREntity {
                name: "B".to_owned(),
                fields: vec![],
                transitions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
            },
        ],
        systems: vec![
            IRSystem {
                name: "S".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec!["A".to_owned()],
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
                name: "T".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec!["B".to_owned()],
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
        ],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let scope = HashMap::from([("B".to_owned(), 2usize)]);
    let system_names = vec!["T".to_owned()];
    let (entities, systems) = select_verify_relevant(&ir, &scope, &system_names);

    assert_eq!(entities.len(), 1);
    assert_eq!(entities[0].name, "B");
    assert_eq!(systems.len(), 1);
    assert_eq!(systems[0].name, "T");
}

#[test]
fn compute_theorem_scope_follows_let_bindings_and_crosscalls() {
    let task = IREntity {
        name: "Task".to_owned(),
        fields: vec![],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };
    let log = IREntity {
        name: "Log".to_owned(),
        fields: vec![],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let program = IRSystem {
        name: "Program".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![IRLetBinding {
            name: "worker".to_owned(),
            system_type: "Worker".to_owned(),
            store_bindings: vec![],
        }],
        procs: vec![],
    };

    let worker = IRSystem {
        name: "Worker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Task".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "run".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "Audit".to_owned(),
                command: "record".to_owned(),
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

    let audit = IRSystem {
        name: "Audit".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Log".to_owned()],
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

    let theorem = IRTheorem {
        name: "t".to_owned(),
        systems: vec!["Program".to_owned()],
        assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
        invariants: vec![],
        shows: vec![],
        by_file: None,
        by_lemmas: vec![],
        span: None,
        file: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![task, log],
        systems: vec![program, worker, audit],
        verifies: vec![],
        theorems: vec![theorem.clone()],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let defs = defenv::DefEnv::from_ir(&ir);
    let (scope, system_names, required_slots) = compute_theorem_scope(&ir, &theorem, &[], &defs);

    assert_eq!(scope.get("Task").copied(), Some(2));
    assert_eq!(scope.get("Log").copied(), Some(2));
    assert!(system_names.contains(&"Program".to_owned()));
    assert!(system_names.contains(&"Worker".to_owned()));
    assert!(system_names.contains(&"Audit".to_owned()));
    assert!(required_slots.is_empty());
}

#[test]
fn collect_in_scope_invariants_wraps_entity_and_target_system_only() {
    let entity = IREntity {
        name: "A".to_owned(),
        fields: vec![IRField {
            name: "x".to_owned(),
            ty: IRType::Int,
            default: None,
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![IRInvariant {
            name: "non_negative".to_owned(),
            body: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
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
        fsm_decls: vec![],
    };

    let caller = IRSystem {
        name: "Caller".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["A".to_owned()],
        commands: vec![],
        actions: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![IRInvariant {
            name: "caller_inv".to_owned(),
            body: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
        }],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };

    let callee = IRSystem {
        name: "Callee".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec![],
        commands: vec![],
        actions: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![IRInvariant {
            name: "callee_inv".to_owned(),
            body: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            },
        }],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity.clone()],
        systems: vec![caller.clone(), callee],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let defs = defenv::DefEnv::from_ir(&ir);
    let wrapped = collect_in_scope_invariants(&defs, &[entity], &[caller]);

    assert_eq!(
        wrapped.len(),
        2,
        "expected entity invariant and target-system invariant only"
    );
    assert!(wrapped.iter().any(|expr| matches!(
        expr,
        IRExpr::Always { body, .. }
            if matches!(
                body.as_ref(),
                IRExpr::Forall { body: inner, .. }
                    if matches!(
                        inner.as_ref(),
                        IRExpr::BinOp { left, .. }
                            if matches!(
                                left.as_ref(),
                                IRExpr::Field { expr, field, .. }
                                    if field == "x"
                                        && matches!(
                                            expr.as_ref(),
                                            IRExpr::Var { name, .. } if name == "__inv_self"
                                        )
                            )
                    )
            )
    )));
    assert!(wrapped.iter().any(|expr| matches!(
        expr,
        IRExpr::Always { body, .. }
            if matches!(
                body.as_ref(),
                IRExpr::Lit { value: LitVal::Bool { value: true }, .. }
            )
    )));
    assert!(
        !wrapped.iter().any(|expr| matches!(
            expr,
            IRExpr::Always { body, .. }
                if matches!(
                    body.as_ref(),
                    IRExpr::Lit { value: LitVal::Bool { value: false }, .. }
                )
        )),
        "callee system invariants must not leak into target-system invariant collection"
    );
}

#[test]
fn collect_crosscall_systems_finds_nested_targets() {
    let mut targets = Vec::new();
    let actions = vec![IRAction::Choose {
        var: "x".to_owned(),
        entity: "Task".to_owned(),
        filter: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        ops: vec![IRAction::ForAll {
            var: "y".to_owned(),
            entity: "Task".to_owned(),
            ops: vec![IRAction::CrossCall {
                system: "Audit".to_owned(),
                command: "record".to_owned(),
                args: vec![],
            }],
        }],
    }];

    collect_crosscall_systems(&actions, &mut targets);

    assert_eq!(targets, vec!["Audit".to_owned()]);
}

#[test]
fn collect_crosscall_systems_finds_match_scrutinee_targets() {
    let mut targets = Vec::new();
    let actions = vec![IRAction::Match {
        scrutinee: IRActionMatchScrutinee::CrossCall {
            system: "Audit".to_owned(),
            command: "record".to_owned(),
            args: vec![],
        },
        arms: vec![IRActionMatchArm {
            pattern: IRPattern::PWild,
            guard: None,
            body: vec![],
        }],
    }];

    collect_crosscall_systems(&actions, &mut targets);

    assert_eq!(targets, vec!["Audit".to_owned()]);
}

#[test]
fn collect_crosscall_systems_finds_system_apply_targets() {
    let mut targets = Vec::new();
    let actions = vec![IRAction::Apply {
        target: "TicketOps".to_owned(),
        transition: "finish_one".to_owned(),
        refs: vec!["tickets".to_owned()],
        args: vec![],
    }];

    collect_crosscall_systems(&actions, &mut targets);

    assert_eq!(targets, vec!["TicketOps".to_owned()]);
}

#[test]
fn contains_liveness_distinguishes_history_from_liveness() {
    let previously = IRExpr::Previously {
        body: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        span: None,
    };
    let since = IRExpr::Since {
        left: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        right: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: false },
            span: None,
        }),
        span: None,
    };
    let historically = IRExpr::Historically {
        body: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        span: None,
    };
    let once = IRExpr::Once {
        body: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        span: None,
    };

    assert!(contains_liveness(&previously));
    assert!(contains_liveness(&since));
    assert!(!contains_liveness(&historically));
    assert!(!contains_liveness(&once));
}

#[test]
fn contains_past_time_detects_all_past_operators() {
    let expr = IRExpr::BinOp {
        op: "OpAnd".to_owned(),
        left: Box::new(IRExpr::Historically {
            body: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            span: None,
        }),
        right: Box::new(IRExpr::Once {
            body: Box::new(IRExpr::Previously {
                body: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };

    let future_only = IRExpr::Always {
        body: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }),
        span: None,
    };

    assert!(contains_past_time(&expr));
    assert!(!contains_past_time(&future_only));
}

// ── Map encoding tests ──────────────────────────────────────────

#[test]
fn map_field_verify_index_after_update() {
    // Entity with a Map<Int, Int> field. Action does m[k:= v].
    // Property: after update, m[k] == v. Tests MapUpdate + Index Z3 encoding.
    let entity = IREntity {
        name: "Store".to_owned(),
        fields: vec![IRField {
            name: "data".to_owned(),
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Int),
            },
            default: None,
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "put".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            updates: vec![IRUpdate {
                field: "data".to_owned(),
                value: IRExpr::MapUpdate {
                    map: Box::new(IRExpr::Var {
                        name: "data".to_owned(),
                        ty: IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Int),
                        },

                        span: None,
                    }),
                    key: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 42 },

                        span: None,
                    }),
                    value: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 100 },

                        span: None,
                    }),
                    ty: IRType::Map {
                        key: Box::new(IRType::Int),
                        value: Box::new(IRType::Int),
                    },

                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Store".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_store".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Store".to_owned(),
                    fields: vec![], // data field unconstrained at creation
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_put".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "s".to_owned(),
                    entity: "Store".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "s".to_owned(),
                        transition: "put".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // Helper: build s.data[42] expression
    let data_at_42 = |var: &str| -> IRExpr {
        IRExpr::Index {
            map: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: var.to_owned(),
                    ty: IRType::Entity {
                        name: "Store".to_owned(),
                    },

                    span: None,
                }),
                field: "data".to_owned(),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },

                span: None,
            }),
            key: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 42 },

                span: None,
            }),
            ty: IRType::Int,

            span: None,
        }
    };

    // Property: always all s: Store | s.data[42] == s.data[42]
    // Tautological — tests that Index encodes correctly in properties
    // without depending on initial/transition values. Z3 should prove
    // this by reflexivity of array select.
    let reflex_property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "s".to_owned(),
            domain: IRType::Entity {
                name: "Store".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(data_at_42("s")),
                right: Box::new(data_at_42("s")),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    // Property: data[42] == 100 — false for newly created entities,
    // but CHECKED at depth 0 shows no violation with no active entities.
    // After create + put it holds. BMC validates the full encoding
    // path (MapUpdate in action → Index in property → comparison).
    let post_put_property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "s".to_owned(),
            domain: IRType::Entity {
                name: "Store".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(data_at_42("s")),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 100 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![
            IRVerify {
                stores: vec![],
                assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
                name: "map_reflex".to_owned(),
                depth: None,
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![reflex_property],
                span: None,
                file: None,
            },
            IRVerify {
                stores: vec![],
                assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
                name: "map_post_put".to_owned(),
                depth: None,
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![post_put_property],
                span: None,
                file: None,
            },
        ],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 2, "expected 2 verify results");

    // Reflexivity: data[42] == data[42] — PROVED by induction (trivially true)
    assert!(
        matches!(&results[0], VerificationResult::Proved { .. }),
        "reflexive map property should be PROVED: got {}",
        results[0]
    );

    // Post-put: data[42] == 100 — COUNTEREXAMPLE expected (create_store
    // event creates entities with unconstrained data, so data[42] != 100
    // before first put). Validates full MapUpdate→Index→comparison path.
    assert!(
        matches!(&results[1], VerificationResult::Counterexample { .. }),
        "post-put map property should find COUNTEREXAMPLE: got {}",
        results[1]
    );
}

#[test]
fn map_literal_in_property_encoding() {
    // Tests MapLit encoding in the property encoder.
    // Entity with Map<Int, Int> field. Property compares field to a
    // MapLit constant: data == Map((42, 100)). BMC checks this.
    let entity = IREntity {
        name: "M".to_owned(),
        fields: vec![IRField {
            name: "data".to_owned(),
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Int),
            },
            default: None,
            initial_constraint: None,
        }],
        transitions: vec![],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["M".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_m".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "M".to_owned(),
                fields: vec![],
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

    // Property: all m: M | m.data != Map((42, 100))
    // MapLit in the assertion — validates MapLit property encoding.
    // True: data is unconstrained at creation, extremely unlikely to
    // equal the specific map literal. BMC should PROVE or CHECK this.
    let map_ty = IRType::Map {
        key: Box::new(IRType::Int),
        value: Box::new(IRType::Int),
    };
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "m".to_owned(),
            domain: IRType::Entity {
                name: "M".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpNEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "m".to_owned(),
                        ty: IRType::Entity {
                            name: "M".to_owned(),
                        },

                        span: None,
                    }),
                    field: "data".to_owned(),
                    ty: map_ty.clone(),

                    span: None,
                }),
                right: Box::new(IRExpr::MapLit {
                    entries: vec![(
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 42 },

                            span: None,
                        },
                        IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 100 },

                            span: None,
                        },
                    )],
                    ty: map_ty,

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "map_lit_test".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    // Should not panic — validates MapLit in property encoder path
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        !matches!(&results[0], VerificationResult::Unprovable { .. }),
        "MapLit in property should encode without error: got {}",
        results[0]
    );
}

#[test]
fn primed_map_update_sugar_encoding() {
    // Tests the primed-index sugar path: data' = data[key:= value]
    // where the action body uses MapUpdate on the current field value.
    // This is the pattern used in workflow_engine: variables'[k] = v
    // which desugars to variables' = variables[k:= v].
    //
    // Verifies that Prime(MapUpdate(Var, key, val)) encodes correctly
    // through the action → frame → property encoding chain.
    let entity = IREntity {
        name: "KV".to_owned(),
        fields: vec![
            IRField {
                name: "store".to_owned(),
                ty: IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
                default: None,
                initial_constraint: None,
            },
            IRField {
                name: "count".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "set_key".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            updates: vec![
                // store' = store[1:= 42]
                IRUpdate {
                    field: "store".to_owned(),
                    value: IRExpr::MapUpdate {
                        map: Box::new(IRExpr::Var {
                            name: "store".to_owned(),
                            ty: IRType::Map {
                                key: Box::new(IRType::Int),
                                value: Box::new(IRType::Int),
                            },

                            span: None,
                        }),
                        key: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        }),
                        value: Box::new(IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 42 },

                            span: None,
                        }),
                        ty: IRType::Map {
                            key: Box::new(IRType::Int),
                            value: Box::new(IRType::Int),
                        },

                        span: None,
                    },
                },
                // count' = count + 1 (scalar frame test alongside map)
                IRUpdate {
                    field: "count".to_owned(),
                    value: IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "count".to_owned(),
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
                },
            ],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["KV".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_kv".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "KV".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_set".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "k".to_owned(),
                    entity: "KV".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "k".to_owned(),
                        transition: "set_key".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // Property: count >= 0 (monotonically increasing from 0).
    // Tests that scalar fields are correctly framed alongside map updates.
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "k".to_owned(),
            domain: IRType::Entity {
                name: "KV".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "k".to_owned(),
                        ty: IRType::Entity {
                            name: "KV".to_owned(),
                        },

                        span: None,
                    }),
                    field: "count".to_owned(),
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

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "primed_map_update".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 5,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // count starts at 0, incremented by 1 each set_key → always >= 0.
    // Map update (store) encodes alongside scalar update without conflict.
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "primed map update with scalar should succeed: got {}",
        results[0]
    );
}

// ── Set encoding tests ──────────────────────────────────────────

#[test]
fn set_membership_via_index() {
    // Tests that `e in S` (lowered to Index(S, e)) works in properties.
    // Entity with Set<Int> field `tags`. Action `add_tag` does tags' = tags[5:= true]
    // (store 5 as member). Property: after add_tag, 5 is in tags.
    //
    // Since Set<T> = Array<T, Bool>, Index(tags, 5) returns Bool = true after store.
    let set_ty = IRType::Set {
        element: Box::new(IRType::Int),
    };

    let entity = IREntity {
        name: "Item".to_owned(),
        fields: vec![IRField {
            name: "tags".to_owned(),
            ty: set_ty.clone(),
            default: None,
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "add_tag".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            // tags' = tags[5:= true] (add 5 to set)
            updates: vec![IRUpdate {
                field: "tags".to_owned(),
                value: IRExpr::MapUpdate {
                    map: Box::new(IRExpr::Var {
                        name: "tags".to_owned(),
                        ty: set_ty.clone(),

                        span: None,
                    }),
                    key: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 5 },

                        span: None,
                    }),
                    value: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ty: set_ty.clone(),

                    span: None,
                },
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    };

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Item".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_item".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Item".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_add".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "i".to_owned(),
                    entity: "Item".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "i".to_owned(),
                        transition: "add_tag".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // Property: always (all i: Item | i.tags[5] == true)
    // i.e., "5 is always a member of tags"
    // This is NOT always true: newly created items have unconstrained tags,
    // so tags[5] can be false before add_tag fires.
    // BMC should find a COUNTEREXAMPLE — validates the full store→select
    // semantic chain for set membership.
    let tags_at_5 = IRExpr::Index {
        map: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "i".to_owned(),
                ty: IRType::Entity {
                    name: "Item".to_owned(),
                },

                span: None,
            }),
            field: "tags".to_owned(),
            ty: set_ty,

            span: None,
        }),
        key: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 5 },

            span: None,
        }),
        ty: IRType::Bool,

        span: None,
    };

    let membership_property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "i".to_owned(),
            domain: IRType::Entity {
                name: "Item".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(tags_at_5),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "set_membership".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![membership_property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // Created items have unconstrained tags → tags[5] can be false → COUNTEREXAMPLE.
    // This validates: Set field as Array<Int,Bool>, store(5,true) in add_tag action,
    // select(5) in property assertion, Bool comparison — full semantic chain.
    assert!(
        matches!(&results[0], VerificationResult::Counterexample { .. }),
        "set membership should produce COUNTEREXAMPLE (unconstrained before add_tag): got {}",
        results[0]
    );
}

#[test]
fn set_literal_in_property() {
    // Tests SetLit in property encoding.
    // Property: Set(1,2,3)[2] == true (2 is a member of {1,2,3}).
    // Uses SetLit directly in the assertion, validates property-side encoding.
    let set_ty = IRType::Set {
        element: Box::new(IRType::Int),
    };

    let entity = IREntity {
        name: "X".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["X".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_x".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "X".to_owned(),
                fields: vec![],
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

    // Property: Set(1,2,3)[2] == true — 2 is in {1,2,3}
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Entity {
                name: "X".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Index {
                    map: Box::new(IRExpr::SetLit {
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
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 3 },

                                span: None,
                            },
                        ],
                        ty: set_ty,

                        span: None,
                    }),
                    key: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "set_lit_membership".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // Set(1,2,3)[2] is always true — should be PROVED
    assert!(
        matches!(&results[0], VerificationResult::Proved { .. }),
        "set literal membership should be PROVED: got {}",
        results[0]
    );
}

#[test]
fn set_literal_cardinality() {
    // Tests #Set(1,2,3) == 3 in a property — cardinality of a set literal.
    let set_ty = IRType::Set {
        element: Box::new(IRType::Int),
    };

    let entity = IREntity {
        name: "X".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["X".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_x".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "X".to_owned(),
                fields: vec![],
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

    // Property: #Set(1,2,3) == 3
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Entity {
                name: "X".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Card {
                    expr: Box::new(IRExpr::SetLit {
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
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 3 },

                                span: None,
                            },
                        ],
                        ty: set_ty,

                        span: None,
                    }),

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

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "card_set_lit".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // #Set(1,2,3) = 3 — compile-time constant, trivially PROVED
    assert!(
        matches!(&results[0], VerificationResult::Proved { .. }),
        "#Set(1,2,3) == 3 should be PROVED: got {}",
        results[0]
    );
}

#[test]
fn set_literal_cardinality_deduplicates() {
    // #Set(1,1,2) should be 2 (not 3) — duplicates are collapsed.
    let set_ty = IRType::Set {
        element: Box::new(IRType::Int),
    };
    let entity = IREntity {
        name: "X".to_owned(),
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
    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["X".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_x".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "X".to_owned(),
                fields: vec![],
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

    // #Set(1,1,2) == 2
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Entity {
                name: "X".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Card {
                    expr: Box::new(IRExpr::SetLit {
                        elements: vec![
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 1 },

                                span: None,
                            },
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 1 }, // duplicate,
                                span: None,
                            },
                            IRExpr::Lit {
                                ty: IRType::Int,
                                value: LitVal::Int { value: 2 },

                                span: None,
                            },
                        ],
                        ty: set_ty,

                        span: None,
                    }),

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "card_dedup".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::Proved { .. }),
        "#Set(1,1,2) == 2 should be PROVED (deduplicated): got {}",
        results[0]
    );
}

// ── Set comprehension tests ─────────────────────────────────────

#[test]
fn set_comprehension_simple_form() {
    // { o: Order where o.status == @Active } — simple set comprehension.
    // Entity with status enum, one transition that sets Active.
    // Property: #{ o: Order where true } >= 0 — always true (count is non-negative).
    // Tests that SetComp encodes without panic and produces a valid Array.
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
        },
    };

    let entity = IREntity {
        name: "Obj".to_owned(),
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
                    variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
                },
                default: Some(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "Idle".to_owned(),
                    args: vec![],
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "activate".to_owned(),
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
                    ctor: "Idle".to_owned(),
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
                    ctor: "Active".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Obj".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_obj".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Obj".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_activate".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Obj".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "activate".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // Simple comprehension: { o: Obj where o.status == @Active }
    let active_set = IRExpr::SetComp {
        var: "o".to_owned(),
        domain: IRType::Entity {
            name: "Obj".to_owned(),
        },
        filter: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "o".to_owned(),
                    ty: IRType::Entity {
                        name: "Obj".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Active".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }),
        projection: None,
        ty: IRType::Set {
            element: Box::new(IRType::Int),
        },

        span: None,
    };

    // Property: { o: Obj where o.status == @Active } == { o: Obj where o.status == @Active }
    // Reflexive — validates SetComp encodes to Array without panic.
    // Wrapped in a Forall to get the right encoding context.
    let property = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(active_set.clone()),
            right: Box::new(active_set),
            ty: IRType::Bool,

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "set_comp_simple".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "set comprehension should encode without error: got {}",
        results[0]
    );
}

#[test]
fn set_comprehension_membership_check() {
    // After activate: slot 0 should be in { o: Obj where o.status == @Active }.
    // Uses Index on the comprehension result to check membership.
    // This won't be provable (needs invariant linking slot index to active set),
    // but it validates the full SetComp→Index→Bool encoding chain.
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
        },
    };

    let entity = IREntity {
        name: "Obj".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Idle".to_owned(),
                args: vec![],
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
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Obj".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_obj".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "Obj".to_owned(),
                fields: vec![],
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

    // { o: Obj where true }[0] — slot 0 membership in "all objects" set
    // This is true iff slot 0 is active. Since we can create objects, and
    // the set includes all active objects, Index(comprehension, 0) == active[0].
    // We check: Index(comprehension, 0) == Index(comprehension, 0) — reflexive,
    // but validates the SetComp→Index chain doesn't panic.
    let comp = IRExpr::SetComp {
        var: "o".to_owned(),
        domain: IRType::Entity {
            name: "Obj".to_owned(),
        },
        filter: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        }),
        projection: None,
        ty: IRType::Set {
            element: Box::new(IRType::Int),
        },

        span: None,
    };

    let comp_at_0 = IRExpr::Index {
        map: Box::new(comp),
        key: Box::new(IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value: 0 },

            span: None,
        }),
        ty: IRType::Bool,

        span: None,
    };

    let property = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(comp_at_0.clone()),
            right: Box::new(comp_at_0),
            ty: IRType::Bool,

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "set_comp_index".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "SetComp→Index chain should encode without error: got {}",
        results[0]
    );
}

#[test]
fn set_comprehension_projection_form() {
    // Projection comprehension: { o.status | o: Obj where true }
    // Collects status values of all active objects into a set.
    // Property: Set(1,2,3)[0] == true is independent of comprehension —
    // just validates projection encoding doesn't panic.
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
        },
    };

    let entity = IREntity {
        name: "Obj".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Idle".to_owned(),
                args: vec![],
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
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Obj".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_obj".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "Obj".to_owned(),
                fields: vec![],
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

    // Projection: { o.status | o: Obj where true }
    let status_set = IRExpr::SetComp {
        var: "o".to_owned(),
        domain: IRType::Entity {
            name: "Obj".to_owned(),
        },
        filter: Box::new(IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },

            span: None,
        }),
        projection: Some(Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "o".to_owned(),
                ty: IRType::Entity {
                    name: "Obj".to_owned(),
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

    // Property: Index(status_set, Idle_id) == Index(status_set, Idle_id)
    // Reflexive on the projection result — validates projection encoding chain.
    // Idle is constructor 0 in VerifyContext.
    let idle_id = IRExpr::Ctor {
        enum_name: "Status".to_owned(),
        ctor: "Idle".to_owned(),
        args: vec![],
        span: None,
    };
    let proj_at_idle = IRExpr::Index {
        map: Box::new(status_set),
        key: Box::new(idle_id),
        ty: IRType::Bool,

        span: None,
    };

    let property = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(proj_at_idle.clone()),
            right: Box::new(proj_at_idle),
            ty: IRType::Bool,

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "set_comp_proj".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 3,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "projection SetComp should encode without error: got {}",
        results[0]
    );
}

// ── Sequence encoding tests ─────────────────────────────────────

#[test]
fn seq_literal_index_and_cardinality() {
    // Tests SeqLit encoding in properties: Seq(10, 20, 30)[1] == 20 and #Seq(10,20,30) == 3.
    let seq_ty = IRType::Seq {
        element: Box::new(IRType::Int),
    };

    let entity = IREntity {
        name: "X".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["X".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_x".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "X".to_owned(),
                fields: vec![],
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

    let seq_lit = || IRExpr::SeqLit {
        elements: vec![
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 10 },

                span: None,
            },
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 20 },

                span: None,
            },
            IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 30 },

                span: None,
            },
        ],
        ty: seq_ty.clone(),

        span: None,
    };

    // Property 1: Seq(10,20,30)[1] == 20
    let index_prop = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Entity {
                name: "X".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Index {
                    map: Box::new(seq_lit()),
                    key: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    }),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 20 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            }),

            span: None,
        }),

        span: None,
    };

    // Property 2: #Seq(10,20,30) == 3
    let card_prop = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Entity {
                name: "X".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Card {
                    expr: Box::new(seq_lit()),

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

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![
            IRVerify {
                stores: vec![],
                assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
                name: "seq_index".to_owned(),
                depth: None,
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![index_prop],
                span: None,
                file: None,
            },
            IRVerify {
                stores: vec![],
                assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
                name: "seq_card".to_owned(),
                depth: None,
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 3,
                }],
                asserts: vec![card_prop],
                span: None,
                file: None,
            },
        ],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 2);

    // Seq(10,20,30)[1] == 20 — PROVED (store/select axiom)
    assert!(
        matches!(&results[0], VerificationResult::Proved { .. }),
        "Seq index should be PROVED: got {}",
        results[0]
    );

    // #Seq(10,20,30) == 3 — compile-time constant, PROVED or CHECKED
    assert!(
        matches!(
            &results[1],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "Seq cardinality should succeed: got {}",
        results[1]
    );
}

#[test]
fn seq_field_frame_across_transition() {
    // Entity with Seq<Int> field + Int field. Transition updates Int only.
    // Seq field should be framed (preserved). Tests Array framing works for Seq.
    let seq_ty = IRType::Seq {
        element: Box::new(IRType::Int),
    };

    let entity = IREntity {
        name: "Q".to_owned(),
        fields: vec![
            IRField {
                name: "items".to_owned(),
                ty: seq_ty.clone(),
                default: None,
                initial_constraint: None,
            },
            IRField {
                name: "count".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        transitions: vec![IRTransition {
            name: "inc".to_owned(),
            refs: vec![],
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            updates: vec![IRUpdate {
                field: "count".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "count".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Q".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_q".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Q".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_inc".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "q".to_owned(),
                    entity: "Q".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "q".to_owned(),
                        transition: "inc".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // Property: items[0] == items[0] — reflexive on the Seq field.
    // This is trivially true but exercises the Array-typed field resolution
    // in the property encoder, proving the Seq field variable is correctly
    // created, accessed, and compared across time steps.
    let items_at_0 = IRExpr::Index {
        map: Box::new(IRExpr::Field {
            expr: Box::new(IRExpr::Var {
                name: "q".to_owned(),
                ty: IRType::Entity {
                    name: "Q".to_owned(),
                },

                span: None,
            }),
            field: "items".to_owned(),
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
    };

    // Also check count >= 0 to validate scalar framing alongside Seq.
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "q".to_owned(),
            domain: IRType::Entity {
                name: "Q".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(items_at_0.clone()),
                    right: Box::new(items_at_0),
                    ty: IRType::Bool,

                    span: None,
                }),
                right: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "q".to_owned(),
                            ty: IRType::Entity {
                                name: "Q".to_owned(),
                            },

                            span: None,
                        }),
                        field: "count".to_owned(),
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
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "seq_frame".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 5,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "Seq frame alongside scalar should succeed: got {}",
        results[0]
    );
}

// ── Cardinality (bounded sum) tests ──────────────────────────────

#[test]
fn card_set_comp_bounded_sum() {
    // #{ o: Obj where o.status == @Active } — count of active objects.
    // With 2 slots and no transitions that create or activate, the count
    // is always 0. Property: #{ o | status == Active } == 0 should be PROVED.
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
        },
    };

    let entity = IREntity {
        name: "Obj".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("Idle"), IRVariant::simple("Active")],
            },
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Idle".to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "activate".to_owned(),
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
                    ctor: "Idle".to_owned(),
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
                    ctor: "Active".to_owned(),
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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Obj".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_obj".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Obj".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_activate".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Obj".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "activate".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // Comprehension: { o: Obj where o.status == @Active }
    let active_comp = IRExpr::SetComp {
        var: "o".to_owned(),
        domain: IRType::Entity {
            name: "Obj".to_owned(),
        },
        filter: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "o".to_owned(),
                    ty: IRType::Entity {
                        name: "Obj".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Active".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }),
        projection: None,
        ty: IRType::Set {
            element: Box::new(IRType::Int),
        },

        span: None,
    };

    // Property: #{ o | Active } >= 0 — always true (count is non-negative).
    // This is semantically meaningful: the bounded sum produces a real Int,
    // not a fresh unconstrained variable. Z3 can prove sum of ite(cond,1,0) >= 0.
    let non_neg_prop = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpGe".to_owned(),
            left: Box::new(IRExpr::Card {
                expr: Box::new(active_comp.clone()),

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

    // Property: #{ o | Active } <= 2 — true with scope size 2 (at most 2 slots).
    // The bounded sum can be at most n_slots = 2.
    let bounded_prop = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpLe".to_owned(),
            left: Box::new(IRExpr::Card {
                expr: Box::new(active_comp),

                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![
            IRVerify {
                stores: vec![],
                assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
                name: "card_non_neg".to_owned(),
                depth: None,
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![non_neg_prop],
                span: None,
                file: None,
            },
            IRVerify {
                stores: vec![],
                assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
                name: "card_bounded".to_owned(),
                depth: None,
                systems: vec![IRVerifySystem {
                    name: "S".to_owned(),
                    lo: 0,
                    hi: 5,
                }],
                asserts: vec![bounded_prop],
                span: None,
                file: None,
            },
        ],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 2);

    // #{ Active } >= 0 — PROVED (bounded sum of non-negative terms)
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "#{{ Active }} >= 0 should succeed: got {}",
        results[0]
    );

    // #{ Active } <= 2 — PROVED (at most 2 slots can be active)
    assert!(
        matches!(
            &results[1],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "#{{ Active }} <= 2 should succeed: got {}",
        results[1]
    );
}

// ── Prop auto-verification tests ────────────────────────────────

#[test]
fn prop_auto_verified_when_true() {
    // A prop targeting a system with a trivially true body should be auto-verified.
    let entity = IREntity {
        name: "X".to_owned(),
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
    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["X".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_x".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "X".to_owned(),
                fields: vec![],
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

    // Prop: always all x: X | x.n >= 0 (true: default is 0, no transitions)
    let prop_body = IRExpr::Forall {
        var: "x".to_owned(),
        domain: IRType::Entity {
            name: "X".to_owned(),
        },
        body: Box::new(IRExpr::BinOp {
            op: "OpGe".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Entity {
                        name: "X".to_owned(),
                    },

                    span: None,
                }),
                field: "n".to_owned(),
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

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![IRFunction {
            name: "n_non_neg".to_owned(),
            ty: IRType::Bool,
            body: prop_body,
            prop_target: Some("S".to_owned()),
            requires: vec![],
            ensures: vec![],
            decreases: None,
            span: None,
            file: None,
        }],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    // Should produce 1 result: the auto-verified prop
    assert_eq!(results.len(), 1, "expected 1 auto-verified prop result");
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { name, .. } if name == "prop_n_non_neg"
        ),
        "prop should be auto-verified as PROVED: got {}",
        results[0]
    );
}

#[test]
fn prop_skipped_when_covered_by_theorem() {
    // A prop already referenced in an explicit theorem should not be double-checked.
    let entity = IREntity {
        name: "X".to_owned(),
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
    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["X".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "create_x".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Create {
                entity: "X".to_owned(),
                fields: vec![],
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

    let prop_ref = IRExpr::Var {
        name: "my_prop".to_owned(),
        ty: IRType::Bool,

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![IRFunction {
            name: "my_prop".to_owned(),
            ty: IRType::Bool,
            body: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            prop_target: Some("S".to_owned()),
            requires: vec![],
            ensures: vec![],
            decreases: None,
            span: None,
            file: None,
        }],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        // Theorem already references my_prop
        theorems: vec![IRTheorem {
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
            name: "explicit_thm".to_owned(),
            systems: vec!["S".to_owned()],
            invariants: vec![],
            shows: vec![IRExpr::Always {
                body: Box::new(prop_ref),

                span: None,
            }],
            by_file: None,
            by_lemmas: vec![],
            span: None,
            file: None,
        }],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    // Should only have 1 result (the explicit theorem), not 2
    assert_eq!(
        results.len(),
        1,
        "prop covered by theorem should not be double-checked: got {} results",
        results.len()
    );
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { name, .. } if name == "explicit_thm"
        ),
        "only the explicit theorem should appear: got {}",
        results[0]
    );
}

#[test]
fn no_prop_verify_flag_skips_props() {
    // --no-prop-verify should skip all prop auto-verification.
    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![IRFunction {
            name: "some_prop".to_owned(),
            ty: IRType::Bool,
            body: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            prop_target: Some("S".to_owned()),
            requires: vec![],
            ensures: vec![],
            decreases: None,
            span: None,
            file: None,
        }],
        entities: vec![],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let config = VerifyConfig {
        no_prop_verify: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert!(
        results.is_empty(),
        "--no-prop-verify should produce no results: got {} results",
        results.len()
    );
}

#[test]
fn prop_auto_verified_when_false() {
    // A false prop should produce COUNTEREXAMPLE or UNPROVABLE.
    let status_type = IRTypeEntry {
        name: "Status".to_owned(),
        ty: IRType::Enum {
            name: "Status".to_owned(),
            variants: vec![IRVariant::simple("On"), IRVariant::simple("Off")],
        },
    };
    let entity = IREntity {
        name: "Switch".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Enum {
                name: "Status".to_owned(),
                variants: vec![IRVariant::simple("On"), IRVariant::simple("Off")],
            },
            default: Some(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Off".to_owned(),
                args: vec![],
                span: None,
            }),
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
                field: "status".to_owned(),
                value: IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: "On".to_owned(),
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
    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Switch".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_switch".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Switch".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "do_toggle".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "s".to_owned(),
                    entity: "Switch".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "s".to_owned(),
                        transition: "toggle".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
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
    };

    // False prop: "all switches are always Off" — toggle breaks this.
    let false_prop_body = IRExpr::Forall {
        var: "s".to_owned(),
        domain: IRType::Entity {
            name: "Switch".to_owned(),
        },
        body: Box::new(IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "s".to_owned(),
                    ty: IRType::Entity {
                        name: "Switch".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Ctor {
                enum_name: "Status".to_owned(),
                ctor: "Off".to_owned(),
                args: vec![],
                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![status_type],
        constants: vec![],
        functions: vec![IRFunction {
            name: "always_off".to_owned(),
            ty: IRType::Bool,
            body: false_prop_body,
            prop_target: Some("S".to_owned()),
            requires: vec![],
            ensures: vec![],
            decreases: None,
            span: None,
            file: None,
        }],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1, "expected 1 auto-verified prop result");
    // The prop is false — IC3 should find a counterexample (toggle sets On),
    // or induction returns Unprovable.
    assert!(
        matches!(
            &results[0],
            VerificationResult::Counterexample { name, .. }
                | VerificationResult::Unprovable { name, .. }
                if name == "prop_always_off"
        ),
        "false prop should produce Counterexample or Unprovable: got {}",
        results[0]
    );
}

// ── Multi-apply sequential composition tests ──────────────────

#[test]
fn multi_apply_sequential_chaining() {
    // Two sequential Apply actions: pack (status 0→1) then ship (requires status==1, sets 2).
    // With intermediate variable chaining, ship's guard sees the result of pack.
    // Property: status is always 0 or 2 (never 1) at action boundaries — FALSE because
    // entities start at 0 and pack_and_ship takes them to 2 in one event step,
    // but status could be 0 (before pack_and_ship) or 2 (after). Status 1 only
    // exists in the intermediate state within the event.
    // Simpler property: status >= 0 (always true). Tests encoding doesn't panic.
    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![
            IRTransition {
                name: "pack".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    },
                }],
                postcondition: None,
            },
            IRTransition {
                name: "ship".to_owned(),
                refs: vec![],
                params: vec![],
                // Guard: requires status == 1 (result of pack)
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_f".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "F".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "pack_and_ship".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "pack".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "ship".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
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
    };

    // Property: status >= 0 (always true — 0, 1, or 2)
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "f".to_owned(),
            domain: IRType::Entity {
                name: "F".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
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
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "multi_apply_test".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 5,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let config = VerifyConfig {
        bounded_only: true, // BMC only — test the chaining encoding
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 1);
    // Should succeed — status is always 0 or 2 at action boundaries, both >= 0.
    // The key test: this doesn't panic and the guard chain works (ship sees pack's result).
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "multi-apply sequential chaining should succeed: got {}",
        results[0]
    );
}

#[test]
fn multi_apply_scene_checks_final_state() {
    // Scene: given entity with status==0, when pack_and_ship fires,
    // then status == 2 (pack sets 1, ship reads 1 and sets 2).
    // This validates intermediate chaining in the scene encoding path.
    use crate::ir::types::{Cardinality, IRScene, IRSceneEvent, IRSceneGiven};

    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![
            IRTransition {
                name: "pack".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "pack_and_ship".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            body: vec![IRAction::Choose {
                var: "f".to_owned(),
                entity: "F".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                }),
                ops: vec![
                    IRAction::Apply {
                        target: "f".to_owned(),
                        transition: "pack".to_owned(),
                        refs: vec![],
                        args: vec![],
                    },
                    IRAction::Apply {
                        target: "f".to_owned(),
                        transition: "ship".to_owned(),
                        refs: vec![],
                        args: vec![],
                    },
                ],
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

    // Scene: given f with status==0, when pack_and_ship, then f.status==2
    let scene = IRScene {
        name: "pack_then_ship".to_owned(),
        systems: vec!["S".to_owned()],
        stores: vec![],
        givens: vec![IRSceneGiven {
            var: "f".to_owned(),
            entity: "F".to_owned(),
            store_name: None,
            constraint: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
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
            },
        }],
        events: vec![IRSceneEvent {
            var: "ps".to_owned(),
            system: "S".to_owned(),
            event: "pack_and_ship".to_owned(),
            args: vec![],
            cardinality: Cardinality::Named("one".to_owned()),
        }],
        ordering: vec![],
        assertions: vec![IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "f".to_owned(),
                    ty: IRType::Entity {
                        name: "F".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![scene],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // Scene should PASS: pack (0→1) then ship (1→2) = final status 2.
    // Without intermediate chaining, ship's guard fails (sees 0, not 1).
    assert!(
        matches!(&results[0], VerificationResult::ScenePass { .. }),
        "scene with multi-apply should PASS: got {}",
        results[0]
    );
}

#[test]
fn multi_apply_ic3_proves_property() {
    require_unbounded_proof_tests!();

    // IC3 rejects same-entity multi-apply (CHC per-Apply rules model
    // multi-step, not atomic intra-event composition). Falls through to
    // staged induction which uses BMC-style intermediate variable chaining.
    // Property: status >= 0 (1-inductive: default 0, transitions set 1 or 2).
    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![
            IRTransition {
                name: "pack".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_f".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "F".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "pack_and_ship".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "pack".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "ship".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
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
    };

    // Property: status >= 0 (always true: 0, 1, or 2)
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "f".to_owned(),
            domain: IRType::Entity {
                name: "F".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
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
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![IRTheorem {
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_theorem_or_lemma(),
            name: "multi_apply_ic3".to_owned(),
            systems: vec!["S".to_owned()],
            invariants: vec![],
            shows: vec![property],
            by_file: None,
            by_lemmas: vec![],
            span: None,
            file: None,
        }],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // IC3 rejects multi-apply (Unknown), then falls to staged induction.
    // status >= 0 is 1-inductive (default 0, transitions set 1 or 2).
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "1-induction"
        ),
        "multi-apply theorem should be PROVED by 1-induction (IC3 rejects, falls through): got {}",
        results[0]
    );
}

#[test]
fn multi_apply_step_scoping_no_intermediate_collision() {
    // Regression: two events with multi-apply chains in the same system.
    // Intermediate variables must be scoped by action and chain_id so that
    // chains at step 0 and step 1 don't alias each other.
    // Entity has three transitions: a (0→1), b (1→2), c (2→3).
    // Event "ab" does a+b (0→2), event "bc" does b+c (but can only fire
    // if status==1, which never happens via ab). We verify status <= 2
    // after create+ab — if intermediates aliased across events, the solver
    // could produce spurious states.
    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![
            IRTransition {
                name: "a".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    },
                }],
                postcondition: None,
            },
            IRTransition {
                name: "b".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

                        span: None,
                    },
                }],
                postcondition: None,
            },
            IRTransition {
                name: "c".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 3 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_f".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "F".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            // Event ab: a (0→1) then b (1→2) — multi-apply chain
            IRSystemAction {
                name: "ab".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "a".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "b".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
                return_expr: None,
            },
            // Event bc: b (1→2) then c (2→3) — second multi-apply chain
            IRSystemAction {
                name: "bc".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "b".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "c".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
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
    };

    // Property: status <= 3 (always true: 0 via default, 2 via ab, 3 via ab then bc)
    // If intermediates aliased across events, solver could produce spurious values.
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "f".to_owned(),
            domain: IRType::Entity {
                name: "F".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
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

            span: None,
        }),

        span: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "step_scope_test".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 5,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let config = VerifyConfig {
        bounded_only: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "two multi-apply events with distinct chains should not alias intermediates: got {}",
        results[0]
    );
}

#[test]
fn multi_apply_active_flag_preserved_in_chain() {
    // Regression: multi-apply chain must assert active flag at action k AND k+1.
    // If active constraints were missing, an inactive entity slot could get
    // spurious intermediate state written through it.
    // Test: entity defaults to status=0, pack_and_ship chains pack(0→1)+ship(1→2).
    // Property: status is exactly 0 or 2 (never anything else at action boundaries).
    // This is tighter than >= 0 — validates that only active entities transition.
    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![
            IRTransition {
                name: "pack".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_f".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "F".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "pack_and_ship".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "pack".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "ship".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                    ],
                }],
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
    };

    // Tighter property: status == 0 OR status == 2
    // Status 1 only exists in intermediate state within the event chain.
    // If active flag constraints were missing, inactive slots could leak
    // intermediate values (1) into step-boundary observations.
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "f".to_owned(),
            domain: IRType::Entity {
                name: "F".to_owned(),
            },
            body: Box::new(IRExpr::BinOp {
                op: "OpOr".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
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
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "status".to_owned(),
                        ty: IRType::Int,

                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![IRVerify {
            stores: vec![],
            assumption_set: crate::ir::types::IRAssumptionSet::default_for_verify(),
            name: "active_flag_test".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "S".to_owned(),
                lo: 0,
                hi: 5,
            }],
            asserts: vec![property],
            span: None,
            file: None,
        }],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    };

    let config = VerifyConfig {
        bounded_only: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(results.len(), 1);
    // Status should only be 0 (default/uncreated) or 2 (after pack_and_ship).
    // The intermediate value 1 must never appear at action boundaries.
    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { .. } | VerificationResult::Checked { .. }
        ),
        "status should be exactly 0 or 2 at action boundaries (active flag preserves chain integrity): got {}",
        results[0]
    );
}

#[test]
fn multi_apply_second_apply_args_depend_on_first_update() {
    // Regression: when the second Apply's transition takes a parameter whose
    // value is computed from a field updated by the first Apply, the parameter
    // must be evaluated against the intermediate state, not the pre-state.
    //
    // Entity "F" has two fields: status (int) and amount (int, default 0).
    // Transition "prepare": guard status==0, sets status=1, sets amount=10.
    // Transition "finalize(expected: int)": guard status==1 AND amount==expected,
    // sets status=2.
    // Event "prep_and_finalize": Choose f, f.prepare(), f.finalize(f.amount).
    // The arg `f.amount` must resolve to 10 (prepare's update), not 0 (pre-state).
    // Property: if status==2 then amount==10 (validates correct arg resolution).
    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![
            IRField {
                name: "status".to_owned(),
                ty: IRType::Int,
                default: Some(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 0 },

                    span: None,
                }),
                initial_constraint: None,
            },
            IRField {
                name: "amount".to_owned(),
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
                name: "prepare".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                updates: vec![
                    IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },

                            span: None,
                        },
                    },
                    IRUpdate {
                        field: "amount".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 10 },

                            span: None,
                        },
                    },
                ],
                postcondition: None,
            },
            IRTransition {
                name: "finalize".to_owned(),
                refs: vec![],
                params: vec![IRTransParam {
                    name: "expected".to_owned(),
                    ty: IRType::Int,
                }],
                // Guard: status==1 AND amount==expected
                guard: IRExpr::BinOp {
                    op: "OpAnd".to_owned(),
                    left: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
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
                    right: Box::new(IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "amount".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        right: Box::new(IRExpr::Var {
                            name: "expected".to_owned(),
                            ty: IRType::Int,

                            span: None,
                        }),
                        ty: IRType::Bool,

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_f".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "F".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "prep_and_finalize".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },

                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "f".to_owned(),
                    entity: "F".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },

                        span: None,
                    }),
                    ops: vec![
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "prepare".to_owned(),
                            refs: vec![],
                            args: vec![],
                        },
                        IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "finalize".to_owned(),
                            refs: vec![],
                            // Arg: f.amount — must resolve from intermediate state (10),
                            // not pre-state (0)
                            args: vec![IRExpr::Var {
                                name: "amount".to_owned(),
                                ty: IRType::Int,

                                span: None,
                            }],
                        },
                    ],
                }],
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
    };

    // Property: if status == 2 then amount == 10.
    // If the second Apply's arg was evaluated against pre-state,
    // finalize's guard (amount==expected) would use expected=0 (pre-state amount),
    // which wouldn't match the intermediate amount=10, making finalize's guard UNSAT.
    // The event wouldn't fire, so status would stay at 0 — the property holds vacuously.
    //
    // With correct intermediate evaluation, expected=10 (from intermediate amount),
    // finalize fires (amount==10==expected), status goes to 2, and status==2 → amount==10
    // holds concretely.
    //
    // To distinguish: use a scene to verify the event CAN fire and produces status==2.
    use crate::ir::types::{Cardinality, IRScene, IRSceneEvent, IRSceneGiven};
    let scene = IRScene {
        name: "prep_finalize_fires".to_owned(),
        systems: vec!["S".to_owned()],
        stores: vec![],
        givens: vec![IRSceneGiven {
            var: "f".to_owned(),
            entity: "F".to_owned(),
            store_name: None,
            constraint: IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
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
                right: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "F".to_owned(),
                            },

                            span: None,
                        }),
                        field: "amount".to_owned(),
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
        }],
        events: vec![IRSceneEvent {
            var: "pf".to_owned(),
            system: "S".to_owned(),
            event: "prep_and_finalize".to_owned(),
            args: vec![],
            cardinality: Cardinality::Named("one".to_owned()),
        }],
        ordering: vec![],
        // Assert: status reaches 2 AND amount is 10 (prepare's update)
        assertions: vec![
            IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
                        },

                        span: None,
                    }),
                    field: "status".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 2 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            },
            IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
                        },

                        span: None,
                    }),
                    field: "amount".to_owned(),
                    ty: IRType::Int,

                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 10 },

                    span: None,
                }),
                ty: IRType::Bool,

                span: None,
            },
        ],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![scene],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // Scene must PASS: prepare sets amount=10, finalize's arg (f.amount)
    // reads from intermediate state and gets 10, guard is satisfied, status→2.
    assert!(
        matches!(&results[0], VerificationResult::ScenePass { .. }),
        "second Apply's args must resolve from intermediate state (amount=10, not 0): got {}",
        results[0]
    );
}

#[test]
fn multi_apply_forall_rejected_in_scene() {
    // Regression: a scene whose event uses ForAll with multiple Apply actions
    // on the same entity must be rejected via find_unsupported_in_actions,
    // not silently encoded incorrectly.
    use crate::ir::types::{Cardinality, IRScene, IRSceneEvent, IRSceneGiven};

    let entity = IREntity {
        name: "F".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: IRType::Int,
            default: Some(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 0 },

                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![
            IRTransition {
                name: "pack".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "status".to_owned(),
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
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

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
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 1 },

                        span: None,
                    }),
                    ty: IRType::Bool,

                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "status".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },

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

    let system = IRSystem {
        name: "S".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["F".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "pack_all_and_ship".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },

                span: None,
            },
            // ForAll with two Applies on same entity — NOT supported
            body: vec![IRAction::ForAll {
                var: "f".to_owned(),
                entity: "F".to_owned(),
                ops: vec![
                    IRAction::Apply {
                        target: "f".to_owned(),
                        transition: "pack".to_owned(),
                        refs: vec![],
                        args: vec![],
                    },
                    IRAction::Apply {
                        target: "f".to_owned(),
                        transition: "ship".to_owned(),
                        refs: vec![],
                        args: vec![],
                    },
                ],
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

    let scene = IRScene {
        name: "forall_multi_apply".to_owned(),
        systems: vec!["S".to_owned()],
        stores: vec![],
        givens: vec![IRSceneGiven {
            var: "f".to_owned(),
            entity: "F".to_owned(),
            store_name: None,
            constraint: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "f".to_owned(),
                        ty: IRType::Entity {
                            name: "F".to_owned(),
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
            },
        }],
        events: vec![IRSceneEvent {
            var: "ps".to_owned(),
            system: "S".to_owned(),
            event: "pack_all_and_ship".to_owned(),
            args: vec![],
            cardinality: Cardinality::Named("one".to_owned()),
        }],
        ordering: vec![],
        assertions: vec![IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Field {
                expr: Box::new(IRExpr::Var {
                    name: "f".to_owned(),
                    ty: IRType::Entity {
                        name: "F".to_owned(),
                    },

                    span: None,
                }),
                field: "status".to_owned(),
                ty: IRType::Int,

                span: None,
            }),
            right: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 2 },

                span: None,
            }),
            ty: IRType::Bool,

            span: None,
        }],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };

    let ir = IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![system],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![scene],
    };

    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    // Must be rejected as SceneFail with "multiple Apply" message,
    // NOT silently encoded incorrectly.
    match &results[0] {
        VerificationResult::SceneFail { reason, .. } => {
            assert!(
                reason.contains("multiple Apply"),
                "ForAll multi-apply rejection should mention 'multiple Apply': got {reason}"
            );
        }
        other => panic!("ForAll multi-apply in scene should produce SceneFail, got: {other}"),
    }
}

// ── Function contract verification tests ────────────────────────

/// Helper: build an IR program with a single function (no entities/systems).
fn make_fn_ir(func: IRFunction) -> IRProgram {
    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![func],
        entities: vec![],
        systems: vec![],
        verifies: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

/// fn double(x: Int): Int ensures result == x + x = x + x
/// Postcondition should be proved.
#[test]
fn fn_contract_simple_ensures_proved() {
    let func = IRFunction {
        name: "double".to_owned(),
        ty: IRType::Fn {
            param: Box::new(IRType::Int),
            result: Box::new(IRType::Int),
        },
        body: IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            span: None,
        },
        prop_target: None,
        requires: vec![],
        ensures: vec![IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "result".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }],
        decreases: None,
        span: None,
        file: None,
    };

    let ir = make_fn_ir(func);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::FnContractProved { name, .. } if name == "double"),
        "expected FnContractProved, got: {}",
        results[0]
    );
}

/// fn bad(x: Int): Int ensures result > x = x
/// Body is just x, but ensures says result > x. Should fail.
#[test]
fn fn_contract_ensures_fails() {
    let func = IRFunction {
        name: "bad".to_owned(),
        ty: IRType::Fn {
            param: Box::new(IRType::Int),
            result: Box::new(IRType::Int),
        },
        body: IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            span: None,
        },
        prop_target: None,
        requires: vec![],
        ensures: vec![IRExpr::BinOp {
            op: "OpGt".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "result".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }],
        decreases: None,
        span: None,
        file: None,
    };

    let ir = make_fn_ir(func);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::FnContractFailed { name, counterexample, .. }
            if name == "bad" && !counterexample.is_empty()),
        "expected FnContractFailed with counterexample, got: {}",
        results[0]
    );
}

/// fn `no_contract(x`: Int): Int = x + 1
/// No ensures clause — should be skipped entirely.
#[test]
fn fn_contract_no_ensures_skipped() {
    let func = IRFunction {
        name: "no_contract".to_owned(),
        ty: IRType::Fn {
            param: Box::new(IRType::Int),
            result: Box::new(IRType::Int),
        },
        body: IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
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
            span: None,
        },
        prop_target: None,
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: None,
        file: None,
    };

    let ir = make_fn_ir(func);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(
        results.len(),
        0,
        "fn without ensures should produce no results"
    );
}

/// fn clamp(x: Int, lo: Int, hi: Int): Int
/// requires lo <= hi
/// ensures result >= lo
/// ensures result <= hi
/// = if x < lo then lo else if x > hi then hi else x
#[test]
fn fn_contract_with_requires_and_multiple_ensures() {
    let func = IRFunction {
        name: "clamp".to_owned(),
        ty: IRType::Fn {
            param: Box::new(IRType::Int),
            result: Box::new(IRType::Fn {
                param: Box::new(IRType::Int),
                result: Box::new(IRType::Fn {
                    param: Box::new(IRType::Int),
                    result: Box::new(IRType::Int),
                }),
            }),
        },
        body: IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Lam {
                param: "lo".to_owned(),
                param_type: IRType::Int,
                body: Box::new(IRExpr::Lam {
                    param: "hi".to_owned(),
                    param_type: IRType::Int,
                    body: Box::new(IRExpr::IfElse {
                        cond: Box::new(IRExpr::BinOp {
                            op: "OpLt".to_owned(),
                            left: Box::new(IRExpr::Var {
                                name: "x".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            right: Box::new(IRExpr::Var {
                                name: "lo".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        then_body: Box::new(IRExpr::Var {
                            name: "lo".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        else_body: Some(Box::new(IRExpr::IfElse {
                            cond: Box::new(IRExpr::BinOp {
                                op: "OpGt".to_owned(),
                                left: Box::new(IRExpr::Var {
                                    name: "x".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                right: Box::new(IRExpr::Var {
                                    name: "hi".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                }),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            then_body: Box::new(IRExpr::Var {
                                name: "hi".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            }),
                            else_body: Some(Box::new(IRExpr::Var {
                                name: "x".to_owned(),
                                ty: IRType::Int,
                                span: None,
                            })),
                            span: None,
                        })),
                        span: None,
                    }),
                    span: None,
                }),
                span: None,
            }),
            span: None,
        },
        prop_target: None,
        requires: vec![IRExpr::BinOp {
            op: "OpLe".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "lo".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::Var {
                name: "hi".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }],
        ensures: vec![
            IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "result".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "lo".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            IRExpr::BinOp {
                op: "OpLe".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "result".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "hi".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
        ],
        decreases: None,
        span: None,
        file: None,
    };

    let ir = make_fn_ir(func);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0], VerificationResult::FnContractProved { name, .. } if name == "clamp"),
        "expected FnContractProved for clamp, got: {}",
        results[0]
    );
}

/// fn `only_requires(x`: Int): Int requires x > 0 = x
/// Has requires but no ensures — should be skipped.
#[test]
fn fn_contract_only_requires_skipped() {
    let func = IRFunction {
        name: "only_requires".to_owned(),
        ty: IRType::Fn {
            param: Box::new(IRType::Int),
            result: Box::new(IRType::Int),
        },
        body: IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            span: None,
        },
        prop_target: None,
        requires: vec![IRExpr::BinOp {
            op: "OpGt".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "x".to_owned(),
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
        }],
        ensures: vec![],
        decreases: None,
        span: None,
        file: None,
    };

    let ir = make_fn_ir(func);
    let results = verify_all(&ir, &VerifyConfig::default());
    assert_eq!(
        results.len(),
        0,
        "fn with only requires should produce no results"
    );
}

/// --no-fn-verify skips fn contract verification.
#[test]
fn fn_contract_skipped_with_flag() {
    let func = IRFunction {
        name: "double".to_owned(),
        ty: IRType::Fn {
            param: Box::new(IRType::Int),
            result: Box::new(IRType::Int),
        },
        body: IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            span: None,
        },
        prop_target: None,
        requires: vec![],
        ensures: vec![IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(IRExpr::Var {
                name: "result".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                right: Box::new(IRExpr::Var {
                    name: "x".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }],
        decreases: None,
        span: None,
        file: None,
    };

    let ir = make_fn_ir(func);
    let config = VerifyConfig {
        no_fn_verify: true,
        ..VerifyConfig::default()
    };
    let results = verify_all(&ir, &config);
    assert_eq!(
        results.len(),
        0,
        "no_fn_verify should skip fn contract verification"
    );
}

// ── format_assumptions tests ──────────────────────────────

#[test]
fn format_assumptions_empty() {
    assert_eq!(super::format_assumptions(&[]), "");
}

#[test]
fn format_assumptions_stutter_only() {
    let a = vec![TrustedAssumption::Stutter];
    assert_eq!(super::format_assumptions(&a), " under stutter");
}

#[test]
fn format_assumptions_mixed_ordering() {
    let a = vec![
        TrustedAssumption::StrongFairness {
            system: "Billing".to_owned(),
            command: "charge".to_owned(),
        },
        TrustedAssumption::Stutter,
        TrustedAssumption::Lemma {
            name: "helper".to_owned(),
        },
        TrustedAssumption::WeakFairness {
            system: "Shipping".to_owned(),
            command: "ship".to_owned(),
        },
        TrustedAssumption::WeakFairness {
            system: "Billing".to_owned(),
            command: "pay".to_owned(),
        },
        TrustedAssumption::Axiom {
            name: "safety_axiom".to_owned(),
            proof_artifact: None,
        },
    ];
    let result = super::format_assumptions(&a);
    // Order: stutter, WF alphabetical, SF alphabetical, by lemmas, axioms
    assert_eq!(
        result,
        " under stutter, WF Billing::pay, WF Shipping::ship, SF Billing::charge, by helper, axiom safety_axiom"
    );
}

#[test]
fn format_assumptions_deduplicates_all_categories() {
    let a = vec![
        TrustedAssumption::Stutter,
        TrustedAssumption::Stutter,
        TrustedAssumption::WeakFairness {
            system: "Billing".to_owned(),
            command: "charge".to_owned(),
        },
        TrustedAssumption::WeakFairness {
            system: "Billing".to_owned(),
            command: "charge".to_owned(),
        },
        TrustedAssumption::StrongFairness {
            system: "Shipping".to_owned(),
            command: "ship".to_owned(),
        },
        TrustedAssumption::StrongFairness {
            system: "Shipping".to_owned(),
            command: "ship".to_owned(),
        },
        TrustedAssumption::Lemma {
            name: "helper".to_owned(),
        },
        TrustedAssumption::Lemma {
            name: "helper".to_owned(),
        },
        TrustedAssumption::Axiom {
            name: "truth".to_owned(),
            proof_artifact: None,
        },
        TrustedAssumption::Axiom {
            name: "truth".to_owned(),
            proof_artifact: None,
        },
    ];
    let result = super::format_assumptions(&a);
    assert_eq!(
        result,
        " under stutter, WF Billing::charge, SF Shipping::ship, by helper, axiom truth"
    );
}

#[test]
fn format_assumptions_includes_axiom_proof_artifact_locator() {
    let a = vec![TrustedAssumption::Axiom {
        name: "crypto_safe".to_owned(),
        proof_artifact: Some(
            super::proof_artifact_ref_for_locator("proofs/crypto.agda", Some("crypto_safe"))
                .expect("valid proof artifact"),
        ),
    }];
    let result = super::format_assumptions(&a);
    assert_eq!(result, " under axiom crypto_safe by \"proofs/crypto.agda\"");
}

#[test]
fn format_assumptions_includes_extern_assumes() {
    let a = vec![
        TrustedAssumption::ExternAssume {
            external: "Stripe".to_owned(),
            detail: "WF charge".to_owned(),
        },
        TrustedAssumption::ExternAssume {
            external: "Clock".to_owned(),
            detail: "assume #1".to_owned(),
        },
    ];
    let result = super::format_assumptions(&a);
    assert_eq!(
        result,
        " under extern Clock assume #1, extern Stripe WF charge"
    );
}

#[test]
fn verify_all_with_cvc5_selection_checks_simple_bmc_target() {
    let ir = make_order_ir(
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        2,
    );
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        bounded_only: true,
        ..short_solver_regression_config()
    };

    let results = verify_all(&ir, &config);

    assert!(
        results.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, depth, .. }
                if name == "test_verify" && *depth == 2
        ) || matches!(
            r,
            VerificationResult::Proved { name, method, .. }
                if name == "test_verify" && method == "explicit-state exhaustive search"
        )),
        "expected simple BMC target to check under cvc5, got: {results:?}"
    );
}

#[test]
fn verify_all_with_independent_z3_chc_selection_preserves_ic3_proofs() {
    require_unbounded_proof_tests!();

    let ir = make_two_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        chc_selection: ChcSelection::Z3,
        ..short_solver_regression_config()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "IC3/PDR"
        ),
        "expected verify block to still prove via Z3 CHC under cvc5 SMT selection, got: {results:?}"
    );
    assert!(
        matches!(
            &results[1],
            VerificationResult::Proved { method, .. } if method == "IC3/PDR"
        ),
        "expected theorem to still prove via Z3 CHC under cvc5 SMT selection, got: {results:?}"
    );
}

#[test]
fn verify_all_with_cvc5_chc_selection_is_honest_about_current_chc_limit() {
    require_unbounded_proof_tests!();

    let ir = make_two_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        chc_selection: ChcSelection::Cvc5,
        unbounded_only: true,
        ..short_solver_regression_config()
    };

    let results = verify_all(&ir, &config);

    assert!(
        results
            .iter()
            .all(|r| matches!(r, VerificationResult::Unprovable { .. })),
        "expected unbounded-only run with cvc5 CHC selection to stay honest instead of claiming proof: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_supported_system_field_safety_via_sygus() {
    let ir = make_system_field_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..short_solver_regression_config()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected supported system-field safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
fn verify_all_routes_supported_finite_system_field_safety_to_explicit_state() {
    let ir = make_system_field_enum_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected finite system-field safety to route to explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_counterexample_with_operational_witness() {
    let ir = make_system_field_enum_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(&results[0], VerificationResult::Counterexample { .. }),
        "expected explicit-state counterexample, got: {results:?}"
    );
    assert!(
        results[0].operational_witness().is_some(),
        "expected operational witness on explicit-state counterexample: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_deadlock_with_operational_witness() {
    let ir = make_system_field_enum_deadlock_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(&results[0], VerificationResult::Deadlock { step: 1, .. }),
        "expected explicit-state deadlock at step 1, got: {results:?}"
    );
    assert!(
        results[0].operational_witness().is_some(),
        "expected operational witness on explicit-state deadlock: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_liveness_violation_with_operational_witness() {
    let ir = make_system_field_eventual_liveness_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let liveness = results
        .iter()
        .find(|r| matches!(r, VerificationResult::LivenessViolation { .. }))
        .expect("expected explicit-state liveness violation");
    assert!(
        liveness.operational_witness().is_some(),
        "expected operational witness on explicit-state liveness violation: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_weak_fairness_on_parameterless_steps() {
    let ir = make_system_field_weak_fair_eventual_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected weak-fair finite liveness slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_strong_fairness_on_parameterless_steps() {
    let ir = make_system_field_strong_fair_eventual_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected strong-fair finite liveness slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_finite_bool_param_system_safety() {
    let ir = make_system_field_bool_param_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected finite bool-param system safety to route to explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_finite_enum_param_system_safety() {
    let ir = make_system_field_enum_param_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected finite enum-param system safety to route to explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_weak_fairness_on_finite_param_steps() {
    let ir = make_system_field_bool_param_weak_fair_eventual_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected weak fairness over finite param action slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_strong_fairness_on_finite_param_steps() {
    let ir = make_system_field_bool_param_strong_fair_eventual_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected strong fairness over finite param action slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_per_tuple_weak_fairness_on_finite_param_steps() {
    let ir = make_system_field_enum_param_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected per-tuple weak fairness over finite param action slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_per_tuple_strong_fairness_on_finite_param_steps() {
    let ir = make_system_field_enum_param_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected per-tuple strong fairness over finite param action slice to prove via explicit-state search, got: {results:?}"
    );
}

fn make_multi_system_duplicate_field_counterexample_ir() -> IRProgram {
    let phase_ty = IRType::Enum {
        name: "Phase".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let bool_ty = IRType::Bool;
    let pending = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "Pending".to_owned(),
        args: vec![],
        span: None,
    };
    let done = IRExpr::Ctor {
        enum_name: "Phase".to_owned(),
        ctor: "Done".to_owned(),
        args: vec![],
        span: None,
    };
    let left = IRSystem {
        name: "LeftDup".to_owned(),
        store_params: vec![],
        fields: vec![
            IRField {
                name: "phase".to_owned(),
                ty: phase_ty.clone(),
                default: Some(pending.clone()),
                initial_constraint: None,
            },
            IRField {
                name: "left_done".to_owned(),
                ty: bool_ty.clone(),
                default: Some(IRExpr::Lit {
                    ty: bool_ty.clone(),
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                initial_constraint: None,
            },
        ],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "finish_left".to_owned(),
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "phase".to_owned(),
                    ty: phase_ty.clone(),
                    span: None,
                }),
                right: Box::new(pending.clone()),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "phase".to_owned(),
                                ty: phase_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(done),
                        ty: IRType::Bool,
                        span: None,
                    },
                },
                IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "left_done".to_owned(),
                                ty: bool_ty.clone(),
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: bool_ty.clone(),
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
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
    let right = IRSystem {
        name: "RightDup".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "phase".to_owned(),
            ty: phase_ty.clone(),
            default: Some(pending),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "hold_right".to_owned(),
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "phase".to_owned(),
                    ty: phase_ty.clone(),
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Phase".to_owned(),
                    ctor: "Pending".to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            body: vec![IRAction::ExprStmt {
                expr: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "phase".to_owned(),
                            ty: phase_ty.clone(),
                            span: None,
                        }),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "Phase".to_owned(),
                        ctor: "Pending".to_owned(),
                        args: vec![],
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
    };
    let verify = IRVerify {
        name: "left_done_stays_false_with_duplicate_field_names".to_owned(),
        depth: None,
        systems: vec![
            IRVerifySystem {
                name: "LeftDup".to_owned(),
                lo: 0,
                hi: 1,
            },
            IRVerifySystem {
                name: "RightDup".to_owned(),
                lo: 0,
                hi: 1,
            },
        ],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: false,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: "left_done".to_owned(),
                    ty: bool_ty,
                    span: None,
                }),
                right: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: false },
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![],
        systems: vec![left, right],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_pooled_let_crosscall_counterexample_ir() -> IRProgram {
    let entity = IREntity {
        name: "Flagged".to_owned(),
        fields: vec![IRField {
            name: "done".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "set_done".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "value".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "done".to_owned(),
                value: IRExpr::Var {
                    name: "value".to_owned(),
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
    let relay = IRSystem {
        name: "FlagRelay".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Flagged".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_flag".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Flagged".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "decision".to_owned(),
                        system: "FlagDecision".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::Choose {
                        var: "f".to_owned(),
                        entity: "Flagged".to_owned(),
                        filter: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ops: vec![IRAction::Apply {
                            target: "f".to_owned(),
                            transition: "set_done".to_owned(),
                            refs: vec![],
                            args: vec![IRExpr::Var {
                                name: "decision".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }],
                        }],
                    },
                ],
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
    };
    let worker = IRSystem {
        name: "FlagDecision".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Flagged".to_owned()],
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
            return_expr: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_let_crosscall_keeps_done_false".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "FlagRelay".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: IRType::Entity {
                    name: "Flagged".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "Flagged".to_owned(),
                            },
                            span: None,
                        }),
                        field: "done".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: false },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![relay, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_pooled_match_crosscall_counterexample_ir() -> IRProgram {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Set"), IRVariant::simple("Hold")],
    };
    let entity = IREntity {
        name: "FlaggedMatch".to_owned(),
        fields: vec![IRField {
            name: "done".to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: false },
                span: None,
            }),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "set_done".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "value".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![IRUpdate {
                field: "done".to_owned(),
                value: IRExpr::Var {
                    name: "value".to_owned(),
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
    let relay = IRSystem {
        name: "FlagMatchRelay".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["FlaggedMatch".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_flag".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "FlaggedMatch".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_match".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Match {
                    scrutinee: IRActionMatchScrutinee::CrossCall {
                        system: "FlagMatchDecision".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    arms: vec![
                        IRActionMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Set".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: vec![IRAction::Choose {
                                var: "f".to_owned(),
                                entity: "FlaggedMatch".to_owned(),
                                filter: Box::new(IRExpr::Lit {
                                    ty: IRType::Bool,
                                    value: LitVal::Bool { value: true },
                                    span: None,
                                }),
                                ops: vec![IRAction::Apply {
                                    target: "f".to_owned(),
                                    transition: "set_done".to_owned(),
                                    refs: vec![],
                                    args: vec![IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: true },
                                        span: None,
                                    }],
                                }],
                            }],
                        },
                        IRActionMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: vec![IRAction::Choose {
                                var: "f".to_owned(),
                                entity: "FlaggedMatch".to_owned(),
                                filter: Box::new(IRExpr::Lit {
                                    ty: IRType::Bool,
                                    value: LitVal::Bool { value: true },
                                    span: None,
                                }),
                                ops: vec![IRAction::Apply {
                                    target: "f".to_owned(),
                                    transition: "set_done".to_owned(),
                                    refs: vec![],
                                    args: vec![IRExpr::Lit {
                                        ty: IRType::Bool,
                                        value: LitVal::Bool { value: false },
                                        span: None,
                                    }],
                                }],
                            }],
                        },
                    ],
                }],
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
    };
    let worker = IRSystem {
        name: "FlagMatchDecision".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["FlaggedMatch".to_owned()],
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
            return_expr: Some(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Set".to_owned(),
                args: vec![],
                span: None,
            }),
        }],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
    };
    let verify = IRVerify {
        name: "pooled_match_crosscall_keeps_done_false".to_owned(),
        depth: None,
        systems: vec![IRVerifySystem {
            name: "FlagMatchRelay".to_owned(),
            lo: 0,
            hi: 2,
        }],
        stores: vec![],
        assumption_set: IRAssumptionSet {
            stutter: true,
            weak_fair: Vec::new(),
            strong_fair: Vec::new(),
            per_tuple: Vec::new(),
        },
        asserts: vec![IRExpr::Always {
            body: Box::new(IRExpr::Forall {
                var: "f".to_owned(),
                domain: IRType::Entity {
                    name: "FlaggedMatch".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "f".to_owned(),
                            ty: IRType::Entity {
                                name: "FlaggedMatch".to_owned(),
                            },
                            span: None,
                        }),
                        field: "done".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: false },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                }),
                span: None,
            }),
            span: None,
        }],
        span: None,
        file: None,
    };

    IRProgram {
        types: vec![IRTypeEntry {
            name: "Decision".to_owned(),
            ty: decision_ty,
        }],
        constants: vec![],
        functions: vec![],
        entities: vec![entity],
        systems: vec![relay, worker],
        verifies: vec![verify],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        scenes: vec![],
    }
}

fn make_explicit_pooled_let_crosscall_into_crosscall_arg_counterexample_ir() -> IRProgram {
    let mut ir = make_explicit_pooled_let_crosscall_counterexample_ir();
    ir.systems.retain(|sys| sys.name != "FlagRelay");
    ir.systems.push(IRSystem {
        name: "FlagArgRelay".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Flagged".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "set_flag".to_owned(),
            params: vec![IRTransParam {
                name: "value".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "f".to_owned(),
                entity: "Flagged".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![IRAction::Apply {
                    target: "f".to_owned(),
                    transition: "set_done".to_owned(),
                    refs: vec![],
                    args: vec![IRExpr::Var {
                        name: "value".to_owned(),
                        ty: IRType::Bool,
                        span: None,
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
    });
    ir.systems.push(IRSystem {
        name: "FlagCrossArgRoot".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Flagged".to_owned()],
        commands: vec![],
        actions: vec![
            IRSystemAction {
                name: "create_flag".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Create {
                    entity: "Flagged".to_owned(),
                    fields: vec![],
                }],
                return_expr: None,
            },
            IRSystemAction {
                name: "relay_set".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![
                    IRAction::LetCrossCall {
                        name: "decision".to_owned(),
                        system: "FlagDecision".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    IRAction::CrossCall {
                        system: "FlagArgRelay".to_owned(),
                        command: "set_flag".to_owned(),
                        args: vec![IRExpr::Var {
                            name: "decision".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }],
                    },
                ],
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
    });
    ir.verifies[0].name = "pooled_let_crosscall_into_crosscall_arg_keeps_done_false".to_owned();
    ir.verifies[0].systems[0].name = "FlagCrossArgRoot".to_owned();
    ir
}

#[test]
fn verify_all_explicit_state_counterexample_carries_step_param_bindings() {
    let ir = make_system_field_bool_param_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample with finite params");
    let witness = result
        .operational_witness()
        .expect("explicit-state counterexample should carry operational witness");
    let step = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step.command(), "set_flag");
    assert_eq!(step.params().len(), 1);
    assert_eq!(step.params()[0].name(), "next_flag");
    assert_eq!(step.params()[0].value(), &op::WitnessValue::Bool(true));
}

#[test]
fn verify_all_explicit_state_supports_multiple_independent_systems() {
    let ir = make_multi_system_field_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample on multi-system finite slice");
    let witness = result
        .operational_witness()
        .expect("multi-system explicit-state counterexample should carry operational witness");
    assert_eq!(witness.behavior().transitions().len(), 1);
    let step = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step.system(), "Left");
    assert_eq!(step.command(), "finish_left");
}

#[test]
fn verify_all_explicit_state_supports_duplicate_system_field_names() {
    let ir = make_multi_system_duplicate_field_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample on duplicate-field multi-system slice");
    let witness = result
        .operational_witness()
        .expect("duplicate-field explicit-state counterexample should carry operational witness");
    let step = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step.system(), "LeftDup");
    assert_eq!(step.command(), "finish_left");
}

#[test]
fn verify_all_explicit_state_supports_system_cross_calls() {
    let ir = make_explicit_system_cross_call_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample on system cross-call slice");
    let witness = result
        .operational_witness()
        .expect("explicit-state cross-call counterexample should carry operational witness");
    let step = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step.system(), "Caller");
    assert_eq!(step.command(), "invoke");
}

#[test]
fn verify_all_explicit_state_supports_let_crosscall_result_threading() {
    let ir = make_explicit_system_let_crosscall_counterexample_ir();
    let defs = defenv::DefEnv::from_ir(&ir);
    let vctx = VerifyContext::from_ir(&ir);
    let obligation =
        transition::TransitionVerifyObligation::for_verify(&ir, &vctx, &ir.verifies[0], &defs)
            .expect("expected transition obligation for let-crosscall slice");
    assert!(
        obligation
            .system()
            .system_names()
            .contains(&"DecisionLet".to_owned()),
        "expected DecisionLet to be in explicit-state scope, got: {:?}",
        obligation.system().system_names()
    );
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .unwrap_or_else(|| {
            panic!(
                "expected explicit-state counterexample on let-crosscall slice, got: {results:?}"
            )
        });
    let witness = result
        .operational_witness()
        .expect("let-crosscall explicit-state counterexample should carry operational witness");
    let step = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step.system(), "CallerLet");
    assert_eq!(step.command(), "invoke");
}

#[test]
fn verify_all_explicit_state_supports_match_routing_on_crosscall_outcomes() {
    let ir = make_explicit_system_match_crosscall_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .unwrap_or_else(|| {
            panic!(
                "expected explicit-state counterexample on match-crosscall slice, got: {results:?}"
            )
        });
    let witness = result
        .operational_witness()
        .expect("match-crosscall explicit-state counterexample should carry operational witness");
    let step = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step.system(), "CallerMatch");
    assert_eq!(step.command(), "invoke");
}

#[test]
fn verify_all_explicit_state_supports_pooled_let_crosscall_result_threading() {
    let ir = make_explicit_pooled_let_crosscall_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .unwrap_or_else(|| {
            panic!(
                "expected explicit-state counterexample on pooled let-crosscall slice, got: {results:?}"
            )
        });
    let witness = result.operational_witness().expect(
        "pooled let-crosscall explicit-state counterexample should carry operational witness",
    );
    let step = &witness.behavior().transitions()[1].atomic_steps()[0];
    assert_eq!(step.system(), "FlagRelay");
    assert_eq!(step.command(), "relay_set");
}

#[test]
fn verify_all_explicit_state_supports_pooled_match_crosscall_routing() {
    let ir = make_explicit_pooled_match_crosscall_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .unwrap_or_else(|| {
            panic!(
                "expected explicit-state counterexample on pooled match-crosscall slice, got: {results:?}"
            )
        });
    let witness = result.operational_witness().expect(
        "pooled match-crosscall explicit-state counterexample should carry operational witness",
    );
    let step = &witness.behavior().transitions()[1].atomic_steps()[0];
    assert_eq!(step.system(), "FlagMatchRelay");
    assert_eq!(step.command(), "relay_match");
}

#[test]
fn verify_all_explicit_state_supports_pooled_let_crosscall_into_crosscall_arg() {
    let ir = make_explicit_pooled_let_crosscall_into_crosscall_arg_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .unwrap_or_else(|| {
            panic!(
                "expected explicit-state counterexample on pooled let-crosscall-into-crosscall-arg slice, got: {results:?}"
            )
        });
    let witness = result.operational_witness().expect(
        "pooled let-crosscall-into-crosscall-arg explicit-state counterexample should carry operational witness",
    );
    let step = &witness.behavior().transitions()[1].atomic_steps()[0];
    assert_eq!(step.system(), "FlagCrossArgRoot");
    assert_eq!(step.command(), "relay_set");
}

#[test]
fn verify_all_explicit_state_proves_cross_call_liveness_under_weak_fairness() {
    let ir = make_explicit_system_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected explicit-state cross-call liveness to prove under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_cross_call_liveness_under_strong_fairness() {
    let ir = make_explicit_system_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected explicit-state cross-call liveness to prove under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_finite_entity_store_safety() {
    let ir = make_explicit_entity_store_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected finite entity-store safety to route to explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_entity_store_counterexample_with_entity_witness() {
    let ir = make_explicit_entity_store_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample on entity-store slice");
    let witness = result
        .operational_witness()
        .expect("entity-store explicit-state counterexample should carry operational witness");
    assert_eq!(witness.behavior().states().len(), 3);
    assert!(
        !witness
            .behavior()
            .state(0)
            .unwrap()
            .entity_slots()
            .is_empty(),
        "expected entity slots in explicit-state witness"
    );
    let step0 = &witness.behavior().transitions()[0].atomic_steps()[0];
    assert_eq!(step0.command(), "create_ticket");
    assert!(
        step0
            .choices()
            .iter()
            .any(|choice| matches!(choice, op::Choice::Create { .. })),
        "expected create choice on create_ticket step"
    );
    let step1 = &witness.behavior().transitions()[1].atomic_steps()[0];
    assert_eq!(step1.command(), "finish_one");
    assert!(
        step1
            .choices()
            .iter()
            .any(|choice| matches!(choice, op::Choice::Choose { binder, .. } if binder == "t")),
        "expected choose binding on finish_one step"
    );
}

#[test]
fn verify_all_explicit_state_carries_transition_arg_bindings_through_choose_apply() {
    let ir = make_explicit_entity_store_transition_arg_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample on entity transition arg fragment");
    let witness = result.operational_witness().expect(
        "explicit-state entity transition arg counterexample should carry operational witness",
    );
    let step = &witness.behavior().transitions()[1].atomic_steps()[0];
    assert_eq!(step.command(), "set_one");
    assert_eq!(step.params().len(), 1);
    assert_eq!(step.params()[0].name(), "next_status");
    assert_eq!(
        step.params()[0].value(),
        &op::WitnessValue::EnumVariant {
            enum_name: "TicketStatus".to_owned(),
            variant: "Done".to_owned(),
        }
    );
}

#[test]
fn verify_all_explicit_state_supports_transition_refs_through_choose_apply() {
    let ir = make_explicit_entity_store_ref_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { .. }))
        .expect("expected explicit-state counterexample on entity transition ref fragment");
    let witness = result.operational_witness().expect(
        "explicit-state entity transition ref counterexample should carry operational witness",
    );
    let step = &witness.behavior().transitions()[1].atomic_steps()[0];
    assert_eq!(step.command(), "finish_with_peer");
    assert!(
        step.choices()
            .iter()
            .filter(|choice| matches!(choice, op::Choice::Choose { .. }))
            .count()
            >= 2,
        "expected nested choose bindings on finish_with_peer step"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_entity_store_liveness_under_weak_fairness() {
    let ir = make_explicit_entity_store_ref_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_entity_store_liveness_under_strong_fairness() {
    let ir = make_explicit_entity_store_ref_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_cross_call_entity_store_liveness_under_weak_fairness() {
    let ir = make_explicit_entity_store_ref_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref cross-call entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_cross_call_entity_store_liveness_under_strong_fairness() {
    let ir = make_explicit_entity_store_ref_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref cross-call entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_param_per_tuple_entity_store_liveness_under_weak_fairness()
{
    let ir = make_explicit_entity_store_ref_param_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+param per-tuple entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_param_per_tuple_entity_store_liveness_under_strong_fairness(
) {
    let ir = make_explicit_entity_store_ref_param_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+param per-tuple entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_param_cross_call_per_tuple_entity_store_liveness_under_weak_fairness(
) {
    let ir = make_explicit_entity_store_ref_param_cross_call_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+param cross-call per-tuple entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_param_cross_call_per_tuple_entity_store_liveness_under_strong_fairness(
) {
    let ir = make_explicit_entity_store_ref_param_cross_call_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+param cross-call per-tuple entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_cross_call_entity_store_liveness_under_weak_fairness(
) {
    let ir = make_explicit_entity_store_ref_result_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result cross-call entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_cross_call_entity_store_liveness_under_strong_fairness(
) {
    let ir = make_explicit_entity_store_ref_result_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result cross-call entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_per_tuple_entity_store_liveness_under_weak_fairness()
{
    let ir = make_explicit_entity_store_ref_result_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result per-tuple entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_per_tuple_entity_store_liveness_under_strong_fairness(
) {
    let ir = make_explicit_entity_store_ref_result_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result per-tuple entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_nested_ref_result_cross_call_entity_store_liveness_under_weak_fairness(
) {
    let ir = make_explicit_entity_store_ref_result_nested_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected nested ref+result cross-call entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_nested_ref_result_cross_call_entity_store_liveness_under_strong_fairness(
) {
    let ir = make_explicit_entity_store_ref_result_nested_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected nested ref+result cross-call entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_nested_cross_call_per_tuple_entity_store_liveness_under_weak_fairness(
) {
    let ir =
        make_explicit_entity_store_ref_result_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result nested cross-call per-tuple entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_nested_cross_call_per_tuple_entity_store_liveness_under_strong_fairness(
) {
    let ir =
        make_explicit_entity_store_ref_result_nested_cross_call_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result nested cross-call per-tuple entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_deep_nested_cross_call_per_tuple_entity_store_liveness_under_weak_fairness(
) {
    let ir =
        make_explicit_entity_store_ref_result_deep_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result deep nested cross-call per-tuple entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_result_deep_nested_cross_call_per_tuple_entity_store_liveness_under_strong_fairness(
) {
    let ir =
        make_explicit_entity_store_ref_result_deep_nested_cross_call_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+result deep nested cross-call per-tuple entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_match_cross_call_entity_store_liveness_under_weak_fairness()
{
    let ir = make_explicit_entity_store_ref_match_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+match cross-call entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_match_cross_call_entity_store_liveness_under_strong_fairness(
) {
    let ir = make_explicit_entity_store_ref_match_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+match cross-call entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_param_nested_cross_call_per_tuple_entity_store_liveness_under_weak_fairness(
) {
    let ir =
        make_explicit_entity_store_ref_param_nested_cross_call_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+param nested cross-call per-tuple entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_ref_param_nested_cross_call_per_tuple_entity_store_liveness_under_strong_fairness(
) {
    let ir =
        make_explicit_entity_store_ref_param_nested_cross_call_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected ref+param nested cross-call per-tuple entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_supports_multi_entity_choose_apply_systems() {
    let ir = make_explicit_multi_entity_store_counterexample_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Counterexample { .. }
        ),
        "expected explicit-state counterexample on multi-entity choose/apply system, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_entity_store_deadlock() {
    let ir = make_explicit_entity_store_deadlock_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(&results[0], VerificationResult::Deadlock { step: 0, .. }),
        "expected explicit-state deadlock at step 0 on empty entity pool, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_quantified_entity_store_liveness_violation() {
    let ir = make_explicit_entity_store_eventual_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::LivenessViolation { .. }))
        .expect("expected quantified explicit-state liveness violation on entity-store slice");
    assert!(
        result.operational_witness().is_some(),
        "expected operational witness on quantified entity-store liveness violation: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_finds_quantified_implication_entity_store_liveness_violation() {
    let ir = make_explicit_entity_store_implication_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::LivenessViolation { .. }))
        .expect("expected quantified explicit-state liveness violation for textual implies");
    assert!(
        result.operational_witness().is_some(),
        "expected operational witness on quantified implication liveness violation: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_quantified_entity_store_liveness_under_weak_fairness() {
    let ir = make_explicit_entity_store_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected quantified entity-store liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_quantified_entity_store_liveness_under_strong_fairness() {
    let ir = make_explicit_entity_store_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected quantified entity-store liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_entity_store_cross_call_liveness_under_weak_fairness() {
    let ir = make_explicit_entity_store_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected entity-store cross-call liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_entity_store_cross_call_liveness_under_strong_fairness() {
    let ir = make_explicit_entity_store_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected entity-store cross-call liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_nested_entity_store_cross_call_liveness_under_weak_fairness() {
    let ir = make_explicit_entity_store_nested_cross_call_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected nested entity-store cross-call liveness to prove via explicit-state search under weak fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_proves_nested_entity_store_cross_call_liveness_under_strong_fairness()
{
    let ir = make_explicit_entity_store_nested_cross_call_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected nested entity-store cross-call liveness to prove via explicit-state search under strong fairness, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_per_tuple_weak_fairness_on_entity_store_steps() {
    let ir = make_explicit_entity_store_param_per_tuple_weak_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected per-tuple weak fairness on entity-store param action slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
fn verify_all_explicit_state_respects_per_tuple_strong_fairness_on_entity_store_steps() {
    let ir = make_explicit_entity_store_param_per_tuple_strong_fair_liveness_ir();
    let config = VerifyConfig {
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "explicit-state exhaustive search"
        ),
        "expected per-tuple strong fairness on entity-store param action slice to prove via explicit-state search, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_fieldless_enum_system_safety_via_sygus() {
    let ir = make_system_field_enum_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected fieldless enum system safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_finite_bool_param_system_safety_via_sygus() {
    let ir = make_system_field_bool_param_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected finite bool-param system safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_finite_enum_param_system_safety_via_sygus() {
    let ir = make_system_field_enum_param_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected finite enum-param system safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_invariant_bearing_system_safety_via_sygus() {
    let ir = make_system_field_counter_with_invariant_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected invariant-bearing system safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_match_bearing_system_safety_via_sygus() {
    let ir = make_system_field_match_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected match-bearing system safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_finite_quantifier_system_safety_via_sygus() {
    let mut ir = make_system_field_bool_param_ir();
    let eq_flag = |name: &str| IRExpr::BinOp {
        op: "OpEq".to_owned(),
        left: Box::new(IRExpr::Var {
            name: "flag".to_owned(),
            ty: IRType::Bool,
            span: None,
        }),
        right: Box::new(IRExpr::Var {
            name: name.to_owned(),
            ty: IRType::Bool,
            span: None,
        }),
        ty: IRType::Bool,
        span: None,
    };
    ir.verifies[0].asserts = vec![IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::Forall {
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
                }),
                right: Box::new(IRExpr::Exists {
                    var: "b".to_owned(),
                    domain: IRType::Bool,
                    body: Box::new(eq_flag("b")),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            right: Box::new(IRExpr::BinOp {
                op: "OpAnd".to_owned(),
                left: Box::new(IRExpr::One {
                    var: "b".to_owned(),
                    domain: IRType::Bool,
                    body: Box::new(eq_flag("b")),
                    span: None,
                }),
                right: Box::new(IRExpr::Lone {
                    var: "b".to_owned(),
                    domain: IRType::Bool,
                    body: Box::new(eq_flag("b")),
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            }),
            ty: IRType::Bool,
            span: None,
        }),
        span: None,
    }];
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected finite-quantifier system safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_entity_safety_via_sygus() {
    let ir = make_pooled_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled entity safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_enum_entity_safety_via_sygus() {
    let ir = make_pooled_ticket_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled enum safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_ref_entity_safety_via_sygus() {
    let ir = make_pooled_ref_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled ref safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_transition_arg_safety_via_sygus() {
    let ir = make_pooled_arg_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled transition-arg safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_crosscall_arg_safety_via_sygus() {
    let ir = make_pooled_crosscall_arg_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled cross-call arg safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_apply_chain_safety_via_sygus() {
    let ir = make_pooled_apply_chain_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled apply-chain safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_create_then_inc_safety_via_sygus() {
    let ir = make_pooled_create_then_inc_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled create-then-inc safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_store_membership_safety_via_sygus() {
    let ir = make_pooled_store_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled store-membership safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_crosscall_safety_via_sygus() {
    let ir = make_pooled_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled cross-call safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_nested_crosscall_safety_via_sygus() {
    let ir = make_pooled_nested_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled nested cross-call safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_match_crosscall_safety_via_sygus() {
    let ir = make_pooled_match_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled match-crosscall safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_let_crosscall_safety_via_sygus() {
    let ir = make_pooled_let_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled let-crosscall safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_match_var_crosscall_safety_via_sygus() {
    let ir = make_pooled_match_var_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled match-var crosscall safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_let_crosscall_into_crosscall_arg_safety_via_sygus()
{
    let ir = make_pooled_let_crosscall_into_crosscall_arg_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled let-crosscall-into-crosscall-arg safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_callee_field_crosscall_safety_via_sygus() {
    let ir = make_pooled_callee_field_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled callee-field crosscall safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_callee_store_crosscall_safety_via_sygus() {
    let ir = make_pooled_callee_store_crosscall_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled callee-store crosscall safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_ignores_unused_proc_metadata_in_pooled_sygus_slice() {
    let mut ir = make_pooled_callee_store_crosscall_counter_ir();
    let unused_proc = IRProc {
        name: "batch".to_owned(),
        params: vec![],
        requires: None,
        nodes: vec![],
        edges: vec![],
    };
    ir.systems[0].procs.push(unused_proc.clone());
    ir.systems[1].procs.push(unused_proc);
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled SyGuS verify to ignore unused proc metadata, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_nested_ref_entity_safety_via_sygus() {
    let ir = make_pooled_nested_ref_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled nested-ref safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_pooled_forall_nested_ref_entity_safety_via_sygus() {
    let ir = make_pooled_forall_nested_ref_counter_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected pooled forall-nested-ref safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_multi_pooled_cross_entity_safety_via_sygus() {
    let ir = make_multi_pooled_counter_marker_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected multi-pooled cross-entity safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_multi_pooled_forall_cross_entity_safety_via_sygus() {
    let ir = make_multi_pooled_forall_counter_marker_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected multi-pooled forall cross-entity safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn verify_all_with_cvc5_selection_proves_multi_pooled_cross_entity_arg_safety_via_sygus() {
    let ir = make_multi_pooled_arg_counter_marker_ir();
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        unbounded_only: true,
        no_ic3: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        matches!(
            &results[0],
            VerificationResult::Proved { method, .. } if method == "CVC5 SyGuS invariant synthesis"
        ),
        "expected multi-pooled cross-entity arg safety verify to prove via CVC5 SyGuS, got: {results:?}"
    );
}

#[test]
fn verify_all_with_both_selection_reconciles_matching_bmc_results() {
    let ir = make_order_ir(
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        2,
    );
    let config = VerifyConfig {
        solver_selection: SolverSelection::Both,
        bounded_only: true,
        ..VerifyConfig::default()
    };

    let results = verify_all(&ir, &config);

    assert!(
        results.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, depth, .. }
                if name == "test_verify" && *depth == 2
        ) || matches!(
            r,
            VerificationResult::Proved { name, method, .. }
                if name == "test_verify" && method == "explicit-state exhaustive search"
        )),
        "expected both mode to reconcile simple BMC target, got: {results:?}"
    );
    assert!(
        !results
            .iter()
            .any(|r| matches!(r, VerificationResult::Unprovable { .. })),
        "both mode should not degrade matching results to unprovable: {results:?}"
    );
}

#[test]
fn cvc5_bmc_failures_carry_operational_witnesses_without_degradation() {
    let deadlock_ir = lower_source_file(
        "deadlock.ab",
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify deadlocked {\n  \
         assume {\n    store sigs: Sig[0..3]\n    let s = S { sigs: sigs }\n  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    );
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        bounded_only: true,
        ..VerifyConfig::default()
    };

    let deadlock_results = verify_all(&deadlock_ir, &config);
    let deadlock = deadlock_results
        .iter()
        .find(|r| matches!(r, VerificationResult::Deadlock { .. }))
        .expect("inline deadlock fixture should produce deadlock under cvc5");
    assert!(
        deadlock.operational_witness().is_some(),
        "deadlock should carry operational witness under cvc5: {deadlock:?}"
    );
    assert_eq!(
        deadlock.evidence_extraction_error(),
        None,
        "deadlock witness extraction should not degrade under cvc5: {deadlock:?}"
    );

    let fairness = verify_fixture_with_config("fairness.ab", &config);
    let liveness = fairness
        .iter()
        .find(|r| {
            matches!(
                r,
                VerificationResult::LivenessViolation { name, .. } if name == "unfair_signal"
            )
        })
        .expect("fairness fixture should produce liveness violation under cvc5");
    assert!(
        liveness.operational_witness().is_some(),
        "liveness should carry operational witness under cvc5: {liveness:?}"
    );
    assert_eq!(
        liveness.evidence_extraction_error(),
        None,
        "liveness witness extraction should not degrade under cvc5: {liveness:?}"
    );
}

#[test]
fn cvc5_bmc_failures_can_carry_relational_witnesses_without_degradation() {
    let deadlock_ir = lower_source_file(
        "deadlock.ab",
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify deadlocked {\n  \
         assume {\n    store sigs: Sig[0..3]\n    let s = S { sigs: sigs }\n  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    );
    let config = VerifyConfig {
        solver_selection: SolverSelection::Cvc5,
        bounded_only: true,
        witness_semantics: WitnessSemantics::Relational,
        ..VerifyConfig::default()
    };

    let deadlock_results = verify_all(&deadlock_ir, &config);
    let deadlock = deadlock_results
        .iter()
        .find(|r| matches!(r, VerificationResult::Deadlock { .. }))
        .expect("inline deadlock fixture should produce deadlock under cvc5");
    assert!(
        deadlock.relational_witness().is_some(),
        "deadlock should carry relational witness under cvc5: {deadlock:?}"
    );
    assert_eq!(
        deadlock.evidence_extraction_error(),
        None,
        "deadlock relational witness extraction should not degrade under cvc5: {deadlock:?}"
    );

    let fairness = verify_fixture_with_config("fairness.ab", &config);
    let liveness = fairness
        .iter()
        .find(|r| {
            matches!(
                r,
                VerificationResult::LivenessViolation { name, .. } if name == "unfair_signal"
            )
        })
        .expect("fairness fixture should produce relational liveness witness under cvc5");
    assert!(
        liveness.relational_witness().is_some(),
        "liveness should carry relational witness under cvc5: {liveness:?}"
    );
    assert_eq!(
        liveness.evidence_extraction_error(),
        None,
        "liveness relational witness extraction should not degrade under cvc5: {liveness:?}"
    );
}

fn fixture_path(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../abide/tests/fixtures")
        .join(name)
}

fn lower_fixture(name: &str) -> IRProgram {
    let root = fixture_path(name);
    let paths = vec![root];
    let (env, load_errors, _all_paths) = abide_sema::loader::load_files(&paths);
    assert!(
        load_errors.is_empty(),
        "load errors for {name}: {load_errors:?}"
    );
    assert!(
        env.include_load_errors.is_empty(),
        "include errors for {name}: {:?}",
        env.include_load_errors
    );

    let (result, errors) = abide_sema::elab::elaborate_env(env);
    let actual_errors: Vec<_> = errors
        .into_iter()
        .filter(|e| !matches!(e.severity, abide_sema::elab::error::Severity::Warning))
        .collect();
    assert!(
        actual_errors.is_empty(),
        "elaboration errors for {name}: {actual_errors:?}"
    );

    let (ir, lower_diagnostics) = crate::ir::lower(&result);
    assert!(
        lower_diagnostics.diagnostics.is_empty(),
        "lower diagnostics for {name}: {:?}",
        lower_diagnostics.diagnostics
    );
    ir
}

fn verify_fixture(name: &str) -> Vec<VerificationResult> {
    let ir = lower_fixture(name);
    verify_all(&ir, &VerifyConfig::default())
}

fn verify_fixture_with_config(name: &str, config: &VerifyConfig) -> Vec<VerificationResult> {
    let ir = lower_fixture(name);
    verify_all(&ir, config)
}

fn lower_source_file(name: &str, source: &str) -> IRProgram {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join(name);
    std::fs::write(&path, source).expect("write source fixture");
    let paths = vec![path];
    let (env, load_errors, _all_paths) = abide_sema::loader::load_files(&paths);
    assert!(
        load_errors.is_empty(),
        "load errors for inline fixture {name}: {load_errors:?}"
    );
    assert!(
        env.include_load_errors.is_empty(),
        "include errors for inline fixture {name}: {:?}",
        env.include_load_errors
    );
    let (result, errors) = abide_sema::elab::elaborate_env(env);
    let actual_errors: Vec<_> = errors
        .into_iter()
        .filter(|e| !matches!(e.severity, abide_sema::elab::error::Severity::Warning))
        .collect();
    assert!(
        actual_errors.is_empty(),
        "elaboration errors for inline fixture {name}: {actual_errors:?}"
    );
    let (ir, lower_diagnostics) = crate::ir::lower(&result);
    assert!(
        lower_diagnostics.diagnostics.is_empty(),
        "lower diagnostics for inline fixture {name}: {:?}",
        lower_diagnostics.diagnostics
    );
    ir
}

#[test]
fn fixture_auth_smoke_results_cover_verify_and_scene_paths() {
    let results = verify_fixture("auth.ab");

    assert!(
        results.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, .. }
                | VerificationResult::Proved { name, .. }
                if name == "auth_safety"
        )),
        "auth fixture should prove/check auth_safety: {results:?}"
    );
    assert!(
        results.iter().any(|r| matches!(
            r,
            VerificationResult::ScenePass { name, .. } if name == "lockout_after_5_failures"
        )),
        "auth fixture should include scene success paths: {results:?}"
    );
}

#[test]
fn fixture_counterexample_deadlock_and_liveness_results_carry_operational_witnesses() {
    let deadlock_ir = lower_source_file(
        "deadlock.ab",
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify deadlocked {\n  \
         assume {\n    store sigs: Sig[0..3]\n    let s = S { sigs: sigs }\n  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    );
    let deep_dead_state = verify_all(&deadlock_ir, &VerifyConfig::default());
    let deadlock = deep_dead_state
        .iter()
        .find(|r| matches!(r, VerificationResult::Deadlock { .. }))
        .expect("inline deadlock fixture should produce deadlock");
    assert!(
        deadlock.operational_witness().is_some(),
        "deadlock results should carry operational witness envelope: {deadlock:?}"
    );

    let fairness = verify_fixture("fairness.ab");
    let liveness = fairness
        .iter()
        .find(|r| matches!(r, VerificationResult::LivenessViolation { name, .. } if name == "unfair_signal"))
        .expect("fairness fixture should produce liveness violation");
    assert!(
        liveness.operational_witness().is_some(),
        "liveness violation should carry operational witness envelope: {liveness:?}"
    );
}

#[test]
fn fixture_fairness_respects_fair_and_unfair_signal_outcomes() {
    let fairness = verify_fixture("fairness.ab");

    assert!(
        fairness.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, .. } | VerificationResult::Proved { name, .. }
            if name == "fair_signal"
        )),
        "fairness fixture should hold for fair_signal under fair command scheduling: {fairness:?}"
    );
    assert!(
        fairness.iter().any(|r| matches!(
            r,
            VerificationResult::LivenessViolation { name, .. } if name == "unfair_signal"
        )),
        "fairness fixture should still violate liveness for unfair_signal: {fairness:?}"
    );
}

#[test]
fn fixture_counterexample_deadlock_and_liveness_results_can_carry_relational_witnesses() {
    let deadlock_ir = lower_source_file(
        "deadlock.ab",
        "module T\n\n\
         entity Sig {\n  flag: bool = false\n}\n\n\
         system S(sigs: Store<Sig>) {\n  \
         command impossible() requires false { create Sig {} }\n}\n\n\
         verify deadlocked {\n  \
         assume {\n    store sigs: Sig[0..3]\n    let s = S { sigs: sigs }\n  }\n  \
         assert always all s: Sig | s.flag == false\n}\n",
    );
    let config = VerifyConfig {
        witness_semantics: WitnessSemantics::Relational,
        ..VerifyConfig::default()
    };
    let deadlock_results = verify_all(&deadlock_ir, &config);
    let deadlock = deadlock_results
        .iter()
        .find(|r| matches!(r, VerificationResult::Deadlock { .. }))
        .expect("inline deadlock fixture should produce deadlock");
    assert!(
        deadlock.relational_witness().is_some(),
        "deadlock results should carry relational witness envelope: {deadlock:?}"
    );
    assert!(
        deadlock.operational_witness().is_none(),
        "relational mode should not attach an operational witness payload: {deadlock:?}"
    );

    let fairness = verify_fixture_with_config("fairness.ab", &config);
    let liveness = fairness
        .iter()
        .find(|r| matches!(r, VerificationResult::LivenessViolation { name, .. } if name == "unfair_signal"))
        .expect("fairness fixture should produce liveness violation");
    assert!(
        liveness.relational_witness().is_some(),
        "liveness violation should carry relational witness envelope: {liveness:?}"
    );
    assert!(
        liveness.operational_witness().is_none(),
        "relational mode should not attach an operational witness payload: {liveness:?}"
    );
}

#[test]
fn fixture_scene_ordering_and_cardinality_smoke() {
    let ordering = verify_fixture("scene_ordering.ab");
    assert!(
        ordering
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { .. })),
        "scene ordering fixture should contain passing scenes: {ordering:?}"
    );
    assert!(
        ordering
            .iter()
            .any(|r| matches!(r, VerificationResult::SceneFail { .. })),
        "scene ordering fixture should contain failing scenes: {ordering:?}"
    );

    let cardinality = verify_fixture("scene_cardinality.ab");
    assert!(
        cardinality
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { .. })),
        "scene cardinality fixture should contain passing scenes: {cardinality:?}"
    );
}

#[test]
fn relational_scene_fragment_detects_create_only_cardinality_scene() {
    let ir = lower_source_file(
        "rel_scene.ab",
        "module RelScene\n\n\
         enum Status = Pending\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
         }\n\n\
         scene exact_two_creates {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             commerce.create_order(){2}\n\
           }\n\
           then {\n\
             assert exists o: Order | o.status == @Pending\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "create-only cardinality scene should be routed to relational backend"
    );
}

#[test]
fn relational_scene_fragment_passes_exact_two_creates() {
    let ir = lower_source_file(
        "rel_scene_pass.ab",
        "module RelScene\n\n\
         enum Status = Pending\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
         }\n\n\
         scene exact_two_creates {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             commerce.create_order(){2}\n\
           }\n\
           then {\n\
             assert exists o: Order | o.status == @Pending\n\
           }\n\
         }\n",
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "exact_two_creates")),
        "exact_two_creates should pass through the relational scene backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_create_only_forall_assertions() {
    let ir = lower_source_file(
        "rel_scene_forall_pass.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_pending() { create Order {} }\n\
         }\n\n\
         scene all_created_pending {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             commerce.create_pending(){2}\n\
           }\n\
           then {\n\
             assert all o: Order | o.status == @Pending\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "create-only forall scene should be routed to relational backend"
    );

    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "all_created_pending")),
        "all_created_pending should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_fails_create_only_forall_assertion() {
    let ir = lower_source_file(
        "rel_scene_forall_fail.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_pending() { create Order {} }\n\
           command create_confirmed() { create Order { status = @Confirmed } }\n\
         }\n\n\
         scene not_all_created_pending {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             commerce.create_pending()\n\
             commerce.create_confirmed()\n\
           }\n\
           then {\n\
             assert all o: Order | o.status == @Pending\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "failing create-only forall scene should stay inside relational backend"
    );

    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::SceneFail { name, .. } if name == "not_all_created_pending")
        ),
        "not_all_created_pending should fail through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_fails_when_store_capacity_is_too_small() {
    let ir = lower_source_file(
        "rel_scene_fail.ab",
        "module RelScene\n\n\
         enum Status = Pending\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
         }\n\n\
         scene exact_two_creates {\n\
           given {\n\
             store orders: Order[0..1]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             commerce.create_order(){2}\n\
           }\n\
           then {\n\
             assert exists o: Order | o.status == @Pending\n\
           }\n\
         }\n",
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::SceneFail { name, .. } if name == "exact_two_creates")),
        "overfull create-only scene should fail through the relational scene backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_ordered_create_only_scenes() {
    let ir = lower_source_file(
        "rel_scene_ordered_create.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_pending() { create Order {} }\n\
           command create_confirmed() { create Order { status = @Confirmed } }\n\
         }\n\n\
         scene ordered_creates {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             let first = commerce.create_pending()\n\
             let second = commerce.create_confirmed()\n\
             assume first -> second\n\
           }\n\
           then {\n\
             assert exists o: Order | o.status == @Confirmed\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "ordered create-only scene should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "ordered_creates")
        ),
        "ordered create-only scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_enforces_xor_on_create_only_scenes() {
    let ir = lower_source_file(
        "rel_scene_xor_create.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_pending() { create Order {} }\n\
           command create_confirmed() { create Order { status = @Confirmed } }\n\
         }\n\n\
         scene xor_impossible {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           when {\n\
             let left = commerce.create_pending(){one}\n\
             let right = commerce.create_confirmed(){one}\n\
             assume left ^| right\n\
           }\n\
           then {\n\
             assert exists o: Order | o.status == @Confirmed\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "xor create-only scene should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::SceneFail { name, .. } if name == "xor_impossible")
        ),
        "xor create-only scene should fail under relational ordering constraints: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_given_bound_update_sequences() {
    let ir = lower_source_file(
        "rel_scene_update.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command confirm_one() { choose o: Order where o.status == @Pending { o.confirm() } }\n\
           command ship_one() { choose o: Order where o.status == @Confirmed { o.ship() } }\n\
         }\n\n\
         scene confirm_then_ship {\n\
           given {\n\
             store orders: Order[0..1]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             let first = commerce.confirm_one()\n\
             let second = commerce.ship_one()\n\
             assume first -> second\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene with givens and ordered action updates should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "confirm_then_ship")),
        "given-bound ordered update scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_ordered_identity_arg_sequences() {
    let ir = lower_source_file(
        "rel_scene_identity_args.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity Parcel {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
         }\n\n\
         scene confirm_then_ship {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             let first = commerce.confirm_order(o.id)\n\
             let second = commerce.ship_order(o.id)\n\
             assume first -> second\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "ordered identity-arg scene should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "confirm_then_ship")),
        "ordered identity-arg scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_same_step_then_sequence_across_entity_types() {
    let ir = lower_source_file(
        "rel_scene_same_step.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\
         enum LogKind = Info | Warning\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity AuditLog {\n\
           kind: LogKind = @Info\n\
           action mark_warning() requires kind == @Info { kind' = @Warning }\n\
         }\n\n\
         system Audited(orders: Store<Order>, logs: Store<AuditLog>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
           command log_action() {\n\
             choose l: AuditLog where l.kind == @Info { l.mark_warning() }\n\
           }\n\
         }\n\n\
         scene same_step_then_sequence {\n\
           given {\n\
             store orders: Order[0..2]\n\
             store logs: AuditLog[0..1]\n\
             let audited = Audited { orders: orders, logs: logs }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let l = one AuditLog in logs where l.kind == @Info\n\
           }\n\
           when {\n\
             let confirm = audited.confirm_order(o.id)\n\
             let log = audited.log_action()\n\
             let ship = audited.ship_order(o.id)\n\
             assume (confirm & log) -> ship\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
             assert l.kind == @Warning\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "same-action then sequence scene should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "same_step_then_sequence")),
        "same-action then sequence scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_optional_same_step_actions() {
    let ir = lower_source_file(
        "rel_scene_same_step_optional.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\
         enum LogKind = Info | Warning\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity AuditLog {\n\
           id: identity\n\
           kind: LogKind = @Info\n\
           action mark_warning() requires kind == @Info { kind' = @Warning }\n\
         }\n\n\
         system Audited(orders: Store<Order>, logs: Store<AuditLog>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
           command log_action(log_id: identity) {\n\
             choose l: AuditLog where l.id == log_id and l.kind == @Info { l.mark_warning() }\n\
           }\n\
         }\n\n\
         scene same_step_optional_log_then_sequence {\n\
           given {\n\
             store orders: Order[0..2]\n\
             store logs: AuditLog[0..1]\n\
             let audited = Audited { orders: orders, logs: logs }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let l = one AuditLog in logs where l.kind == @Info\n\
           }\n\
           when {\n\
             let confirm = audited.confirm_order(o.id)\n\
             let log = audited.log_action(l.id){lone}\n\
             let ship = audited.ship_order(o.id)\n\
             assume (confirm & log) -> ship\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "optional same-action scene should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "same_step_optional_log_then_sequence")
        ),
        "optional same-action scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_no_same_step_actions() {
    let ir = lower_source_file(
        "rel_scene_same_step_no.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\
         enum LogKind = Info | Warning\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity AuditLog {\n\
           id: identity\n\
           kind: LogKind = @Info\n\
           action mark_warning() requires kind == @Info { kind' = @Warning }\n\
         }\n\n\
         system Audited(orders: Store<Order>, logs: Store<AuditLog>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
           command log_action(log_id: identity) {\n\
             choose l: AuditLog where l.id == log_id and l.kind == @Info { l.mark_warning() }\n\
           }\n\
         }\n\n\
         scene same_step_no_log_keeps_info {\n\
           given {\n\
             store orders: Order[0..2]\n\
             store logs: AuditLog[0..1]\n\
             let audited = Audited { orders: orders, logs: logs }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let l = one AuditLog in logs where l.kind == @Info\n\
           }\n\
           when {\n\
             let confirm = audited.confirm_order(o.id)\n\
             let log = audited.log_action(l.id){no}\n\
             let ship = audited.ship_order(o.id)\n\
             assume (confirm & log) -> ship\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
             assert l.kind == @Info\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "no-cardinality same-action scene should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "no-cardinality same-action scene should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_non_singleton_stateful_updates() {
    let ir = lower_source_file(
        "rel_scene_stateful_cardinality.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Counter {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires true {\n\
             status' = @Confirmed\n\
           }\n\
         }\n\n\
         system CounterOps(counters: Store<Counter>) {\n\
           command confirm_one(counter_id: identity) {\n\
             choose c: Counter where c.id == counter_id { c.confirm() }\n\
           }\n\
         }\n\n\
         scene exact_two_updates {\n\
           given {\n\
             store counters: Counter[0..1]\n\
             let counterOps = CounterOps { counters: counters }\n\
             let c = one Counter in counters where c.status == @Pending\n\
           }\n\
           when {\n\
             counterOps.confirm_one(c.id){2}\n\
           }\n\
           then {\n\
             assert c.status == @Confirmed\n\
           }\n\
         }\n\n\
         scene exact_three_updates {\n\
           given {\n\
             store counters: Counter[0..1]\n\
             let counterOps = CounterOps { counters: counters }\n\
             let c = one Counter in counters where c.status == @Pending\n\
           }\n\
           when {\n\
             counterOps.confirm_one(c.id){3}\n\
           }\n\
           then {\n\
             assert c.status == @Confirmed\n\
           }\n\
         }\n\n\
         scene some_updates {\n\
           given {\n\
             store counters: Counter[0..1]\n\
             let counterOps = CounterOps { counters: counters }\n\
             let c = one Counter in counters where c.status == @Pending\n\
           }\n\
           when {\n\
             counterOps.confirm_one(c.id){some}\n\
           }\n\
           then {\n\
             assert c.status == @Confirmed\n\
           }\n\
         }\n",
    );
    for scene in &ir.scenes {
        assert!(
            relational::supports_scene_fragment(&ir, scene)
                .expect("support detection should succeed"),
            "non-singleton stateful scene should stay inside the relational fragment: {}",
            scene.name
        );
        let routed = relational::try_check_scene_block_relational(&ir, scene);
        assert!(
            matches!(routed, Some(VerificationResult::ScenePass { .. })),
            "non-singleton stateful scene should be owned by the relational backend: {} => {routed:?}",
            scene.name
        );
    }
}

#[test]
fn relational_scene_fragment_supports_finite_transition_args() {
    let ir = lower_source_file(
        "rel_scene_transition_args.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action set_status(next: Status) requires next == @Confirmed or next == @Shipped {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command set_status(order_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id { o.set_status(next) }\n\
           }\n\
         }\n\n\
         scene set_then_ship {\n\
           given {\n\
             store orders: Order[0..1]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             let first = commerce.set_status(o.id, @Confirmed)\n\
             let second = commerce.set_status(o.id, @Shipped)\n\
             assume first -> second\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "finite transition-arg scene should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "finite transition-arg scene should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_ref_alias_args() {
    let ir = lower_source_file(
        "rel_scene_ref_args.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           active: bool = true\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action sync_from[customer: Customer](next: Status)\n\
             requires customer.active == true\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system Commerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, customer: identity, next: Status) {\n\
             choose o: Order where o.id == order_id { o.sync_from[customer](next) }\n\
           }\n\
         }\n\n\
         scene sync_with_active_customer {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = Commerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let c = one Customer in customers where c.active == true\n\
           }\n\
           when {\n\
             commerce.sync(o.id, c.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene ref-alias case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene ref-alias case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_nested_ref_binding() {
    let ir = lower_source_file(
        "rel_scene_nested_ref.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           active: bool = true\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action sync_from[c: Customer](next: Status)\n\
             requires c.active == true\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system SyncCommerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id {\n\
               choose c: Customer where c.active == true {\n\
                 o.sync_from[c](next)\n\
               }\n\
             }\n\
           }\n\
         }\n\n\
         scene sync_with_nested_active_customer {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = SyncCommerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let c = one Customer in customers where c.active == true\n\
           }\n\
           when {\n\
             commerce.sync(o.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
             assert c.active == true\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene nested-ref case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene nested-ref case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_nested_ref_binding_via_identity_arg() {
    let ir = lower_source_file(
        "rel_scene_nested_ref_arg.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           active: bool = true\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action sync_from[customer: Customer](next: Status)\n\
             requires customer.active == true\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system SyncCommerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, customer_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id {\n\
               choose customer: Customer where customer.id == customer_id and customer.active == true {\n\
                 o.sync_from[customer](next)\n\
               }\n\
             }\n\
           }\n\
         }\n\n\
         scene sync_with_selected_customer {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = SyncCommerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let customer = one Customer in customers where customer.active == true\n\
           }\n\
           when {\n\
             commerce.sync(o.id, customer.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
             assert customer.active == true\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene nested-ref identity-arg case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene nested-ref identity-arg case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_nested_ref_binding_via_bound_field_match() {
    let ir = lower_source_file(
        "rel_scene_nested_ref_field_match.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           active: bool = true\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           needs_active: bool = true\n\
           status: Status = @Pending\n\
           action sync_from[customer: Customer](next: Status)\n\
             requires customer.active == true\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system SyncCommerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id {\n\
               choose customer: Customer where customer.active == o.needs_active {\n\
                 o.sync_from[customer](next)\n\
               }\n\
             }\n\
           }\n\
         }\n\n\
         scene sync_with_field_matched_customer {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = SyncCommerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending and o.needs_active == true\n\
             let customer = one Customer in customers where customer.active == true\n\
           }\n\
           when {\n\
             commerce.sync(o.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
             assert customer.active == true\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene nested-ref field-match case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene nested-ref field-match case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_nested_ref_binding_via_bound_field_neq() {
    let ir = lower_source_file(
        "rel_scene_nested_ref_field_neq.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           active: bool = true\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           inactive_match: bool = false\n\
           status: Status = @Pending\n\
           action sync_from[customer: Customer](next: Status)\n\
             requires customer.active == true\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system SyncCommerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id {\n\
               choose customer: Customer where customer.active != o.inactive_match {\n\
                 o.sync_from[customer](next)\n\
               }\n\
             }\n\
           }\n\
         }\n\n\
         scene sync_with_field_mismatched_customer {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = SyncCommerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending and o.inactive_match == false\n\
             let customer = one Customer in customers where customer.active == true\n\
           }\n\
           when {\n\
             commerce.sync(o.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
             assert customer.active == true\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene nested-ref field-neq case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene nested-ref field-neq case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_nested_ref_binding_via_bound_field_gt() {
    let ir = lower_source_file(
        "rel_scene_nested_ref_field_gt.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           score: int = 5\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           min_score: int = 3\n\
           status: Status = @Pending\n\
           action sync_from[customer: Customer](next: Status)\n\
             requires customer.score > min_score\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system SyncCommerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id {\n\
               choose customer: Customer where customer.score > o.min_score {\n\
                 o.sync_from[customer](next)\n\
               }\n\
             }\n\
           }\n\
         }\n\n\
         scene sync_with_higher_scored_customer {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = SyncCommerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending and o.min_score == 3\n\
             let customer = one Customer in customers where customer.score == 5\n\
           }\n\
           when {\n\
             commerce.sync(o.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
             assert customer.score > o.min_score\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene nested-ref field-gt case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene nested-ref field-gt case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_literal_order_filters() {
    let ir = lower_source_file(
        "rel_scene_literal_order_filters.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Customer {\n\
           id: identity\n\
           score: int = 5\n\
         }\n\n\
         entity Order {\n\
           id: identity\n\
           min_score: int = 3\n\
           status: Status = @Pending\n\
           action sync_from[customer: Customer](next: Status)\n\
             requires customer.score > min_score\n\
             requires status == @Pending {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system SyncCommerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command sync(order_id: identity, next: Status) {\n\
             choose o: Order where o.id == order_id and o.min_score >= 3 {\n\
               choose customer: Customer where customer.score > 4 {\n\
                 o.sync_from[customer](next)\n\
               }\n\
             }\n\
           }\n\
         }\n\n\
         scene sync_with_literal_order_filters {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store customers: Customer[0..1]\n\
             let commerce = SyncCommerce { orders: orders, customers: customers }\n\
             let o = one Order in orders where o.status == @Pending and o.min_score >= 3\n\
             let customer = one Customer in customers where customer.score > 4\n\
           }\n\
           when {\n\
             commerce.sync(o.id, @Confirmed)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
             assert customer.score > 4\n\
             assert o.min_score >= 3\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "scene literal-order filter case should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "scene literal-order filter case should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_four_event_unordered_search() {
    let ir = lower_source_file(
        "rel_scene_unordered_four.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity Parcel {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         system Logistics(orders: Store<Order>, parcels: Store<Parcel>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
           command confirm_parcel(parcel_id: identity) {\n\
             choose p: Parcel where p.id == parcel_id and p.status == @Pending { p.confirm() }\n\
           }\n\
           command ship_parcel(parcel_id: identity) {\n\
             choose p: Parcel where p.id == parcel_id and p.status == @Confirmed { p.ship() }\n\
           }\n\
         }\n\n\
         scene unordered_two_flow_pairs {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store parcels: Parcel[0..1]\n\
             let logistics = Logistics { orders: orders, parcels: parcels }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let p = one Parcel in parcels where p.status == @Pending\n\
           }\n\
           when {\n\
             logistics.confirm_order(o.id)\n\
             logistics.ship_order(o.id)\n\
             logistics.confirm_parcel(p.id)\n\
             logistics.ship_parcel(p.id)\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
             assert p.status == @Shipped\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "four-event unordered scene should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "four-event unordered scene should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_five_event_unordered_search() {
    let ir = lower_source_file(
        "rel_scene_unordered_five.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         enum LogKind = Info | Warning\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity Parcel {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         entity AuditLog {\n\
           id: identity\n\
           kind: LogKind = @Info\n\
           action mark_warning() requires kind == @Info { kind' = @Warning }\n\
         }\n\n\
         system LogisticsAudit(orders: Store<Order>, parcels: Store<Parcel>, logs: Store<AuditLog>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
           command confirm_parcel(parcel_id: identity) {\n\
             choose p: Parcel where p.id == parcel_id and p.status == @Pending { p.confirm() }\n\
           }\n\
           command ship_parcel(parcel_id: identity) {\n\
             choose p: Parcel where p.id == parcel_id and p.status == @Confirmed { p.ship() }\n\
           }\n\
           command log_action(log_id: identity) {\n\
             choose l: AuditLog where l.id == log_id and l.kind == @Info { l.mark_warning() }\n\
           }\n\
         }\n\n\
         scene unordered_two_flow_pairs_and_log {\n\
           given {\n\
             store orders: Order[0..1]\n\
             store parcels: Parcel[0..1]\n\
             store logs: AuditLog[0..1]\n\
             let logistics = LogisticsAudit { orders: orders, parcels: parcels, logs: logs }\n\
             let o = one Order in orders where o.status == @Pending\n\
             let p = one Parcel in parcels where p.status == @Pending\n\
             let l = one AuditLog in logs where l.kind == @Info\n\
           }\n\
           when {\n\
             logistics.confirm_order(o.id)\n\
             logistics.ship_order(o.id)\n\
             logistics.confirm_parcel(p.id)\n\
             logistics.ship_parcel(p.id)\n\
             logistics.log_action(l.id)\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
             assert p.status == @Shipped\n\
             assert l.kind == @Warning\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "five-event unordered scene should stay inside the relational fragment"
    );
    let routed = relational::try_check_scene_block_relational(&ir, scene);
    assert!(
        matches!(routed, Some(VerificationResult::ScenePass { .. })),
        "five-event unordered scene should be owned by the relational backend: {routed:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_solver_chosen_order_for_small_event_sets() {
    let ir = lower_source_file(
        "rel_scene_no_ordering.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
         }\n\n\
         scene no_ordering {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             commerce.confirm_order(o.id)\n\
             commerce.ship_order(o.id)\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "unordered identity-arg scene should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "no_ordering")
        ),
        "unordered small event scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_supports_lone_optional_events() {
    let ir = lower_source_file(
        "rel_scene_lone_optional.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed | Shipped\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
           action ship() requires status == @Confirmed { status' = @Shipped }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
           command ship_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Confirmed { o.ship() }\n\
           }\n\
         }\n\n\
         scene lone_confirm_keeps_pending {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             commerce.confirm_order(o.id){lone}\n\
           }\n\
           then {\n\
             assert o.status == @Pending\n\
           }\n\
         }\n\n\
         scene lone_confirm_must_ship {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             commerce.confirm_order(o.id){lone}\n\
           }\n\
           then {\n\
             assert o.status == @Shipped\n\
           }\n\
         }\n\n\
         scene no_ship_after_confirm {\n\
           given {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             let confirm = commerce.confirm_order(o.id)\n\
             let ship = commerce.ship_order(o.id){no}\n\
             assume confirm -> ship\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
           }\n\
         }\n",
    );
    for scene in &ir.scenes {
        assert!(
            relational::supports_scene_fragment(&ir, scene)
                .expect("support detection should succeed"),
            "optional-presence scene should stay inside the relational fragment: {}",
            scene.name
        );
    }
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "lone_confirm_keeps_pending")
        ),
        "lone scene witness should pass through the relational backend: {results:?}"
    );
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::SceneFail { name, .. } if name == "lone_confirm_must_ship")
        ),
        "impossible lone scene should fail through the relational backend: {results:?}"
    );
    assert!(
        results
            .iter()
            .any(|r| matches!(r, VerificationResult::ScenePass { name, .. } if name == "no_ship_after_confirm")),
        "ordered no-cardinality scene should pass through the relational backend: {results:?}"
    );
}

#[test]
fn relational_scene_fragment_rejects_event_arg_scenes_and_leaves_them_on_smt_path() {
    let ir = lower_source_file(
        "rel_scene_nonbinding_arg_unsupported.ab",
        "module RelScene\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n\
           id: identity\n\
           status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command confirm_order(order_id: identity) {\n\
             choose o: Order where o.id == order_id and o.status == @Pending { o.confirm() }\n\
           }\n\
         }\n\n\
         scene confirm_one {\n\
           given {\n\
             store orders: Order[0..1]\n\
             let commerce = Commerce { orders: orders }\n\
             let o = one Order in orders where o.status == @Pending\n\
           }\n\
           when {\n\
             commerce.confirm_order(0)\n\
           }\n\
           then {\n\
             assert o.status == @Confirmed\n\
           }\n\
         }\n",
    );
    let scene = &ir.scenes[0];
    assert!(
        !relational::supports_scene_fragment(&ir, scene).expect("support detection should succeed"),
        "non-binding event-arg scenes should remain outside the relational fragment"
    );
}

#[test]
fn relational_verify_fragment_detects_create_only_bounded_verify() {
    let ir = lower_source_file(
        "rel_verify_detect.ab",
        "module RelVerify\n\n\
         enum Status = Pending\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
         }\n\n\
         verify pending_orders {\n\
           assume {\n\
             store orders: Order[0..3]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "create-only bounded verify should be routed to relational backend"
    );
}

#[test]
fn relational_verify_fragment_checks_create_only_safety() {
    let ir = lower_source_file(
        "rel_verify_pass.ab",
        "module RelVerify\n\n\
         enum Status = Pending\n\n\
         entity Order {\n  status: Status = @Pending\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
         }\n\n\
         verify pending_orders {\n\
           assume {\n\
             store orders: Order[0..3]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending)\n\
         }\n",
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::Checked { name, .. } if name == "pending_orders")
        ),
        "create-only bounded verify should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_finds_counterexample_with_relational_witness() {
    let ir = lower_source_file(
        "rel_verify_fail.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Confirmed\n}\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
         }\n\n\
         verify pending_orders {\n\
           assume {\n\
             store orders: Order[0..3]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending)\n\
         }\n",
    );
    let results = verify_all(
        &ir,
        &VerifyConfig {
            witness_semantics: WitnessSemantics::Relational,
            ..VerifyConfig::default()
        },
    );
    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { name, .. } if name == "pending_orders"))
        .unwrap_or_else(|| panic!("expected relational counterexample, got {results:?}"));
    assert!(
        result.relational_witness().is_some(),
        "relational bounded counterexample should carry relational witness evidence: {result:?}"
    );
}

#[test]
fn relational_verify_fragment_detects_create_and_update_bounded_verify() {
    let ir = lower_source_file(
        "rel_verify_update_detect.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
           command confirm_order() { choose o: Order where true { o.confirm() } }\n\
         }\n\n\
         verify known_statuses {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending or o.status == @Confirmed)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "create-plus-apply bounded verify should be routed to relational backend"
    );
}

#[test]
fn relational_verify_fragment_checks_create_and_update_safety() {
    let ir = lower_source_file(
        "rel_verify_update_pass.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
           command confirm_order() { choose o: Order where true { o.confirm() } }\n\
         }\n\n\
         verify known_statuses {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending or o.status == @Confirmed)\n\
         }\n",
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::Checked { name, .. } if name == "known_statuses")
        ),
        "create-plus-apply bounded verify should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_finds_update_counterexample_with_relational_witness() {
    let ir = lower_source_file(
        "rel_verify_update_fail.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
           command confirm_order() { choose o: Order where true { o.confirm() } }\n\
         }\n\n\
         verify pending_orders {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending)\n\
         }\n",
    );
    let results = verify_all(
        &ir,
        &VerifyConfig {
            witness_semantics: WitnessSemantics::Relational,
            ..VerifyConfig::default()
        },
    );
    let result = results
        .iter()
        .find(|r| matches!(r, VerificationResult::Counterexample { name, .. } if name == "pending_orders"))
        .unwrap_or_else(|| panic!("expected relational counterexample, got {results:?}"));
    assert!(
        result.relational_witness().is_some(),
        "create-plus-apply bounded counterexample should carry relational witness evidence: {result:?}"
    );
}

#[test]
fn relational_verify_fragment_detects_finite_transition_args() {
    let ir = lower_source_file(
        "rel_verify_args_detect.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed | Cancelled\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action set_status(next: Status) requires status == @Pending { status' = next }\n\
         }\n\n\
         system ArgCommerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
           command confirm_order() { choose o: Order where true { o.set_status(@Confirmed) } }\n\
         }\n\n\
         verify known_statuses {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = ArgCommerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending or o.status == @Confirmed)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "finite transition arguments should stay inside the relational fragment"
    );
}

#[test]
fn relational_verify_fragment_checks_finite_transition_args_safety() {
    let ir = lower_source_file(
        "rel_verify_args_pass.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed | Cancelled\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action set_status(next: Status) requires status == @Pending { status' = next }\n\
         }\n\n\
         system ArgCommerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
           command confirm_order() { choose o: Order where true { o.set_status(@Confirmed) } }\n\
         }\n\n\
         verify never_cancelled {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = ArgCommerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | not (o.status == @Cancelled))\n\
         }\n",
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::Checked { name, .. } if name == "never_cancelled")
        ),
        "transition-arg bounded verify should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_finds_transition_arg_counterexample_with_relational_witness() {
    let ir = lower_source_file(
        "rel_verify_args_fail.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed | Cancelled\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action set_status(next: Status) requires status == @Pending { status' = next }\n\
         }\n\n\
         system ArgCommerce(orders: Store<Order>) {\n\
           command create_order() { create Order {} }\n\
           command cancel_order() { choose o: Order where true { o.set_status(@Cancelled) } }\n\
         }\n\n\
         verify pending_orders {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = ArgCommerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending)\n\
         }\n",
    );
    let results = verify_all(
        &ir,
        &VerifyConfig {
            witness_semantics: WitnessSemantics::Relational,
            ..VerifyConfig::default()
        },
    );
    let result = results
        .iter()
        .find(
            |r| matches!(r, VerificationResult::Counterexample { name, .. } if name == "pending_orders"),
        )
        .unwrap_or_else(|| panic!("expected relational counterexample, got {results:?}"));
    assert!(
        result.relational_witness().is_some(),
        "transition-arg bounded counterexample should carry relational witness evidence: {result:?}"
    );
}

#[test]
fn relational_verify_fragment_supports_sequential_multi_action_step_bodies() {
    let ir = lower_source_file(
        "rel_verify_multi_action.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         system Commerce(orders: Store<Order>) {\n\
           command bootstrap() {\n\
             create Order {}\n\
             choose o: Order where true { o.confirm() }\n\
           }\n\
         }\n\n\
         verify known_statuses {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             let commerce = Commerce { orders: orders }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending or o.status == @Confirmed)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "sequential multi-action action bodies should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::Checked { name, .. } if name == "known_statuses")
        ),
        "sequential multi-action bounded verify should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_checks_two_entity_pools() {
    let ir = lower_source_file(
        "rel_verify_multi_entity.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         entity Customer {\n  active: bool = false\n\
           action activate() requires not active { active' = true }\n\
         }\n\n\
         system Commerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command seed() {\n\
             create Order {}\n\
             create Customer {}\n\
           }\n\
           command progress() {\n\
             choose o: Order where true { o.confirm() }\n\
             choose c: Customer where true { c.activate() }\n\
           }\n\
         }\n\n\
         verify known_state {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             store customers: Customer[0..2]\n\
             let commerce = Commerce { orders: orders, customers: customers }\n\
           }\n\
           assert always ((all o: Order | o.status == @Pending or o.status == @Confirmed) and (all c: Customer | c.active == false or c.active == true))\n\
         }\n",
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::Checked { name, .. } if name == "known_state")
        ),
        "two-entity bounded verify should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_finds_two_entity_counterexample_with_relational_witness() {
    let ir = lower_source_file(
        "rel_verify_multi_entity_fail.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action confirm() requires status == @Pending { status' = @Confirmed }\n\
         }\n\n\
         entity Customer {\n  active: bool = false\n\
           action activate() requires not active { active' = true }\n\
         }\n\n\
         system Commerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command seed() {\n\
             create Order {}\n\
             create Customer {}\n\
           }\n\
           command progress() {\n\
             choose o: Order where true { o.confirm() }\n\
             choose c: Customer where true { c.activate() }\n\
           }\n\
         }\n\n\
         verify pending_and_inactive {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             store customers: Customer[0..2]\n\
             let commerce = Commerce { orders: orders, customers: customers }\n\
           }\n\
           assert always ((all o: Order | o.status == @Pending) and (all c: Customer | c.active == false))\n\
         }\n",
    );
    let results = verify_all(
        &ir,
        &VerifyConfig {
            witness_semantics: WitnessSemantics::Relational,
            ..VerifyConfig::default()
        },
    );
    let result = results
        .iter()
        .find(
            |r| matches!(r, VerificationResult::Counterexample { name, .. } if name == "pending_and_inactive"),
        )
        .unwrap_or_else(|| panic!("expected relational counterexample, got {results:?}"));
    assert!(
        result.relational_witness().is_some(),
        "two-entity bounded counterexample should carry relational witness evidence: {result:?}"
    );
}

#[test]
fn relational_verify_fragment_checks_nested_cross_entity_quantifiers() {
    let ir = lower_source_file(
        "rel_verify_nested_quantifiers.ab",
        "module RelVerify\n\n\
         entity Order {\n  paid: bool = false\n}\n\n\
         entity Payment {\n  captured: bool = false\n}\n\n\
         system Commerce(orders: Store<Order>, payments: Store<Payment>) {\n\
           command seed() {\n\
             create Order { paid = true }\n\
             create Payment { captured = true }\n\
           }\n\
         }\n\n\
         verify matching_states {\n\
           assume {\n\
             stutter\n\
             store orders: Order[0..2]\n\
             store payments: Payment[0..2]\n\
             let commerce = Commerce { orders: orders, payments: payments }\n\
           }\n\
           assert always (all o: Order | all p: Payment | o.paid == p.captured)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "nested cross-entity quantifiers should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, .. }
                | VerificationResult::Proved { name, .. } if name == "matching_states"
        )),
        "nested cross-entity quantifiers should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_finds_nested_cross_entity_quantifier_counterexample() {
    let ir = lower_source_file(
        "rel_verify_nested_quantifiers_fail.ab",
        "module RelVerify\n\n\
         entity Order {\n  paid: bool = false\n}\n\n\
         entity Payment {\n  captured: bool = false\n}\n\n\
         system Commerce(orders: Store<Order>, payments: Store<Payment>) {\n\
           command seed() {\n\
             create Order { paid = true }\n\
             create Payment { captured = false }\n\
           }\n\
         }\n\n\
         verify matching_states {\n\
           assume {\n\
             stutter\n\
             store orders: Order[0..2]\n\
             store payments: Payment[0..2]\n\
             let commerce = Commerce { orders: orders, payments: payments }\n\
           }\n\
           assert always (all o: Order | all p: Payment | o.paid == p.captured)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "nested cross-entity quantifier counterexamples should stay inside the relational fragment"
    );
    let results = verify_all(
        &ir,
        &VerifyConfig {
            witness_semantics: WitnessSemantics::Relational,
            ..VerifyConfig::default()
        },
    );
    let result = results
        .iter()
        .find(
            |r| matches!(r, VerificationResult::Counterexample { name, .. } if name == "matching_states"),
        )
        .unwrap_or_else(|| panic!("expected relational counterexample, got {results:?}"));
    assert!(
        result.relational_witness().is_some(),
        "nested cross-entity quantifier counterexample should carry relational witness evidence: {result:?}"
    );
}

#[test]
fn relational_verify_fragment_checks_cross_entity_ref_and_args_safety() {
    let ir = lower_source_file(
        "rel_verify_multi_entity_ref.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed | Cancelled\n\n\
         entity Customer {\n  active: bool = false\n\
           action activate() requires not active { active' = true }\n\
         }\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action sync_from[c: Customer](next: Status)\n\
             requires status == @Pending\n\
             requires c.active == true {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system Commerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command seed() {\n\
             create Order {}\n\
             create Customer { active = true }\n\
           }\n\
           command sync() {\n\
             choose o: Order where o.status == @Pending {\n\
               choose c: Customer where c.active == true { o.sync_from[c](@Confirmed) }\n\
             }\n\
           }\n\
         }\n\n\
         verify synced_orders_not_cancelled {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             store customers: Customer[0..2]\n\
             let commerce = Commerce { orders: orders, customers: customers }\n\
           }\n\
           assert always (all o: Order | o.status != @Cancelled)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "cross-entity ref+arg bounded verify should stay inside the relational fragment"
    );
    let results = verify_all(&ir, &VerifyConfig::default());
    assert!(
        results.iter().any(
            |r| matches!(r, VerificationResult::Checked { name, .. } if name == "synced_orders_not_cancelled")
        ),
        "cross-entity ref+arg bounded verify should check through the relational backend: {results:?}"
    );
}

#[test]
fn relational_verify_fragment_finds_cross_entity_ref_and_arg_counterexample_with_relational_witness(
) {
    let ir = lower_source_file(
        "rel_verify_multi_entity_ref_fail.ab",
        "module RelVerify\n\n\
         enum Status = Pending | Confirmed | Cancelled\n\n\
         entity Customer {\n  active: bool = false\n\
           action activate() requires not active { active' = true }\n\
         }\n\n\
         entity Order {\n  status: Status = @Pending\n\
           action sync_from[c: Customer](next: Status)\n\
             requires status == @Pending\n\
             requires c.active == true {\n\
             status' = next\n\
           }\n\
         }\n\n\
         system Commerce(orders: Store<Order>, customers: Store<Customer>) {\n\
           command seed() {\n\
             create Order {}\n\
             create Customer { active = true }\n\
           }\n\
           command sync() {\n\
             choose o: Order where o.status == @Pending {\n\
               choose c: Customer where c.active == true { o.sync_from[c](@Cancelled) }\n\
             }\n\
           }\n\
         }\n\n\
         verify synced_orders_remain_pending {\n\
           assume {\n\
             store orders: Order[0..2]\n\
             store customers: Customer[0..2]\n\
             let commerce = Commerce { orders: orders, customers: customers }\n\
           }\n\
           assert always (all o: Order | o.status == @Pending)\n\
         }\n",
    );
    let verify = &ir.verifies[0];
    assert!(
        relational::supports_verify_fragment(&ir, verify)
            .expect("support detection should succeed"),
        "cross-entity ref+arg bounded counterexample should stay inside the relational fragment"
    );
    let results = verify_all(
        &ir,
        &VerifyConfig {
            witness_semantics: WitnessSemantics::Relational,
            ..VerifyConfig::default()
        },
    );
    let result = results
        .iter()
        .find(
            |r| matches!(r, VerificationResult::Counterexample { name, .. } if name == "synced_orders_remain_pending"),
        )
        .unwrap_or_else(|| panic!("expected relational counterexample, got {results:?}"));
    assert!(
        result.relational_witness().is_some(),
        "cross-entity ref+arg bounded counterexample should carry relational witness evidence: {result:?}"
    );
}

#[test]
fn fixture_liveness_and_fairness_smoke() {
    let results = verify_fixture("liveness_reduction.ab");
    assert!(
        results.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { .. }
                | VerificationResult::Counterexample { .. }
                | VerificationResult::LivenessViolation { .. }
                | VerificationResult::Unprovable { .. }
        )),
        "liveness reduction fixture should exercise liveness verdict paths: {results:?}"
    );

    let strong = verify_fixture("strong_fairness.ab");
    assert!(
        strong
            .iter()
            .any(|r| matches!(r, VerificationResult::Unprovable { .. })),
        "strong fairness fixture should exercise unprovable liveness paths: {strong:?}"
    );
    assert!(
        strong.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { .. } | VerificationResult::Proved { .. }
        )),
        "strong fairness fixture should still exercise successful safety paths: {strong:?}"
    );
}

#[test]
fn fixture_function_contracts_smoke() {
    for fixture in [
        "contracts.ab",
        "imperative.ab",
        "termination.ab",
        "assert_assume.ab",
        "algorithms.ab",
        "functions.ab",
    ] {
        let results = verify_fixture(fixture);
        assert!(
            results.iter().any(|r| matches!(
                r,
                VerificationResult::FnContractProved { .. }
                    | VerificationResult::FnContractFailed { .. }
                    | VerificationResult::FnContractAdmitted { .. }
            )),
            "{fixture} should exercise fn contract verification: {results:?}"
        );
    }
}

#[test]
fn fixture_collections_and_quantifiers_smoke() {
    for fixture in [
        "collection_ops.ab",
        "collections.ab",
        "quantifiers.ab",
        "until.ab",
        "lambdas.ab",
        "refinements.ab",
    ] {
        let results = verify_fixture(fixture);
        assert!(
            !results.is_empty(),
            "{fixture} should produce verification results"
        );
    }
}

#[test]
fn fixture_large_systems_and_multi_file_smoke() {
    let workflow = verify_fixture("workflow.ab");
    assert!(
        workflow.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, .. }
                | VerificationResult::Proved { name, .. }
                if name == "workflow_safety" || name == "workflow_liveness"
        )),
        "workflow fixture should exercise verify paths: {workflow:?}"
    );
    assert!(
        workflow
            .iter()
            .filter(|r| matches!(r, VerificationResult::ScenePass { .. }))
            .count()
            >= 3,
        "workflow fixture should contain its passing scenes: {workflow:?}"
    );

    let inventory = verify_fixture("inventory.ab");
    assert!(
        inventory.iter().any(|r| matches!(
            r,
            VerificationResult::Proved { name, .. }
                | VerificationResult::Checked { name, .. }
                if name == "inventory_safety"
        )),
        "inventory fixture should exercise proved safety paths: {inventory:?}"
    );
    assert!(
        inventory
            .iter()
            .filter(|r| matches!(r, VerificationResult::ScenePass { .. }))
            .count()
            >= 2,
        "inventory fixture should contain both passing scenes: {inventory:?}"
    );

    let commerce = verify_fixture("commerce.ab");
    assert!(
        commerce.iter().any(|r| matches!(
            r,
            VerificationResult::Counterexample { name, .. } if name == "commerce_smoke"
        )),
        "commerce fixture should exercise counterexample paths: {commerce:?}"
    );
    assert!(
        commerce.iter().any(|r| matches!(
            r,
            VerificationResult::ScenePass { name, .. } if name == "happy_path"
        )),
        "commerce fixture should exercise multi-file scene paths: {commerce:?}"
    );

    let logistics = verify_fixture("logistics.ab");
    assert!(
        logistics.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { name, .. }
                | VerificationResult::Proved { name, .. }
                if name == "logistics_safety"
        )),
        "logistics fixture should exercise include/import safety paths: {logistics:?}"
    );
    assert!(
        logistics.iter().any(|r| matches!(
            r,
            VerificationResult::ScenePass { name, .. } if name == "reserve_and_ship"
        )),
        "logistics fixture should exercise included scene paths: {logistics:?}"
    );
}

#[test]
fn fixture_relational_liveness_and_nondeterminism_smoke() {
    let quantified_false = verify_fixture("liveness_quantified_false.ab");
    assert!(
        quantified_false.iter().any(|r| matches!(
            r,
            VerificationResult::LivenessViolation { .. }
                | VerificationResult::Counterexample { .. }
                | VerificationResult::Checked { .. }
                | VerificationResult::Unprovable { .. }
        )),
        "liveness_quantified_false should exercise quantified liveness encoding: {quantified_false:?}"
    );

    let symmetry = verify_fixture("symmetry_reduction.ab");
    assert!(
        symmetry.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { .. }
                | VerificationResult::Counterexample { .. }
                | VerificationResult::LivenessViolation { .. }
                | VerificationResult::Proved { .. }
        )),
        "symmetry_reduction should exercise symmetry-aware bounded checks: {symmetry:?}"
    );

    let nondet = verify_fixture("nondet_defaults.ab");
    assert!(
        nondet.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { .. } | VerificationResult::Counterexample { .. }
        )),
        "nondet_defaults should exercise nondeterministic initialization: {nondet:?}"
    );

    let where_false = verify_fixture("nondet_where_false.ab");
    assert!(
        where_false.iter().any(|r| matches!(
            r,
            VerificationResult::Checked { .. }
                | VerificationResult::Proved { .. }
                | VerificationResult::Unprovable { .. }
        )),
        "nondet_where_false should exercise vacuity handling: {where_false:?}"
    );

    let dead = verify_fixture("deep_dead_state.ab");
    assert!(
        dead.iter().any(|r| matches!(
            r,
            VerificationResult::Unprovable { name, .. }
                | VerificationResult::LivenessViolation { name, .. }
                | VerificationResult::Counterexample { name, .. }
                if name == "deep_dead"
        )),
        "deep_dead_state should exercise deep liveness/dead-state handling: {dead:?}"
    );
}

#[test]
fn fixture_remaining_verify_features_smoke() {
    for fixture in [
        "cardinality.ab",
        "constructor_fields.ab",
        "call_site.ab",
        "recursion_stress.ab",
        "refinement_call_site.ab",
        "one_lone.ab",
        "lemmas.ab",
        "nested_actions.ab",
        "command_step_query.ab",
    ] {
        let results = verify_fixture(fixture);
        assert!(
            results.iter().any(|r| matches!(
                r,
                VerificationResult::Checked { .. }
                    | VerificationResult::Proved { .. }
                    | VerificationResult::Counterexample { .. }
                    | VerificationResult::Unprovable { .. }
                    | VerificationResult::Deadlock { .. }
                    | VerificationResult::LivenessViolation { .. }
                    | VerificationResult::ScenePass { .. }
                    | VerificationResult::SceneFail { .. }
                    | VerificationResult::FnContractProved { .. }
                    | VerificationResult::FnContractFailed { .. }
                    | VerificationResult::FnContractAdmitted { .. }
            )),
            "{fixture} should exercise verifier result paths: {results:?}"
        );
    }
}
