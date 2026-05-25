use super::*;
use crate::ir::types::{IRAggKind, IRProgram, IRTransition, IRUpdate, IRVariant, LitVal};
use crate::verify::context::VerifyContext;
use crate::verify::ic3;
use crate::verify::solver::{active_solver_family, set_active_solver_family, SolverFamily};
use crate::verify::transition::{solve_transition_obligation, TransitionObligation};

#[test]
fn cvc5_sygus_disabled_reason_documents_hard_cancellation_boundary() {
    let reason = cvc5_sygus_disabled_reason();

    assert!(reason.contains("disabled by default"));
    assert!(reason.contains("hard cancellation hook"));
    assert!(reason.contains("ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1"));
}

fn make_counter_entity() -> IREntity {
    IREntity {
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
            updates: vec![crate::ir::types::IRUpdate {
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
    }
}

fn non_negative_property() -> IRExpr {
    IRExpr::Always {
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
    }
}

fn int_lit(value: i64) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Int,
        value: LitVal::Int { value },
        span: None,
    }
}

fn real_lit(value: f64) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Real,
        value: LitVal::Real { value },
        span: None,
    }
}

fn bool_lit(value: bool) -> IRExpr {
    IRExpr::Lit {
        ty: IRType::Bool,
        value: LitVal::Bool { value },
        span: None,
    }
}

fn bin_expr(op: &str, left: IRExpr, right: IRExpr, ty: IRType) -> IRExpr {
    IRExpr::BinOp {
        op: op.to_owned(),
        left: Box::new(left),
        right: Box::new(right),
        ty,
        span: None,
    }
}

fn nonnegative_derived_field() -> crate::ir::types::IRDerivedField {
    crate::ir::types::IRDerivedField {
        name: "nonnegative".to_owned(),
        body: bin_expr(
            "OpGe",
            IRExpr::Var {
                name: "x".to_owned(),
                ty: IRType::Int,
                span: None,
            },
            int_lit(0),
            IRType::Bool,
        ),
        ty: IRType::Bool,
    }
}

fn true_derived_field() -> crate::ir::types::IRDerivedField {
    crate::ir::types::IRDerivedField {
        name: "always_enabled".to_owned(),
        body: bool_lit(true),
        ty: IRType::Bool,
    }
}

fn status_ty() -> IRType {
    IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    }
}

fn status_ctor(ctor: &str) -> IRExpr {
    IRExpr::Ctor {
        enum_name: "Status".to_owned(),
        ctor: ctor.to_owned(),
        args: vec![],
        span: None,
    }
}

fn pending_to_done_fsm(field: &str) -> crate::ir::types::IRFsm {
    crate::ir::types::IRFsm {
        field: field.to_owned(),
        enum_name: "Status".to_owned(),
        transitions: vec![crate::ir::types::IRFsmTransition {
            from: "Pending".to_owned(),
            to: "Done".to_owned(),
        }],
    }
}

#[test]
fn sygus_expr_encoder_supports_integer_div_mod_and_bool_xor() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let enum_catalog = EnumCatalog::new();

    for expr in [
        bin_expr("OpDiv", int_lit(9), int_lit(3), IRType::Int),
        bin_expr("OpMod", int_lit(9), int_lit(4), IRType::Int),
        bin_expr("OpXor", bool_lit(true), bool_lit(false), IRType::Bool),
    ] {
        encode_expr(&tm, &expr, &vars, &enum_catalog)
            .unwrap_or_else(|err| panic!("finite SyGuS expression should encode: {err}"));
    }
}

#[test]
fn sygus_expr_encoder_supports_real_literals_and_arithmetic() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let enum_catalog = EnumCatalog::new();
    let expr = bin_expr("OpDiv", real_lit(3.0), real_lit(2.0), IRType::Real);

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("real literal arithmetic should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_finite_choose_expressions() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let enum_catalog = EnumCatalog::new();
    let expr = IRExpr::Choose {
        var: "b".to_owned(),
        domain: IRType::Bool,
        predicate: Some(Box::new(IRExpr::Var {
            name: "b".to_owned(),
            ty: IRType::Bool,
            span: None,
        })),
        ty: IRType::Bool,
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("finite SyGuS choose expression should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_inline_lambda_application() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let enum_catalog = EnumCatalog::new();
    let expr = IRExpr::App {
        func: Box::new(IRExpr::Lam {
            param: "b".to_owned(),
            param_type: IRType::Bool,
            body: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            span: None,
        }),
        arg: Box::new(bool_lit(true)),
        ty: IRType::Bool,
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("inline SyGuS lambda application should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_accepts_qualified_enum_constructor_names() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let mut enum_catalog = EnumCatalog::new();
    enum_catalog.insert(
        "Status".to_owned(),
        HashMap::from([("Pending".to_owned(), 0), ("Done".to_owned(), 1)]),
    );

    let expr = IRExpr::Ctor {
        enum_name: "Status".to_owned(),
        ctor: "Status::Pending".to_owned(),
        args: vec![],
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("qualified enum constructor should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_accepts_constructor_atoms_lowered_as_vars() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let mut enum_catalog = EnumCatalog::new();
    enum_catalog.insert(
        "Status".to_owned(),
        HashMap::from([("Pending".to_owned(), 0), ("Done".to_owned(), 1)]),
    );
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };

    let expr = IRExpr::Var {
        name: "Pending".to_owned(),
        ty: status_ty,
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("constructor atom lowered as Var should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_static_payload_constructor_destructuring() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::new();
    let enum_catalog = EnumCatalog::new();

    let expr = IRExpr::Match {
        scrutinee: Box::new(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Accept".to_owned(),
            args: vec![("allowed".to_owned(), bool_lit(true))],
            span: None,
        }),
        arms: vec![
            crate::ir::types::IRMatchArm {
                pattern: crate::ir::types::IRPattern::PCtor {
                    name: "Accept".to_owned(),
                    fields: vec![crate::ir::types::IRFieldPat {
                        name: "allowed".to_owned(),
                        pattern: crate::ir::types::IRPattern::PVar {
                            name: "accepted".to_owned(),
                        },
                    }],
                },
                guard: None,
                body: IRExpr::Var {
                    name: "accepted".to_owned(),
                    ty: IRType::Bool,
                    span: None,
                },
            },
            crate::ir::types::IRMatchArm {
                pattern: crate::ir::types::IRPattern::PWild,
                guard: None,
                body: bool_lit(false),
            },
        ],
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("static payload constructor match should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_dynamic_payload_constructor_destructuring() {
    let tm = Cvc5Tm::new();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let enum_catalog = EnumCatalog::from_types(&tm, std::slice::from_ref(&decision_ty))
        .expect("payload enum datatype catalog should build");
    let decision_sort = enum_catalog
        .payload_sort("Decision")
        .expect("Decision datatype sort should be available");
    let vars = HashMap::from([(
        "decision".to_owned(),
        tm.mk_var(decision_sort.clone(), "decision"),
    )]);

    let expr = IRExpr::Match {
        scrutinee: Box::new(IRExpr::Var {
            name: "decision".to_owned(),
            ty: decision_ty,
            span: None,
        }),
        arms: vec![
            crate::ir::types::IRMatchArm {
                pattern: crate::ir::types::IRPattern::PCtor {
                    name: "Accept".to_owned(),
                    fields: vec![crate::ir::types::IRFieldPat {
                        name: "amount".to_owned(),
                        pattern: crate::ir::types::IRPattern::PVar {
                            name: "payload".to_owned(),
                        },
                    }],
                },
                guard: Some(bin_expr(
                    "OpGe",
                    IRExpr::Var {
                        name: "payload".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    },
                    int_lit(0),
                    IRType::Bool,
                )),
                body: IRExpr::Var {
                    name: "payload".to_owned(),
                    ty: IRType::Int,
                    span: None,
                },
            },
            crate::ir::types::IRMatchArm {
                pattern: crate::ir::types::IRPattern::PWild,
                guard: None,
                body: int_lit(0),
            },
        ],
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("dynamic payload constructor match should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_payload_field_projection() {
    let tm = Cvc5Tm::new();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let enum_catalog = EnumCatalog::from_types(&tm, std::slice::from_ref(&decision_ty))
        .expect("payload enum datatype catalog should build");
    let decision_sort = enum_catalog
        .payload_sort("Decision")
        .expect("Decision datatype sort should be available");
    let vars = HashMap::from([(
        "decision".to_owned(),
        tm.mk_var(decision_sort.clone(), "decision"),
    )]);
    let dynamic_projection = IRExpr::Field {
        expr: Box::new(IRExpr::Var {
            name: "decision".to_owned(),
            ty: decision_ty.clone(),
            span: None,
        }),
        field: "amount".to_owned(),
        ty: IRType::Int,
        span: None,
    };
    encode_expr(&tm, &dynamic_projection, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("dynamic payload field projection should encode: {err}"));

    let static_projection = IRExpr::Field {
        expr: Box::new(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Accept".to_owned(),
            args: vec![("amount".to_owned(), int_lit(7))],
            span: None,
        }),
        field: "amount".to_owned(),
        ty: IRType::Int,
        span: None,
    };
    encode_expr(&tm, &static_projection, &HashMap::new(), &enum_catalog)
        .unwrap_or_else(|err| panic!("static payload field projection should encode: {err}"));
}

#[test]
fn sygus_core_accepts_payload_enum_fields_before_solver_setup() {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let system = IRSystem {
        name: "PayloadSystem".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "decision".to_owned(),
            ty: decision_ty.clone(),
            default: Some(IRExpr::Ctor {
                enum_name: "Decision".to_owned(),
                ctor: "Accept".to_owned(),
                args: vec![("amount".to_owned(), int_lit(0))],
                span: None,
            }),
            initial_constraint: None,
        }],
        entities: vec![],
        commands: vec![],
        actions: vec![],
        procs: vec![],
        invariants: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        queries: vec![],
        preds: vec![],
        let_bindings: vec![],
    };
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "decision".to_owned(),
                ty: decision_ty,
                span: None,
            }),
            arms: vec![
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PCtor {
                        name: "Accept".to_owned(),
                        fields: vec![crate::ir::types::IRFieldPat {
                            name: "amount".to_owned(),
                            pattern: crate::ir::types::IRPattern::PVar {
                                name: "payload".to_owned(),
                            },
                        }],
                    },
                    guard: None,
                    body: bin_expr(
                        "OpGe",
                        IRExpr::Var {
                            name: "payload".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        },
                        int_lit(0),
                        IRType::Bool,
                    ),
                },
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PWild,
                    guard: None,
                    body: bool_lit(true),
                },
            ],
            span: None,
        }),
        span: None,
    };

    let err = try_cvc5_sygus_system_safety_inner(&system, &property, 0)
        .expect_err("empty system should still be rejected after payload setup succeeds");
    assert!(
        err.contains("requires at least one step"),
        "payload enum fields should pass setup before the empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_expr_encoder_supports_finite_payload_enum_quantifiers() {
    let tm = Cvc5Tm::new();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "allowed".to_owned(),
                    ty: IRType::Bool,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let enum_catalog = EnumCatalog::from_types(&tm, std::slice::from_ref(&decision_ty))
        .expect("finite payload enum datatype catalog should build");
    let expr = IRExpr::Forall {
        var: "decision".to_owned(),
        domain: decision_ty.clone(),
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "decision".to_owned(),
                ty: decision_ty,
                span: None,
            }),
            arms: vec![
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PCtor {
                        name: "Accept".to_owned(),
                        fields: vec![crate::ir::types::IRFieldPat {
                            name: "allowed".to_owned(),
                            pattern: crate::ir::types::IRPattern::PVar {
                                name: "allowed".to_owned(),
                            },
                        }],
                    },
                    guard: None,
                    body: IRExpr::Var {
                        name: "allowed".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    },
                },
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PWild,
                    guard: None,
                    body: bool_lit(true),
                },
            ],
            span: None,
        }),
        span: None,
    };

    encode_expr(&tm, &expr, &HashMap::new(), &enum_catalog)
        .unwrap_or_else(|err| panic!("finite payload enum quantifier should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_finite_aggregate_kinds() {
    let tm = Cvc5Tm::new();
    let status_field = IRField {
        name: "status".to_owned(),
        ty: status_ty(),
        default: Some(status_ctor("Pending")),
        initial_constraint: None,
    };
    let enum_catalog = build_enum_catalog(&tm, &[status_field]).expect("enum catalog should build");

    let count_true = IRExpr::Aggregate {
        kind: IRAggKind::Count,
        var: "b".to_owned(),
        domain: IRType::Bool,
        body: Box::new(IRExpr::Var {
            name: "b".to_owned(),
            ty: IRType::Bool,
            span: None,
        }),
        in_filter: None,
        span: None,
    };
    encode_expr(&tm, &count_true, &HashMap::new(), &enum_catalog)
        .unwrap_or_else(|err| panic!("finite Count aggregate should encode: {err}"));

    let product_with_filter = IRExpr::Aggregate {
        kind: IRAggKind::Product,
        var: "b".to_owned(),
        domain: IRType::Bool,
        body: Box::new(IRExpr::IfElse {
            cond: Box::new(IRExpr::Var {
                name: "b".to_owned(),
                ty: IRType::Bool,
                span: None,
            }),
            then_body: Box::new(int_lit(2)),
            else_body: Some(Box::new(int_lit(3))),
            span: None,
        }),
        in_filter: Some(Box::new(IRExpr::Var {
            name: "b".to_owned(),
            ty: IRType::Bool,
            span: None,
        })),
        span: None,
    };
    encode_expr(&tm, &product_with_filter, &HashMap::new(), &enum_catalog)
        .unwrap_or_else(|err| panic!("finite Product aggregate should encode: {err}"));

    for kind in [IRAggKind::Min, IRAggKind::Max] {
        let aggregate = IRExpr::Aggregate {
            kind,
            var: "s".to_owned(),
            domain: status_ty(),
            body: Box::new(IRExpr::Var {
                name: "s".to_owned(),
                ty: IRType::Int,
                span: None,
            }),
            in_filter: None,
            span: None,
        };
        encode_expr(&tm, &aggregate, &HashMap::new(), &enum_catalog)
            .unwrap_or_else(|err| panic!("finite {kind:?} aggregate should encode: {err}"));
    }
}

#[test]
fn sygus_expr_encoder_supports_prime_wrappers() {
    let tm = Cvc5Tm::new();
    let vars = HashMap::from([("x".to_owned(), tm.mk_var(tm.integer_sort(), "x"))]);
    let enum_catalog = EnumCatalog::new();
    let expr = IRExpr::Prime {
        expr: Box::new(IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        }),
        span: None,
    };

    encode_expr(&tm, &expr, &vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("prime wrapper should encode: {err}"));
}

#[test]
fn sygus_expr_encoder_supports_derived_field_bindings() {
    let tm = Cvc5Tm::new();
    let mut vars = HashMap::from([("x".to_owned(), tm.mk_var(tm.integer_sort(), "x"))]);
    let enum_catalog = EnumCatalog::new();

    extend_with_derived_fields(
        &tm,
        &mut vars,
        &[nonnegative_derived_field()],
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("derived field should encode: {err}"));

    encode_expr(
        &tm,
        &IRExpr::Var {
            name: "nonnegative".to_owned(),
            ty: IRType::Bool,
            span: None,
        },
        &vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("derived field reference should encode: {err}"));
}

#[test]
fn sygus_param_enumerator_supports_finite_payload_enum_params() {
    let tm = Cvc5Tm::new();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "allowed".to_owned(),
                    ty: IRType::Bool,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let enum_catalog = EnumCatalog::from_types(&tm, std::slice::from_ref(&decision_ty))
        .expect("finite payload enum datatype catalog should build");
    let envs = enumerate_param_envs(
        &tm,
        &[crate::ir::types::IRTransParam {
            name: "decision".to_owned(),
            ty: decision_ty,
        }],
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("finite payload enum params should enumerate: {err}"));

    assert_eq!(envs.len(), 3);
    assert!(envs.iter().all(|env| env.contains_key("decision")));
}

#[test]
fn sygus_system_step_allows_unused_action_return_expr() {
    let tm = Cvc5Tm::new();
    let mut system = make_counter_system();
    system.actions[0].return_expr = Some(IRExpr::Var {
        name: "x".to_owned(),
        ty: IRType::Int,
        span: None,
    });
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("unused system action return expression should encode: {err}"));
}

#[test]
fn sygus_system_step_stages_top_level_exprstmt_updates() {
    let tm = Cvc5Tm::new();
    let mut system = make_counter_system();
    system.fields.push(IRField {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        default: Some(bool_lit(false)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "stage_root".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![
            crate::ir::types::IRAction::ExprStmt {
                expr: bin_expr(
                    "OpEq",
                    IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "x".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        span: None,
                    },
                    int_lit(1),
                    IRType::Bool,
                ),
            },
            crate::ir::types::IRAction::ExprStmt {
                expr: bin_expr(
                    "OpEq",
                    IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "flag".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    },
                    bin_expr(
                        "OpEq",
                        IRExpr::Var {
                            name: "x".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        },
                        int_lit(1),
                        IRType::Bool,
                    ),
                    IRType::Bool,
                ),
            },
        ],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("system ExprStmt sequence should encode: {err}"));
    let updates = collect_system_updates(
        &tm,
        &system.actions[0],
        &system.fields,
        &curr_vars,
        &enum_catalog,
    )
    .expect("system ExprStmt sequence updates should collect");
    let flag_rhs = updates
        .get("flag")
        .expect("flag should be updated")
        .to_string();
    assert!(
        !flag_rhs.contains("x"),
        "second top-level ExprStmt should read the staged x update, not current x: {flag_rhs}"
    );
}

#[test]
fn sygus_system_step_supports_real_fields_and_arithmetic() {
    let tm = Cvc5Tm::new();
    let mut system = make_counter_system();
    system.fields = vec![IRField {
        name: "balance".to_owned(),
        ty: IRType::Real,
        default: Some(real_lit(0.0)),
        initial_constraint: None,
    }];
    system.actions = vec![IRSystemAction {
        name: "deposit".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![crate::ir::types::IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "balance".to_owned(),
                        ty: IRType::Real,
                        span: None,
                    }),
                    span: None,
                },
                bin_expr(
                    "OpAdd",
                    IRExpr::Var {
                        name: "balance".to_owned(),
                        ty: IRType::Real,
                        span: None,
                    },
                    real_lit(1.5),
                    IRType::Real,
                ),
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_initial_field(&tm, &system.fields[0], &curr_vars, &enum_catalog)
        .unwrap_or_else(|err| panic!("real field default should encode: {err}"));
    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("real field action should encode: {err}"));
}

#[test]
fn sygus_system_step_supports_block_and_vardecl_rhs() {
    let tm = Cvc5Tm::new();
    let mut system = make_counter_system();
    system.actions = vec![IRSystemAction {
        name: "bind_then_update".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![crate::ir::types::IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Block {
                    exprs: vec![
                        bool_lit(true),
                        IRExpr::VarDecl {
                            name: "tmp".to_owned(),
                            ty: IRType::Int,
                            init: Box::new(int_lit(1)),
                            rest: Box::new(bin_expr(
                                "OpAdd",
                                IRExpr::Var {
                                    name: "tmp".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                                int_lit(1),
                                IRType::Int,
                            )),
                            span: None,
                        },
                    ],
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("block/vardecl RHS should encode: {err}"));
}

#[test]
fn sygus_system_step_supports_finite_aggregate_rhs() {
    let tm = Cvc5Tm::new();
    let mut system = make_counter_system();
    system.actions = vec![IRSystemAction {
        name: "aggregate_update".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![crate::ir::types::IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Aggregate {
                    kind: IRAggKind::Sum,
                    var: "b".to_owned(),
                    domain: IRType::Bool,
                    body: Box::new(IRExpr::IfElse {
                        cond: Box::new(IRExpr::Var {
                            name: "b".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        then_body: Box::new(int_lit(2)),
                        else_body: Some(Box::new(int_lit(1))),
                        span: None,
                    }),
                    in_filter: None,
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("finite aggregate RHS should encode: {err}"));
}

#[test]
fn sygus_system_step_supports_payload_field_projection_rhs() {
    let tm = Cvc5Tm::new();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let mut system = make_counter_system();
    system.fields.push(IRField {
        name: "decision".to_owned(),
        ty: decision_ty.clone(),
        default: Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Accept".to_owned(),
            args: vec![("amount".to_owned(), int_lit(3))],
            span: None,
        }),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "copy_payload".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![crate::ir::types::IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "x".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "decision".to_owned(),
                        ty: decision_ty,
                        span: None,
                    }),
                    field: "amount".to_owned(),
                    ty: IRType::Int,
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("payload field projection RHS should encode: {err}"));
}

#[test]
fn sygus_system_step_supports_action_match_on_system_field() {
    let tm = Cvc5Tm::new();
    let mut system = make_status_system();
    system.fields.push(IRField {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        default: Some(bool_lit(false)),
        initial_constraint: None,
    });
    system.fields.push(IRField {
        name: "count".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "match_status".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![crate::ir::types::IRAction::Match {
            scrutinee: crate::ir::types::IRActionMatchScrutinee::Var {
                name: "status".to_owned(),
            },
            arms: vec![
                crate::ir::types::IRActionMatchArm {
                    pattern: crate::ir::types::IRPattern::PCtor {
                        name: "Done".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: vec![
                        crate::ir::types::IRAction::ExprStmt {
                            expr: bin_expr(
                                "OpEq",
                                IRExpr::Prime {
                                    expr: Box::new(IRExpr::Var {
                                        name: "flag".to_owned(),
                                        ty: IRType::Bool,
                                        span: None,
                                    }),
                                    span: None,
                                },
                                bool_lit(true),
                                IRType::Bool,
                            ),
                        },
                        crate::ir::types::IRAction::ExprStmt {
                            expr: bin_expr(
                                "OpEq",
                                IRExpr::Prime {
                                    expr: Box::new(IRExpr::Var {
                                        name: "count".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    span: None,
                                },
                                IRExpr::IfElse {
                                    cond: Box::new(IRExpr::Var {
                                        name: "flag".to_owned(),
                                        ty: IRType::Bool,
                                        span: None,
                                    }),
                                    then_body: Box::new(int_lit(1)),
                                    else_body: Some(Box::new(int_lit(0))),
                                    span: None,
                                },
                                IRType::Bool,
                            ),
                        },
                    ],
                },
                crate::ir::types::IRActionMatchArm {
                    pattern: crate::ir::types::IRPattern::PWild,
                    guard: None,
                    body: vec![crate::ir::types::IRAction::ExprStmt {
                        expr: bin_expr(
                            "OpEq",
                            IRExpr::Prime {
                                expr: Box::new(IRExpr::Var {
                                    name: "flag".to_owned(),
                                    ty: IRType::Bool,
                                    span: None,
                                }),
                                span: None,
                            },
                            bool_lit(false),
                            IRType::Bool,
                        ),
                    }],
                },
            ],
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("system action match should encode: {err}"));

    let updates = collect_system_updates(
        &tm,
        &system.actions[0],
        &system.fields,
        &curr_vars,
        &enum_catalog,
    )
    .expect("system action match updates should collect");
    let count_rhs = updates
        .get("count")
        .expect("count should be updated")
        .to_string();
    assert!(
        !count_rhs.contains("flag"),
        "second match-arm update should read the staged flag update, not the current flag: {count_rhs}"
    );
}

#[test]
fn sygus_core_accepts_initial_field_constraints_before_solver_setup() {
    let mut system = make_counter_system();
    system.fields[0].default = None;
    system.fields[0].initial_constraint = Some(bin_expr(
        "OpGe",
        IRExpr::Var {
            name: "$".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        int_lit(0),
        IRType::Bool,
    ));
    system.actions.clear();

    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("empty system should still be rejected after initial constraint setup");
    assert!(
        err.contains("requires at least one step"),
        "initial constraints should pass setup before the empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_single_entity_transition_supports_postconditions() {
    let tm = Cvc5Tm::new();
    let mut entity = make_counter_entity();
    entity.transitions[0].postcondition = Some(bin_expr(
        "OpGe",
        IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        int_lit(1),
        IRType::Bool,
    ));
    let enum_catalog = build_enum_catalog(&tm, &entity.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &entity.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_transition(
        &tm,
        &entity.transitions[0],
        &entity.fields,
        &entity.derived_fields,
        &entity.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("single-entity transition postcondition should encode: {err}"));
}

#[test]
fn sygus_pooled_transition_supports_postconditions() {
    let tm = Cvc5Tm::new();
    let mut entity = make_counter_entity();
    entity.transitions[0].postcondition = Some(bin_expr(
        "OpGe",
        IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        int_lit(1),
        IRType::Bool,
    ));
    let enum_catalog = build_enum_catalog(&tm, &entity.fields).expect("enum catalog should build");

    encode_pooled_transition_at_slot_for_test(&tm, &entity.transitions[0], &entity, &enum_catalog)
        .unwrap_or_else(|err| panic!("pooled transition postcondition should encode: {err}"));
}

#[test]
fn sygus_pooled_transition_supports_derived_field_guards_and_postconditions() {
    let tm = Cvc5Tm::new();
    let mut entity = make_counter_entity();
    entity.derived_fields.push(nonnegative_derived_field());
    entity.transitions[0].guard = IRExpr::Var {
        name: "nonnegative".to_owned(),
        ty: IRType::Bool,
        span: None,
    };
    entity.transitions[0].postcondition = Some(IRExpr::Var {
        name: "nonnegative".to_owned(),
        ty: IRType::Bool,
        span: None,
    });
    let enum_catalog = build_enum_catalog_with_derived(&tm, &entity.fields, &entity.derived_fields)
        .expect("enum catalog should build");

    encode_pooled_transition_at_slot_for_test(&tm, &entity.transitions[0], &entity, &enum_catalog)
        .unwrap_or_else(|err| {
            panic!("pooled transition derived guard/postcondition should encode: {err}")
        });
}

#[test]
fn sygus_single_entity_transition_supports_fsm_constraints() {
    let tm = Cvc5Tm::new();
    let mut entity = make_status_entity();
    entity.fsm_decls.push(pending_to_done_fsm("status"));
    let enum_catalog = build_enum_catalog(&tm, &entity.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &entity.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_transition(
        &tm,
        &entity.transitions[0],
        &entity.fields,
        &entity.derived_fields,
        &entity.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("single-entity transition FSM constraint should encode: {err}"));
}

#[test]
fn sygus_system_step_supports_fsm_constraints() {
    let tm = Cvc5Tm::new();
    let mut system = make_status_system();
    system.fsm_decls.push(pending_to_done_fsm("status"));
    let enum_catalog = build_enum_catalog(&tm, &system.fields).expect("enum catalog should build");
    let mut curr_vars = HashMap::new();
    let mut next_vars = HashMap::new();
    for field in &system.fields {
        let sort = sort_for_field(&tm, field, &enum_catalog).expect("field sort should build");
        curr_vars.insert(field.name.clone(), tm.mk_var(sort.clone(), &field.name));
        next_vars.insert(
            field.name.clone(),
            tm.mk_var(sort, &format!("{}_next", field.name)),
        );
    }

    encode_system_step(
        &tm,
        &system.actions[0],
        &system.fields,
        &system.fsm_decls,
        &curr_vars,
        &next_vars,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("system step FSM constraint should encode: {err}"));
}

#[test]
fn sygus_pooled_transition_supports_fsm_constraints() {
    let tm = Cvc5Tm::new();
    let mut entity = make_status_entity();
    entity.fsm_decls.push(pending_to_done_fsm("status"));
    let enum_catalog = build_enum_catalog(&tm, &entity.fields).expect("enum catalog should build");

    encode_pooled_transition_at_slot_for_test(&tm, &entity.transitions[0], &entity, &enum_catalog)
        .unwrap_or_else(|err| panic!("pooled transition FSM constraint should encode: {err}"));
}

#[test]
fn sygus_accepts_fsm_decls_before_solver_setup() {
    let mut entity = make_status_entity();
    entity.fsm_decls.push(pending_to_done_fsm("status"));
    entity.transitions.clear();
    let err = try_cvc5_sygus_single_entity_inner(&entity, &non_negative_property(), 0)
        .expect_err("empty entity should still be rejected after FSM setup");
    assert!(
        err.contains("requires at least one transition"),
        "entity FSM declarations should pass setup before empty-transition diagnostic, got: {err}"
    );

    let mut system = make_status_system();
    system.fsm_decls.push(pending_to_done_fsm("status"));
    system.actions.clear();
    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("empty system should still be rejected after FSM setup");
    assert!(
        err.contains("requires at least one step"),
        "system FSM declarations should pass setup before empty-step diagnostic, got: {err}"
    );

    let mut pooled_entity = make_status_entity();
    pooled_entity.fsm_decls.push(pending_to_done_fsm("status"));
    let mut pooled_system = make_pooled_store_counter_system();
    pooled_system.entities = vec!["StatusEntity".to_owned()];
    pooled_system.store_params[0].entity_type = "StatusEntity".to_owned();
    pooled_system.actions.clear();
    let err = try_cvc5_sygus_pooled_system_safety_inner(
        &pooled_system,
        &pooled_entity,
        2,
        &non_negative_property(),
        0,
    )
    .expect_err("empty pooled system should still be rejected after entity FSM setup");
    assert!(
        err.contains("requires at least one step"),
        "pooled entity FSM declarations should pass setup before empty-step diagnostic, got: {err}"
    );

    pooled_entity.fsm_decls.clear();
    pooled_system.fields.push(IRField {
        name: "status".to_owned(),
        ty: status_ty(),
        default: Some(status_ctor("Pending")),
        initial_constraint: None,
    });
    pooled_system.fsm_decls.push(pending_to_done_fsm("status"));
    let err = try_cvc5_sygus_pooled_system_safety_inner(
        &pooled_system,
        &pooled_entity,
        2,
        &non_negative_property(),
        0,
    )
    .expect_err("empty pooled system should still be rejected after system FSM setup");
    assert!(
        err.contains("requires at least one step"),
        "pooled system FSM declarations should pass setup before empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_pooled_accepts_derived_fields_before_solver_setup() {
    let mut entity = make_counter_entity();
    let mut system = make_pooled_store_counter_system();
    system.actions.clear();
    system.derived_fields.push(true_derived_field());
    let err =
        try_cvc5_sygus_pooled_system_safety_inner(&system, &entity, 2, &non_negative_property(), 0)
            .expect_err("empty pooled system should still be rejected after system derived setup");
    assert!(
        err.contains("requires at least one step"),
        "pooled system derived fields should pass setup before empty-step diagnostic, got: {err}"
    );

    entity.derived_fields.push(nonnegative_derived_field());
    system.derived_fields.clear();
    let err =
        try_cvc5_sygus_pooled_system_safety_inner(&system, &entity, 2, &non_negative_property(), 0)
            .expect_err("empty pooled system should still be rejected after entity derived setup");
    assert!(
        err.contains("requires at least one step"),
        "pooled entity derived fields should pass setup before empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_pooled_system_step_supports_root_field_exprstmt() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "total".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "bump_total".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                bin_expr(
                    "OpAdd",
                    IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    },
                    int_lit(1),
                    IRType::Int,
                ),
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled root field ExprStmt should encode: {err}"));
}

#[test]
fn sygus_pooled_nested_exprstmt_updates_selected_entity_field() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.actions = vec![IRSystemAction {
        name: "bump_selected".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::Choose {
            var: "c".to_owned(),
            entity: "Counter".to_owned(),
            filter: Box::new(bool_lit(true)),
            ops: vec![IRAction::ExprStmt {
                expr: bin_expr(
                    "OpEq",
                    IRExpr::Prime {
                        expr: Box::new(IRExpr::Field {
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
                        span: None,
                    },
                    bin_expr(
                        "OpAdd",
                        IRExpr::Field {
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
                        },
                        int_lit(1),
                        IRType::Int,
                    ),
                    IRType::Bool,
                ),
            }],
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &entity.fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled nested entity-field ExprStmt should encode: {err}"));
}

#[test]
fn sygus_pooled_nested_exprstmt_sequences_update_selected_entity_fields() {
    let tm = Cvc5Tm::new();
    let mut entity = make_pooled_counter_entity();
    entity.fields.push(IRField {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        default: Some(bool_lit(false)),
        initial_constraint: None,
    });
    let mut system = make_pooled_counter_system();
    system.actions = vec![IRSystemAction {
        name: "stage_selected".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::Choose {
            var: "c".to_owned(),
            entity: "Counter".to_owned(),
            filter: Box::new(bool_lit(true)),
            ops: vec![
                IRAction::ExprStmt {
                    expr: bin_expr(
                        "OpEq",
                        IRExpr::Prime {
                            expr: Box::new(IRExpr::Field {
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
                            span: None,
                        },
                        int_lit(1),
                        IRType::Bool,
                    ),
                },
                IRAction::ExprStmt {
                    expr: bin_expr(
                        "OpEq",
                        IRExpr::Prime {
                            expr: Box::new(IRExpr::Field {
                                expr: Box::new(IRExpr::Var {
                                    name: "c".to_owned(),
                                    ty: IRType::Entity {
                                        name: "Counter".to_owned(),
                                    },
                                    span: None,
                                }),
                                field: "flag".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        },
                        bin_expr(
                            "OpEq",
                            IRExpr::Field {
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
                            },
                            int_lit(1),
                            IRType::Bool,
                        ),
                        IRType::Bool,
                    ),
                },
            ],
        }],
        return_expr: None,
    }];
    let enum_catalog = build_enum_catalog(&tm, &entity.fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    let formula = encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| {
        panic!("pooled nested entity-field ExprStmt sequence should encode: {err}")
    });
    let formula = formula.to_string();
    assert!(
        !formula.contains("(= Counter_0_flag_next Counter_0_flag)"),
        "second nested ExprStmt should update flag from staged x instead of framing it, got: {formula}"
    );
}

#[test]
fn sygus_pooled_multi_action_tracks_root_field_intermediates() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "total".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "bump_total_then_counter".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![
            IRAction::ExprStmt {
                expr: bin_expr(
                    "OpEq",
                    IRExpr::Prime {
                        expr: Box::new(IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        }),
                        span: None,
                    },
                    bin_expr(
                        "OpAdd",
                        IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        },
                        int_lit(1),
                        IRType::Int,
                    ),
                    IRType::Bool,
                ),
            },
            IRAction::Choose {
                var: "c".to_owned(),
                entity: "Counter".to_owned(),
                filter: Box::new(bool_lit(true)),
                ops: vec![IRAction::ExprStmt {
                    expr: bin_expr(
                        "OpEq",
                        IRExpr::Prime {
                            expr: Box::new(IRExpr::Field {
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
                            span: None,
                        },
                        IRExpr::Var {
                            name: "total".to_owned(),
                            ty: IRType::Int,
                            span: None,
                        },
                        IRType::Bool,
                    ),
                }],
            },
        ],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| {
        panic!("pooled multi-action root-field intermediate should encode: {err}")
    });
}

#[test]
fn sygus_pooled_system_step_supports_finite_choose_exprstmt_rhs() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        default: Some(bool_lit(false)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "set_flag".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "flag".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Choose {
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
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled finite choose RHS should encode: {err}"));
}

#[test]
fn sygus_pooled_system_step_supports_inline_lambda_application_rhs() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        default: Some(bool_lit(false)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "set_flag".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "flag".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::App {
                    func: Box::new(IRExpr::Lam {
                        param: "b".to_owned(),
                        param_type: IRType::Bool,
                        body: Box::new(IRExpr::Var {
                            name: "b".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        span: None,
                    }),
                    arg: Box::new(bool_lit(true)),
                    ty: IRType::Bool,
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled inline lambda application RHS should encode: {err}"));
}

#[test]
fn sygus_pooled_system_step_supports_block_and_vardecl_rhs() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "total".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "bind_then_update".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Block {
                    exprs: vec![
                        bool_lit(true),
                        IRExpr::VarDecl {
                            name: "tmp".to_owned(),
                            ty: IRType::Int,
                            init: Box::new(int_lit(1)),
                            rest: Box::new(bin_expr(
                                "OpAdd",
                                IRExpr::Var {
                                    name: "tmp".to_owned(),
                                    ty: IRType::Int,
                                    span: None,
                                },
                                int_lit(1),
                                IRType::Int,
                            )),
                            span: None,
                        },
                    ],
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled block/vardecl RHS should encode: {err}"));
}

#[test]
fn sygus_pooled_system_step_supports_finite_aggregate_rhs() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "total".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "aggregate_update".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Aggregate {
                    kind: IRAggKind::Sum,
                    var: "b".to_owned(),
                    domain: IRType::Bool,
                    body: Box::new(IRExpr::IfElse {
                        cond: Box::new(IRExpr::Var {
                            name: "b".to_owned(),
                            ty: IRType::Bool,
                            span: None,
                        }),
                        then_body: Box::new(int_lit(2)),
                        else_body: Some(Box::new(int_lit(1))),
                        span: None,
                    }),
                    in_filter: None,
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled finite aggregate RHS should encode: {err}"));
}

#[test]
fn sygus_pooled_system_step_supports_payload_field_projection_rhs() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![
            IRVariant {
                name: "Accept".to_owned(),
                fields: vec![crate::ir::types::IRVariantField {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
            },
            IRVariant::simple("Reject"),
        ],
    };
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "total".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.fields.push(IRField {
        name: "decision".to_owned(),
        ty: decision_ty.clone(),
        default: Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Accept".to_owned(),
            args: vec![("amount".to_owned(), int_lit(3))],
            span: None,
        }),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "copy_payload".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::ExprStmt {
            expr: bin_expr(
                "OpEq",
                IRExpr::Prime {
                    expr: Box::new(IRExpr::Var {
                        name: "total".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
                IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "decision".to_owned(),
                        ty: decision_ty,
                        span: None,
                    }),
                    field: "amount".to_owned(),
                    ty: IRType::Int,
                    span: None,
                },
                IRType::Bool,
            ),
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled payload field projection RHS should encode: {err}"));
}

#[test]
fn sygus_pooled_system_step_supports_action_match_on_system_field() {
    let tm = Cvc5Tm::new();
    let entity = make_pooled_counter_entity();
    let mut system = make_pooled_counter_system();
    system.fields.push(IRField {
        name: "status".to_owned(),
        ty: status_ty(),
        default: Some(status_ctor("Pending")),
        initial_constraint: None,
    });
    system.fields.push(IRField {
        name: "flag".to_owned(),
        ty: IRType::Bool,
        default: Some(bool_lit(false)),
        initial_constraint: None,
    });
    system.fields.push(IRField {
        name: "count".to_owned(),
        ty: IRType::Int,
        default: Some(int_lit(0)),
        initial_constraint: None,
    });
    system.actions = vec![IRSystemAction {
        name: "match_status".to_owned(),
        params: vec![],
        guard: bool_lit(true),
        body: vec![IRAction::Match {
            scrutinee: crate::ir::types::IRActionMatchScrutinee::Var {
                name: "status".to_owned(),
            },
            arms: vec![
                crate::ir::types::IRActionMatchArm {
                    pattern: crate::ir::types::IRPattern::PCtor {
                        name: "Done".to_owned(),
                        fields: vec![],
                    },
                    guard: None,
                    body: vec![
                        IRAction::ExprStmt {
                            expr: bin_expr(
                                "OpEq",
                                IRExpr::Prime {
                                    expr: Box::new(IRExpr::Var {
                                        name: "flag".to_owned(),
                                        ty: IRType::Bool,
                                        span: None,
                                    }),
                                    span: None,
                                },
                                bool_lit(true),
                                IRType::Bool,
                            ),
                        },
                        IRAction::ExprStmt {
                            expr: bin_expr(
                                "OpEq",
                                IRExpr::Prime {
                                    expr: Box::new(IRExpr::Var {
                                        name: "count".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    span: None,
                                },
                                int_lit(1),
                                IRType::Bool,
                            ),
                        },
                    ],
                },
                crate::ir::types::IRActionMatchArm {
                    pattern: crate::ir::types::IRPattern::PWild,
                    guard: None,
                    body: vec![
                        IRAction::ExprStmt {
                            expr: bin_expr(
                                "OpEq",
                                IRExpr::Prime {
                                    expr: Box::new(IRExpr::Var {
                                        name: "flag".to_owned(),
                                        ty: IRType::Bool,
                                        span: None,
                                    }),
                                    span: None,
                                },
                                bool_lit(false),
                                IRType::Bool,
                            ),
                        },
                        IRAction::ExprStmt {
                            expr: bin_expr(
                                "OpEq",
                                IRExpr::Prime {
                                    expr: Box::new(IRExpr::Var {
                                        name: "count".to_owned(),
                                        ty: IRType::Int,
                                        span: None,
                                    }),
                                    span: None,
                                },
                                int_lit(0),
                                IRType::Bool,
                            ),
                        },
                    ],
                },
            ],
        }],
        return_expr: None,
    }];
    let all_fields = system
        .fields
        .iter()
        .cloned()
        .chain(entity.fields.iter().cloned())
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_test(
        &tm,
        &system.actions[0],
        &system,
        std::slice::from_ref(&entity),
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| panic!("pooled action match on system field should encode: {err}"));
}

#[test]
fn sygus_pooled_action_match_guards_can_read_let_crosscall_locals() {
    let tm = Cvc5Tm::new();
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Bump"), IRVariant::simple("Hold")],
    };
    let mut entity = make_pooled_counter_entity();
    entity.fields.push(IRField {
        name: "decision_seed".to_owned(),
        ty: decision_ty.clone(),
        default: Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Hold".to_owned(),
            args: vec![],
            span: None,
        }),
        initial_constraint: None,
    });
    let relay = IRSystem {
        name: "CounterRelay".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "relay_match_guard".to_owned(),
            params: vec![],
            guard: bool_lit(true),
            body: vec![
                IRAction::LetCrossCall {
                    name: "decision".to_owned(),
                    system: "DecisionWorker".to_owned(),
                    command: "decide".to_owned(),
                    args: vec![],
                },
                IRAction::Match {
                    scrutinee: crate::ir::types::IRActionMatchScrutinee::Var {
                        name: "decision".to_owned(),
                    },
                    arms: vec![
                        crate::ir::types::IRActionMatchArm {
                            pattern: crate::ir::types::IRPattern::PCtor {
                                name: "Bump".to_owned(),
                                fields: vec![],
                            },
                            guard: Some(bin_expr(
                                "OpEq",
                                IRExpr::Var {
                                    name: "decision".to_owned(),
                                    ty: decision_ty.clone(),
                                    span: None,
                                },
                                IRExpr::Ctor {
                                    enum_name: "Decision".to_owned(),
                                    ctor: "Bump".to_owned(),
                                    args: vec![],
                                    span: None,
                                },
                                IRType::Bool,
                            )),
                            body: vec![IRAction::Match {
                                scrutinee: crate::ir::types::IRActionMatchScrutinee::Var {
                                    name: "decision".to_owned(),
                                },
                                arms: vec![
                                    crate::ir::types::IRActionMatchArm {
                                        pattern: crate::ir::types::IRPattern::PCtor {
                                            name: "Bump".to_owned(),
                                            fields: vec![],
                                        },
                                        guard: None,
                                        body: vec![IRAction::Choose {
                                            var: "c".to_owned(),
                                            entity: "Counter".to_owned(),
                                            filter: Box::new(bool_lit(true)),
                                            ops: vec![IRAction::Apply {
                                                target: "c".to_owned(),
                                                transition: "inc".to_owned(),
                                                refs: vec![],
                                                args: vec![],
                                            }],
                                        }],
                                    },
                                    crate::ir::types::IRActionMatchArm {
                                        pattern: crate::ir::types::IRPattern::PWild,
                                        guard: None,
                                        body: vec![],
                                    },
                                ],
                            }],
                        },
                        crate::ir::types::IRActionMatchArm {
                            pattern: crate::ir::types::IRPattern::PWild,
                            guard: None,
                            body: vec![],
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
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "decide".to_owned(),
            params: vec![],
            guard: bool_lit(true),
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
    let all_fields = relay
        .fields
        .iter()
        .chain(worker.fields.iter())
        .chain(entity.fields.iter())
        .cloned()
        .collect::<Vec<_>>();
    let enum_catalog = build_enum_catalog(&tm, &all_fields).expect("enum catalog should build");
    let slots_per_entity = HashMap::from([(entity.name.clone(), 1usize)]);

    encode_pooled_system_step_for_systems_test(
        &tm,
        &relay.actions[0],
        &relay,
        &[relay.clone(), worker],
        &[entity],
        &slots_per_entity,
        &enum_catalog,
    )
    .unwrap_or_else(|err| {
        panic!("pooled action match guards should read LetCrossCall locals: {err}")
    });
}

#[test]
fn sygus_core_accepts_command_metadata_before_solver_setup() {
    let mut system = make_counter_system();
    system.commands.push(crate::ir::types::IRCommand {
        name: "inc".to_owned(),
        params: vec![],
        return_type: None,
    });
    system.actions.clear();
    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("empty system should still be rejected after command metadata setup");
    assert!(
        err.contains("requires at least one step"),
        "command metadata should pass setup before empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_pooled_accepts_command_metadata_before_solver_setup() {
    let entity = make_counter_entity();
    let mut system = make_pooled_store_counter_system();
    system.commands.push(crate::ir::types::IRCommand {
        name: "create_counter".to_owned(),
        params: vec![],
        return_type: None,
    });
    system.actions.clear();
    let err =
        try_cvc5_sygus_pooled_system_safety_inner(&system, &entity, 2, &non_negative_property(), 0)
            .expect_err(
                "empty pooled system should still be rejected after command metadata setup",
            );
    assert!(
        err.contains("requires at least one step"),
        "pooled command metadata should pass setup before empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_core_accepts_query_and_pred_metadata_before_solver_setup() {
    let mut system = make_counter_system();
    system.queries.push(crate::ir::types::IRQuery {
        name: "is_nonnegative".to_owned(),
        params: vec![],
        requires: vec![],
        body: IRExpr::Var {
            name: "nonnegative".to_owned(),
            ty: IRType::Bool,
            span: None,
        },
    });
    system.preds.push(crate::ir::types::IRFunction {
        name: "always_ok".to_owned(),
        ty: IRType::Bool,
        body: bool_lit(true),
        prop_target: None,
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: None,
        file: None,
    });
    system.actions.clear();

    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("empty system should still be rejected after query/pred metadata setup");
    assert!(
        err.contains("requires at least one step"),
        "query/pred metadata should pass setup before empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_pooled_accepts_query_and_pred_metadata_before_solver_setup() {
    let entity = make_counter_entity();
    let mut system = make_pooled_store_counter_system();
    system.queries.push(crate::ir::types::IRQuery {
        name: "any_counter".to_owned(),
        params: vec![],
        requires: vec![],
        body: bool_lit(true),
    });
    system.preds.push(crate::ir::types::IRFunction {
        name: "pool_ok".to_owned(),
        ty: IRType::Bool,
        body: bool_lit(true),
        prop_target: None,
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: None,
        file: None,
    });
    system.actions.clear();

    let err =
        try_cvc5_sygus_pooled_system_safety_inner(&system, &entity, 2, &non_negative_property(), 0)
            .expect_err(
                "empty pooled system should still be rejected after query/pred metadata setup",
            );
    assert!(
        err.contains("requires at least one step"),
        "pooled query/pred metadata should pass setup before empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_keeps_let_bindings_as_topology_boundary() {
    let mut system = make_counter_system();
    system.let_bindings.push(crate::ir::types::IRLetBinding {
        name: "child".to_owned(),
        system_type: "CounterSys".to_owned(),
        store_bindings: vec![],
    });
    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("let binding topology should remain unsupported");
    assert!(err.contains("let-bindings"));

    let entity = make_counter_entity();
    let mut pooled = make_pooled_store_counter_system();
    pooled.let_bindings.push(crate::ir::types::IRLetBinding {
        name: "child".to_owned(),
        system_type: "CounterStorePool".to_owned(),
        store_bindings: vec![],
    });
    let err =
        try_cvc5_sygus_pooled_system_safety_inner(&pooled, &entity, 2, &non_negative_property(), 0)
            .expect_err("pooled let binding topology should remain unsupported");
    assert!(err.contains("let-bindings"));
}

#[test]
fn sygus_core_accepts_derived_fields_before_solver_setup() {
    let mut derived_entity = make_counter_entity();
    derived_entity
        .derived_fields
        .push(nonnegative_derived_field());
    derived_entity.transitions.clear();
    let err = try_cvc5_sygus_single_entity_inner(&derived_entity, &non_negative_property(), 0)
        .expect_err("empty entity should still be rejected after derived setup");
    assert!(
        err.contains("requires at least one transition"),
        "derived fields should pass setup before the empty-transition diagnostic, got: {err}"
    );

    let mut derived_system = make_counter_system();
    derived_system
        .derived_fields
        .push(nonnegative_derived_field());
    derived_system.actions.clear();
    let err = try_cvc5_sygus_system_safety_inner(&derived_system, &non_negative_property(), 0)
        .expect_err("empty system should still be rejected after derived setup");
    assert!(
        err.contains("requires at least one step"),
        "derived fields should pass setup before the empty-step diagnostic, got: {err}"
    );
}

#[test]
fn sygus_core_reports_unsupported_shapes_before_solver_setup() {
    use crate::ir::types::IRStoreParam;

    let mut no_transition = make_counter_entity();
    no_transition.transitions.clear();
    let err = try_cvc5_sygus_single_entity_inner(&no_transition, &non_negative_property(), 0)
        .expect_err("transition required");
    assert!(err.contains("requires at least one transition"));

    let mut system = make_counter_system();
    system.store_params.push(IRStoreParam {
        name: "counters".to_owned(),
        entity_type: "Counter".to_owned(),
    });
    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("store params unsupported");
    assert!(err.contains("store params"));

    let mut system = make_counter_system();
    system.entities.push("Counter".to_owned());
    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("entity pools unsupported");
    assert!(err.contains("entity pools"));

    let mut left = make_counter_system();
    left.name = "Left".to_owned();
    let mut right = make_counter_system();
    right.name = "Right".to_owned();
    let err = collect_unique_system_fields(&[left, right]).expect_err("duplicate field");
    assert!(err.contains("globally unique system field names"));
}

fn make_counter_system() -> IRSystem {
    IRSystem {
        name: "CounterSys".to_owned(),
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
            body: vec![crate::ir::types::IRAction::ExprStmt {
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
    }
}

fn make_status_system() -> IRSystem {
    let status_ty = status_ty();
    IRSystem {
        name: "StatusSys".to_owned(),
        store_params: vec![],
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(status_ctor("Pending")),
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
            body: vec![crate::ir::types::IRAction::ExprStmt {
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
    }
}

fn make_status_entity() -> IREntity {
    let status_ty = status_ty();
    IREntity {
        name: "StatusEntity".to_owned(),
        fields: vec![IRField {
            name: "status".to_owned(),
            ty: status_ty.clone(),
            default: Some(status_ctor("Pending")),
            initial_constraint: None,
        }],
        transitions: vec![IRTransition {
            name: "finish".to_owned(),
            refs: vec![],
            params: vec![],
            guard: bin_expr(
                "OpEq",
                IRExpr::Var {
                    name: "status".to_owned(),
                    ty: status_ty.clone(),
                    span: None,
                },
                status_ctor("Pending"),
                IRType::Bool,
            ),
            updates: vec![crate::ir::types::IRUpdate {
                field: "status".to_owned(),
                value: status_ctor("Done"),
            }],
            postcondition: None,
        }],
        derived_fields: vec![],
        invariants: vec![],
        fsm_decls: vec![],
    }
}

fn make_bool_param_system() -> IRSystem {
    IRSystem {
        name: "ToggleSys".to_owned(),
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
            body: vec![crate::ir::types::IRAction::ExprStmt {
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
    }
}

fn make_bool_param_entity() -> IREntity {
    IREntity {
        name: "ToggleEntity".to_owned(),
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
        transitions: vec![IRTransition {
            name: "set_flag".to_owned(),
            refs: vec![],
            params: vec![IRTransParam {
                name: "next_flag".to_owned(),
                ty: IRType::Bool,
            }],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            updates: vec![crate::ir::types::IRUpdate {
                field: "flag".to_owned(),
                value: IRExpr::Var {
                    name: "next_flag".to_owned(),
                    ty: IRType::Bool,
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

fn make_invariant_counter_system() -> IRSystem {
    let mut system = make_counter_system();
    system.invariants.push(crate::ir::types::IRInvariant {
        name: "x_non_negative".to_owned(),
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
    });
    system
}

fn make_match_status_system() -> IRSystem {
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    IRSystem {
        name: "MatchStatusSys".to_owned(),
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
            body: vec![crate::ir::types::IRAction::ExprStmt {
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
                            crate::ir::types::IRMatchArm {
                                pattern: crate::ir::types::IRPattern::PCtor {
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
                            crate::ir::types::IRMatchArm {
                                pattern: crate::ir::types::IRPattern::PWild,
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
    }
}

fn make_pooled_counter_entity() -> IREntity {
    IREntity {
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
            updates: vec![crate::ir::types::IRUpdate {
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
    }
}

fn make_pooled_counter_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_pooled_ticket_entity() -> IREntity {
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![
            IRVariant::simple("Pending"),
            IRVariant::simple("Active"),
            IRVariant::simple("Closed"),
        ],
    };
    IREntity {
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
            updates: vec![crate::ir::types::IRUpdate {
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
    }
}

fn make_pooled_ticket_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_pooled_ref_counter_entity() -> IREntity {
    IREntity {
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
            refs: vec![crate::ir::types::IRTransRef {
                name: "peer".to_owned(),
                entity: "Counter".to_owned(),
            }],
            params: vec![],
            guard: IRExpr::BinOp {
                op: "OpGe".to_owned(),
                left: Box::new(IRExpr::Field {
                    expr: Box::new(IRExpr::Var {
                        name: "peer".to_owned(),
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
            },
            updates: vec![crate::ir::types::IRUpdate {
                field: "x".to_owned(),
                value: IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Field {
                        expr: Box::new(IRExpr::Var {
                            name: "peer".to_owned(),
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

fn make_pooled_ref_counter_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_pooled_bool_param_counter_entity() -> IREntity {
    IREntity {
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
            updates: vec![crate::ir::types::IRUpdate {
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
    }
}

fn make_pooled_bool_param_counter_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_pooled_apply_chain_entity() -> IREntity {
    IREntity {
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
                    crate::ir::types::IRUpdate {
                        field: "status".to_owned(),
                        value: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 1 },
                            span: None,
                        },
                    },
                    crate::ir::types::IRUpdate {
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
                updates: vec![crate::ir::types::IRUpdate {
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
    }
}

fn make_pooled_apply_chain_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_pooled_create_then_inc_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_pooled_store_counter_system() -> IRSystem {
    IRSystem {
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
    }
}

fn make_multi_pooled_entities() -> Vec<IREntity> {
    vec![
        IREntity {
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
                refs: vec![crate::ir::types::IRTransRef {
                    name: "m".to_owned(),
                    entity: "Marker".to_owned(),
                }],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpGe".to_owned(),
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
                        value: LitVal::Int { value: 0 },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![crate::ir::types::IRUpdate {
                    field: "x".to_owned(),
                    value: IRExpr::BinOp {
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
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        },
        IREntity {
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
        },
    ]
}

fn make_multi_pooled_system() -> IRSystem {
    IRSystem {
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
    }
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_single_entity_proves_simple_non_negative_counter() {
    let entity = make_counter_entity();
    let property = non_negative_property();

    let result = try_cvc5_sygus_single_entity(&entity, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove simple single-entity safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_single_entity_matches_current_z3_ic3_on_simple_counter() {
    let entity = make_counter_entity();
    let property = non_negative_property();
    let ir = IRProgram {
        types: vec![],
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

    let z3_result = ic3::try_ic3_single_entity(&entity, &vctx, &property, 5_000);
    let sygus_result = try_cvc5_sygus_single_entity(&entity, &property, 5_000);

    assert!(matches!(z3_result, Ic3Result::Proved));
    assert!(matches!(sygus_result, Ic3Result::Proved));
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn active_cvc5_transition_backend_uses_sygus_for_single_entity_safety() {
    let entity = make_counter_entity();
    let property = non_negative_property();
    let ir = IRProgram {
        types: vec![],
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
    let previous = active_solver_family();
    set_active_solver_family(SolverFamily::Cvc5).unwrap();

    let result = solve_transition_obligation(TransitionObligation::SingleEntitySafety {
        entity: &entity,
        vctx: &vctx,
        property: &property,
        timeout_ms: 5_000,
    });

    set_active_solver_family(previous).unwrap();
    assert!(matches!(result, Ic3Result::Proved));
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_single_entity_returns_unknown_for_unsupported_transition_params() {
    let mut entity = make_counter_entity();
    entity.transitions[0]
        .params
        .push(crate::ir::types::IRTransParam {
            name: "delta".to_owned(),
            ty: IRType::Int,
        });
    let property = non_negative_property();

    let result = try_cvc5_sygus_single_entity(&entity, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref msg) if msg.contains("only supports finite Bool/enum action params")),
        "expected honest Unknown for unsupported SyGuS shape, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_single_entity_supports_finite_bool_transition_params() {
    let entity = make_bool_param_entity();
    let property = IRExpr::Always {
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
    };

    let result = try_cvc5_sygus_single_entity(&entity, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove bool-param single-entity safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_proves_simple_non_negative_counter() {
    let system = make_counter_system();
    let property = non_negative_property();

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove simple system-field safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_supports_fieldless_enum_status_machine() {
    let system = make_status_system();
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let property = IRExpr::Always {
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
    };

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove fieldless enum system safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_supports_finite_bool_step_params() {
    let system = make_bool_param_system();
    let property = IRExpr::Always {
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
    };

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove bool-param system safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_supports_system_invariants() {
    let system = make_invariant_counter_system();
    let property = non_negative_property();

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove invariant-bearing system safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_supports_match_expressions() {
    let system = make_match_status_system();
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Match {
            scrutinee: Box::new(IRExpr::Var {
                name: "status".to_owned(),
                ty: status_ty.clone(),
                span: None,
            }),
            arms: vec![
                crate::ir::types::IRMatchArm {
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
                },
                crate::ir::types::IRMatchArm {
                    pattern: crate::ir::types::IRPattern::PWild,
                    guard: None,
                    body: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Var {
                            name: "status".to_owned(),
                            ty: status_ty.clone(),
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
    };

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove match-bearing system safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_supports_finite_quantifier_expressions() {
    let system = make_bool_param_system();
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
    let property = IRExpr::Always {
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
    };

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove finite-quantifier system safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_create_and_choose_apply() {
    let system = make_pooled_counter_system();
    let entity = make_pooled_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled create/choose safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_enum_state_forall_and_finite_step_params() {
    let system = make_pooled_ticket_system();
    let entity = make_pooled_ticket_entity();
    let status_ty = IRType::Enum {
        name: "TicketStatus".to_owned(),
        variants: vec![
            IRVariant::simple("Pending"),
            IRVariant::simple("Active"),
            IRVariant::simple("Closed"),
        ],
    };
    let property = IRExpr::Always {
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled enum/forall safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_ref_bearing_apply() {
    let system = make_pooled_ref_counter_system();
    let entity = make_pooled_ref_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled ref-bearing safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_nested_choose_ref_binding() {
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
    let entity = make_pooled_ref_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove nested-choose ref safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_forall_with_nested_choose_ref_binding() {
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
    let entity = make_pooled_ref_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove forall/nested-choose ref safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_finite_transition_args() {
    let system = make_pooled_bool_param_counter_system();
    let entity = make_pooled_bool_param_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled transition-arg safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_apply_chains_with_intermediate_args() {
    let system = make_pooled_apply_chain_system();
    let entity = make_pooled_apply_chain_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "f".to_owned(),
            domain: IRType::Entity {
                name: "F".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled apply-chain safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_create_then_choose_apply_in_one_step() {
    let system = make_pooled_create_then_inc_system();
    let entity = make_pooled_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 1, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove create-then-choose-apply safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_pooled_system_safety_supports_store_param_quantifier_membership() {
    let system = make_pooled_store_counter_system();
    let entity = make_pooled_counter_entity();
    let property = IRExpr::Always {
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
    };

    let result = try_cvc5_sygus_pooled_system_safety(&system, &entity, 2, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove store-param membership safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_crosscall_leaf_step() {
    let mut root = make_pooled_counter_system();
    root.name = "CounterRelayPool".to_owned();
    root.actions[1] = IRSystemAction {
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
    let worker = IRSystem {
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
    };
    let entity = make_pooled_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled cross-call safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_crosscall_step_args() {
    let mut root = make_pooled_bool_param_counter_system();
    root.name = "CounterArgRelayPool".to_owned();
    root.actions[1] = IRSystemAction {
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
    let worker = IRSystem {
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
    };
    let entity = make_pooled_bool_param_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled cross-call arg safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_nested_crosscall_chain() {
    let mut root = make_pooled_counter_system();
    root.name = "CounterRelayPool".to_owned();
    root.actions[1] = IRSystemAction {
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
    let worker = IRSystem {
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
    };
    let leaf = IRSystem {
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
    };
    let entity = make_pooled_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker, leaf],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled nested cross-call safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_returns_unknown_for_crosscall_cycle() {
    let mut root = make_pooled_counter_system();
    root.name = "CounterCycleRoot".to_owned();
    root.actions[1] = IRSystemAction {
        name: "relay_inc".to_owned(),
        params: vec![],
        guard: IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        body: vec![IRAction::CrossCall {
            system: "CounterCycleWorker".to_owned(),
            command: "relay_back".to_owned(),
            args: vec![],
        }],
        return_expr: None,
    };
    let worker = IRSystem {
        name: "CounterCycleWorker".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        actions: vec![IRSystemAction {
            name: "relay_back".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::CrossCall {
                system: "CounterCycleRoot".to_owned(),
                command: "relay_inc".to_owned(),
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
    let entity = make_pooled_counter_entity();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Unknown(ref msg) if msg.contains("recursive cross-call cycles")),
        "expected honest Unknown for pooled cross-call cycle, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_match_on_crosscall_result() {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Bump"), IRVariant::simple("Hold")],
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
                    scrutinee: crate::ir::types::IRActionMatchScrutinee::CrossCall {
                        system: "DecisionWorker".to_owned(),
                        command: "decide".to_owned(),
                        args: vec![],
                    },
                    arms: vec![
                        crate::ir::types::IRActionMatchArm {
                            pattern: crate::ir::types::IRPattern::PCtor {
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
                        crate::ir::types::IRActionMatchArm {
                            pattern: crate::ir::types::IRPattern::PWild,
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
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &relay,
        &[relay.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled match-crosscall safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_let_crosscall_binding() {
    let entity = make_pooled_bool_param_counter_entity();
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
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &relay,
        &[relay.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled let-crosscall safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_match_on_let_crosscall_var() {
    let decision_ty = IRType::Enum {
        name: "Decision".to_owned(),
        variants: vec![IRVariant::simple("Bump"), IRVariant::simple("Hold")],
    };
    let mut entity = make_pooled_bool_param_counter_entity();
    entity.fields.push(IRField {
        name: "decision_seed".to_owned(),
        ty: decision_ty.clone(),
        default: Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Hold".to_owned(),
            args: vec![],
            span: None,
        }),
        initial_constraint: None,
    });
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
                        scrutinee: crate::ir::types::IRActionMatchScrutinee::Var {
                            name: "decision".to_owned(),
                        },
                        arms: vec![
                            crate::ir::types::IRActionMatchArm {
                                pattern: crate::ir::types::IRPattern::PCtor {
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
                            crate::ir::types::IRActionMatchArm {
                                pattern: crate::ir::types::IRPattern::PWild,
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
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &relay,
        &[relay.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled match-var crosscall safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_callee_system_fields() {
    let entity = make_pooled_bool_param_counter_entity();
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
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled callee-field crosscall safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_supports_callee_store_params() {
    let entity = make_pooled_bool_param_counter_entity();
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
        store_params: vec![crate::ir::types::IRStoreParam {
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
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove pooled callee-store crosscall safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_system_pooled_safety_ignores_unused_proc_metadata() {
    let entity = make_pooled_bool_param_counter_entity();
    let unused_proc = crate::ir::types::IRProc {
        name: "batch".to_owned(),
        params: vec![],
        requires: None,
        nodes: vec![],
        edges: vec![],
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
        procs: vec![unused_proc.clone()],
    };
    let worker = IRSystem {
        name: "DecisionWorker".to_owned(),
        store_params: vec![crate::ir::types::IRStoreParam {
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
        procs: vec![unused_proc],
    };
    let property = IRExpr::Always {
        body: Box::new(IRExpr::Forall {
            var: "c".to_owned(),
            domain: IRType::Entity {
                name: "Counter".to_owned(),
            },
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
    };
    let slots = HashMap::from([("Counter".to_owned(), 2usize)]);

    let result = try_cvc5_sygus_multi_system_pooled_safety(
        &root,
        &[root.clone(), worker],
        &[entity],
        &slots,
        &property,
        5_000,
    );
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to ignore unused proc metadata, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_pooled_system_safety_supports_cross_entity_ref_binding() {
    let system = make_multi_pooled_system();
    let entities = make_multi_pooled_entities();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: IRType::Entity {
                    name: "Counter".to_owned(),
                },
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
            right: Box::new(IRExpr::Forall {
                var: "m".to_owned(),
                domain: IRType::Entity {
                    name: "Marker".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
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
    };
    let slots = HashMap::from([
        ("Counter".to_owned(), 2usize),
        ("Marker".to_owned(), 2usize),
    ]);

    let result =
        try_cvc5_sygus_multi_pooled_system_safety(&system, &entities, &slots, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove multi-pooled cross-entity safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_pooled_system_safety_supports_forall_cross_entity_ref_binding() {
    let mut system = make_multi_pooled_system();
    system.name = "CounterMarkerForallPool".to_owned();
    system.actions[2] = IRSystemAction {
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
    let entities = make_multi_pooled_entities();
    let property = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: IRType::Entity {
                    name: "Counter".to_owned(),
                },
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
            right: Box::new(IRExpr::Forall {
                var: "m".to_owned(),
                domain: IRType::Entity {
                    name: "Marker".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
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
    };
    let slots = HashMap::from([
        ("Counter".to_owned(), 2usize),
        ("Marker".to_owned(), 2usize),
    ]);

    let result =
        try_cvc5_sygus_multi_pooled_system_safety(&system, &entities, &slots, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove multi-pooled forall cross-entity safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_multi_pooled_system_safety_supports_cross_entity_ref_with_transition_args() {
    let mut system = make_multi_pooled_system();
    system.actions[2].body = vec![IRAction::Choose {
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
    }];
    let mut entities = make_multi_pooled_entities();
    let counter = entities
        .iter_mut()
        .find(|entity| entity.name == "Counter")
        .expect("counter entity");
    counter.transitions[0].params = vec![IRTransParam {
        name: "copy".to_owned(),
        ty: IRType::Bool,
    }];
    counter.transitions[0].updates[0].value = IRExpr::IfElse {
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
    let property = IRExpr::Always {
        body: Box::new(IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(IRExpr::Forall {
                var: "c".to_owned(),
                domain: IRType::Entity {
                    name: "Counter".to_owned(),
                },
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
            right: Box::new(IRExpr::Forall {
                var: "m".to_owned(),
                domain: IRType::Entity {
                    name: "Marker".to_owned(),
                },
                body: Box::new(IRExpr::BinOp {
                    op: "OpGe".to_owned(),
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
    };
    let slots = HashMap::from([
        ("Counter".to_owned(), 2usize),
        ("Marker".to_owned(), 2usize),
    ]);

    let result =
        try_cvc5_sygus_multi_pooled_system_safety(&system, &entities, &slots, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Proved),
        "expected cvc5 SyGuS to prove multi-pooled cross-entity ref+arg safety, got: {result:?}"
    );
}

#[test]
#[ignore = "in-process cvc5 SyGuS has no hard cancellation; run with ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 when isolating this test"]
fn cvc5_sygus_system_safety_returns_unknown_for_int_step_params() {
    let mut system = make_counter_system();
    system.actions[0].params.push(IRTransParam {
        name: "delta".to_owned(),
        ty: IRType::Int,
    });
    let property = non_negative_property();

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref msg) if msg.contains("only supports finite Bool/enum action params")),
        "expected honest Unknown for unsupported int step params, got: {result:?}"
    );
}
