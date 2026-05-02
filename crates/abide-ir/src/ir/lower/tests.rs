use super::*;
use crate::ir::relation::{IRRelationExpr, IRRelationSource, IRRelationType};
use crate::span::Span;

#[test]
fn lower_expr_propagates_span() {
    let sp = Span { start: 10, end: 20 };
    let expr = E::EExpr::Lit(
        E::Ty::Builtin(E::BuiltinTy::Int),
        E::Literal::Int(42),
        Some(sp),
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_expr(&expr, &ctx);
    match ir {
        IRExpr::Lit { span, .. } => assert_eq!(span, Some(sp)),
        other => panic!("expected Lit, got {other:?}"),
    }
}

#[test]
fn lower_expr_propagates_none_span() {
    let expr = E::EExpr::Lit(
        E::Ty::Builtin(E::BuiltinTy::Bool),
        E::Literal::Bool(true),
        None,
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_expr(&expr, &ctx);
    match ir {
        IRExpr::Lit { span, .. } => assert_eq!(span, None),
        other => panic!("expected Lit, got {other:?}"),
    }
}

#[test]
fn lower_expr_binop_propagates_span() {
    let sp = Span { start: 5, end: 15 };
    let a = E::EExpr::Lit(E::Ty::Builtin(E::BuiltinTy::Int), E::Literal::Int(1), None);
    let b = E::EExpr::Lit(E::Ty::Builtin(E::BuiltinTy::Int), E::Literal::Int(2), None);
    let expr = E::EExpr::BinOp(
        E::Ty::Builtin(E::BuiltinTy::Int),
        E::BinOp::Add,
        Box::new(a),
        Box::new(b),
        Some(sp),
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_expr(&expr, &ctx);
    match ir {
        IRExpr::BinOp { span, .. } => assert_eq!(span, Some(sp)),
        other => panic!("expected BinOp, got {other:?}"),
    }
}

#[test]
fn lower_relation_join_uses_relation_ir() {
    let relation_ty =
        |left: E::Ty, right: E::Ty| E::Ty::Set(Box::new(E::Ty::Tuple(vec![left, right])));
    let customer_ty = E::Ty::Entity("Customer".to_owned());
    let order_customer = E::EExpr::Var(
        relation_ty(E::Ty::Entity("Order".to_owned()), customer_ty.clone()),
        "order_customer".to_owned(),
        None,
    );
    let customer_segment = E::EExpr::Var(
        relation_ty(customer_ty, E::Ty::Builtin(E::BuiltinTy::String)),
        "customer_segment".to_owned(),
        None,
    );
    let expr = E::EExpr::QualCall(
        relation_ty(
            E::Ty::Entity("Order".to_owned()),
            E::Ty::Builtin(E::BuiltinTy::String),
        ),
        "Rel".to_owned(),
        "join".to_owned(),
        vec![order_customer, customer_segment],
        None,
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let lowered = lower_relation_expr(&expr, &ctx).expect("relation join should lower");

    assert!(matches!(lowered, IRRelationExpr::Join(_, _)));
    assert_eq!(
        lowered.relation_type().expect("join type"),
        IRRelationType::binary(
            IRType::Entity {
                name: "Order".to_owned()
            },
            IRType::String
        )
    );
    let IRRelationExpr::Join(left, right) = lowered else {
        unreachable!("asserted above")
    };
    let IRRelationExpr::Symbol(left_symbol) = left.as_ref() else {
        panic!("left side should lower to a relation symbol")
    };
    assert_eq!(
        left_symbol.source,
        IRRelationSource::UserRelation {
            name: "order_customer".to_owned()
        }
    );
    let IRRelationExpr::Symbol(right_symbol) = right.as_ref() else {
        panic!("right side should lower to a relation symbol")
    };
    assert_eq!(
        right_symbol.source,
        IRRelationSource::UserRelation {
            name: "customer_segment".to_owned()
        }
    );
}

#[test]
fn lower_relation_project_uses_literal_columns() {
    let tuple_set_ty = E::Ty::Set(Box::new(E::Ty::Tuple(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Entity("Customer".to_owned()),
        E::Ty::Builtin(E::BuiltinTy::String),
    ])));
    let projected_ty = E::Ty::Set(Box::new(E::Ty::Tuple(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Builtin(E::BuiltinTy::String),
    ])));
    let expr = E::EExpr::QualCall(
        projected_ty,
        "Rel".to_owned(),
        "project".to_owned(),
        vec![
            E::EExpr::Var(tuple_set_ty, "order_customer_segment".to_owned(), None),
            E::EExpr::Lit(E::Ty::Builtin(E::BuiltinTy::Int), E::Literal::Int(0), None),
            E::EExpr::Lit(E::Ty::Builtin(E::BuiltinTy::Int), E::Literal::Int(2), None),
        ],
        None,
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let lowered = lower_relation_expr(&expr, &ctx).expect("relation project should lower");

    assert!(matches!(lowered, IRRelationExpr::Project { .. }));
    assert_eq!(
        lowered.relation_type().expect("project type"),
        IRRelationType::binary(
            IRType::Entity {
                name: "Order".to_owned()
            },
            IRType::String
        )
    );
    let IRRelationExpr::Project { columns, .. } = lowered else {
        unreachable!("asserted above")
    };
    assert_eq!(columns, vec![0, 2]);
}

#[test]
fn lower_relation_derived_operators_use_relation_ir() {
    let unary_ty = |name: &str| E::Ty::Set(Box::new(E::Ty::Entity(name.to_owned())));
    let binary_ty = |left: &str, right: &str| {
        E::Ty::Set(Box::new(E::Ty::Tuple(vec![
            E::Ty::Entity(left.to_owned()),
            E::Ty::Entity(right.to_owned()),
        ])))
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let product = E::EExpr::QualCall(
        binary_ty("Order", "Customer"),
        "Rel".to_owned(),
        "product".to_owned(),
        vec![
            E::EExpr::Var(unary_ty("Order"), "orders".to_owned(), None),
            E::EExpr::Var(unary_ty("Customer"), "customers".to_owned(), None),
        ],
        None,
    );
    assert!(matches!(
        lower_relation_expr(&product, &ctx).expect("product should lower"),
        IRRelationExpr::Product(_, _)
    ));

    let transpose = E::EExpr::QualCall(
        binary_ty("Customer", "Order"),
        "Rel".to_owned(),
        "transpose".to_owned(),
        vec![E::EExpr::Var(
            binary_ty("Order", "Customer"),
            "order_customer".to_owned(),
            None,
        )],
        None,
    );
    assert!(matches!(
        lower_relation_expr(&transpose, &ctx).expect("transpose should lower"),
        IRRelationExpr::Transpose(_)
    ));

    let edge = E::EExpr::Var(binary_ty("Node", "Node"), "edge".to_owned(), None);
    let closure = E::EExpr::QualCall(
        binary_ty("Node", "Node"),
        "Rel".to_owned(),
        "closure".to_owned(),
        vec![edge.clone()],
        None,
    );
    assert!(matches!(
        lower_relation_expr(&closure, &ctx).expect("closure should lower"),
        IRRelationExpr::TransitiveClosure(_)
    ));

    let reach = E::EExpr::QualCall(
        binary_ty("Node", "Node"),
        "Rel".to_owned(),
        "reach".to_owned(),
        vec![edge],
        None,
    );
    assert!(matches!(
        lower_relation_expr(&reach, &ctx).expect("reach should lower"),
        IRRelationExpr::ReflexiveTransitiveClosure(_)
    ));
}

#[test]
fn lower_relation_set_operators_use_relation_ir() {
    let rel_ty = E::Ty::Set(Box::new(E::Ty::Tuple(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Entity("Customer".to_owned()),
    ])));
    let lhs = E::EExpr::Var(rel_ty.clone(), "lhs".to_owned(), None);
    let rhs = E::EExpr::Var(rel_ty.clone(), "rhs".to_owned(), None);
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let union = E::EExpr::BinOp(
        rel_ty.clone(),
        E::BinOp::Add,
        Box::new(lhs.clone()),
        Box::new(rhs.clone()),
        None,
    );
    assert!(matches!(
        lower_relation_expr(&union, &ctx).expect("union should lower"),
        IRRelationExpr::Union(_, _)
    ));

    let intersection = E::EExpr::BinOp(
        rel_ty.clone(),
        E::BinOp::Mul,
        Box::new(lhs.clone()),
        Box::new(rhs.clone()),
        None,
    );
    assert!(matches!(
        lower_relation_expr(&intersection, &ctx).expect("intersection should lower"),
        IRRelationExpr::Intersection(_, _)
    ));

    let difference = E::EExpr::BinOp(rel_ty, E::BinOp::Sub, Box::new(lhs), Box::new(rhs), None);
    assert!(matches!(
        lower_relation_expr(&difference, &ctx).expect("difference should lower"),
        IRRelationExpr::Difference(_, _)
    ));
}

#[test]
fn lower_relation_tuple_set_literals_use_relation_ir() {
    let rel_ty = E::Ty::Set(Box::new(E::Ty::Tuple(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Entity("Customer".to_owned()),
    ])));
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let empty = E::EExpr::SetLit(rel_ty.clone(), vec![], None);
    assert!(matches!(
        lower_relation_expr(&empty, &ctx).expect("empty relation should lower"),
        IRRelationExpr::Empty(_)
    ));

    let tuple = E::EExpr::TupleLit(
        E::Ty::Tuple(vec![
            E::Ty::Entity("Order".to_owned()),
            E::Ty::Entity("Customer".to_owned()),
        ]),
        vec![
            E::EExpr::Var(E::Ty::Entity("Order".to_owned()), "order".to_owned(), None),
            E::EExpr::Var(
                E::Ty::Entity("Customer".to_owned()),
                "customer".to_owned(),
                None,
            ),
        ],
        None,
    );
    let singleton = E::EExpr::SetLit(rel_ty, vec![tuple], None);
    assert!(matches!(
        lower_relation_expr(&singleton, &ctx).expect("singleton relation should lower"),
        IRRelationExpr::SingletonTuple { .. }
    ));
}

#[test]
fn lower_relation_type_literal_preserves_nary_columns() {
    let rel_ty = E::Ty::Relation(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Entity("Customer".to_owned()),
        E::Ty::Builtin(E::BuiltinTy::String),
    ]);
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let empty = E::EExpr::SetLit(rel_ty, vec![], None);
    let lowered = lower_relation_expr(&empty, &ctx).expect("empty relation should lower");

    assert_eq!(lowered.relation_type().expect("relation type").arity(), 3);
}

#[test]
fn lower_relation_field_uses_store_scoped_relation_symbol() {
    let result_ty = E::Ty::Relation(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Enum("Status".to_owned(), vec!["Pending".to_owned()]),
    ]);
    let expr = E::EExpr::QualCall(
        result_ty,
        "Rel".to_owned(),
        "field".to_owned(),
        vec![
            E::EExpr::Var(E::Ty::Store("Order".to_owned()), "orders".to_owned(), None),
            E::EExpr::Qual(
                E::Ty::Named("Order".to_owned()),
                "Order".to_owned(),
                "status".to_owned(),
                None,
            ),
        ],
        None,
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let lowered = lower_relation_expr(&expr, &ctx).expect("field relation should lower");

    let IRRelationExpr::Symbol(symbol) = lowered else {
        panic!("expected relation symbol");
    };
    assert_eq!(symbol.name, "orders.status");
    assert_eq!(
        symbol.source,
        IRRelationSource::EntityField {
            entity: "Order".to_owned(),
            field: "status".to_owned()
        }
    );
    assert_eq!(symbol.relation_type.arity(), 2);
}

#[test]
fn lower_verify_propagates_span_and_file() {
    let sp = Span {
        start: 100,
        end: 200,
    };
    let ev = E::EVerify {
        name: "test".to_owned(),
        depth: None,
        stores: vec![E::EStoreDecl {
            name: "es".to_owned(),
            entity_type: "E".to_owned(),
            lo: 0,
            hi: 10,
        }],
        proc_bounds: vec![],
        let_bindings: vec![E::ELetBinding {
            name: "sys".to_owned(),
            system_type: "Sys".to_owned(),
            store_bindings: vec![("es".to_owned(), "es".to_owned())],
        }],
        assume_block: None,
        assumption_set: E::AssumptionSet::default_for_verify(),
        asserts: vec![E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        )],
        span: Some(sp),
        file: Some("/test.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_verify(&ev, &std::collections::HashMap::new(), &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/test.ab"));
}

#[test]
fn lower_theorem_propagates_span_and_file() {
    let sp = Span { start: 50, end: 80 };
    let et = E::ETheorem {
        name: "thm".to_owned(),
        targets: vec!["Sys".to_owned()],
        assume_block: None,
        enclosing_under_idx: None,
        assumption_set: E::AssumptionSet::default_for_theorem_or_lemma(),
        invariants: vec![],
        shows: vec![E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        )],
        by_file: Some("proofs/thm.agda".to_owned()),
        by_lemmas: vec![],
        span: Some(sp),
        file: Some("/proof.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_theorem(&et, &std::collections::HashMap::new(), &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/proof.ab"));
    assert_eq!(ir.by_file.as_deref(), Some("proofs/thm.agda"));
}

#[test]
fn lower_scene_propagates_span_and_file() {
    let sp = Span { start: 30, end: 60 };
    let es = E::EScene {
        name: "sc".to_owned(),
        stores: vec![],
        let_bindings: vec![E::ELetBinding {
            name: "sys".to_owned(),
            system_type: "Sys".to_owned(),
            store_bindings: vec![],
        }],
        givens: vec![],
        whens: vec![],
        thens: vec![],
        given_constraints: vec![],
        activations: vec![],
        span: Some(sp),
        file: Some("/scene.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_scene(&es, &std::collections::HashMap::new(), &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/scene.ab"));
}

#[test]
fn lower_scene_action_stays_operational_not_app() {
    let es = E::EScene {
        name: "sc".to_owned(),
        stores: vec![],
        let_bindings: vec![E::ELetBinding {
            name: "auth".to_owned(),
            system_type: "Auth".to_owned(),
            store_bindings: vec![],
        }],
        givens: vec![],
        whens: vec![E::ESceneWhen::Action {
            var: "login_failed".to_owned(),
            system: "Auth".to_owned(),
            event: "login_failed".to_owned(),
            args: vec![E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Int),
                E::Literal::Int(5),
                None,
            )],
            card: Some("one".to_owned()),
        }],
        thens: vec![],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_scene(&es, &std::collections::HashMap::new(), &ctx);
    assert_eq!(ir.events.len(), 1);
    assert_eq!(ir.events[0].system, "Auth");
    assert_eq!(ir.events[0].event, "login_failed");
    assert_eq!(ir.events[0].args.len(), 1);
    assert!(
        !matches!(ir.events[0].args[0], IRExpr::App { .. }),
        "scene event occurrence should lower to IRSceneEvent metadata, not App"
    );
}

#[test]
fn lower_axiom_propagates_span_and_file() {
    let sp = Span { start: 0, end: 25 };
    let ea = E::EAxiom {
        name: "ax".to_owned(),
        body: E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        ),
        by_file: Some("proofs/ax.agda".to_owned()),
        span: Some(sp),
        file: Some("/ax.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_axiom(&ea, &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/ax.ab"));
    assert_eq!(ir.by_file.as_deref(), Some("proofs/ax.agda"));
}

#[test]
fn lower_fn_propagates_file() {
    let sp = Span { start: 10, end: 40 };
    let ef = E::EFn {
        name: "f".to_owned(),
        params: vec![("x".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
        ret_ty: E::Ty::Builtin(E::BuiltinTy::Int),
        contracts: vec![],
        body: E::EExpr::Var(E::Ty::Builtin(E::BuiltinTy::Int), "x".to_owned(), None),
        span: Some(sp),
        file: Some("/fn.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_fn(&ef, &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/fn.ab"));
}

#[test]
fn lower_pred_propagates_file() {
    let sp = Span { start: 20, end: 50 };
    let ep = E::EPred {
        name: "p".to_owned(),
        params: vec![("x".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
        body: E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        ),
        span: Some(sp),
        file: Some("/pred.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_pred(&ep, &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/pred.ab"));
}

#[test]
fn lower_prop_propagates_file() {
    let sp = Span { start: 30, end: 70 };
    let ep = E::EProp {
        name: "safe".to_owned(),
        target: Some("Sys".to_owned()),
        body: E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        ),
        span: Some(sp),
        file: Some("/prop.ab".to_owned()),
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_prop(&ep, &ctx);
    assert_eq!(ir.span, Some(sp));
    assert_eq!(ir.file.as_deref(), Some("/prop.ab"));
}
