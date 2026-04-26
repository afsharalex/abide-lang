use super::*;
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
