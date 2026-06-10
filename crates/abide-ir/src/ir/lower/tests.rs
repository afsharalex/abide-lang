use super::relation_expr::lower_relation_expr;
use super::*;
use crate::ir::relation::{IRRelationExpr, IRRelationSource, IRRelationType};
use crate::ir::types::{IRAction, IRPattern};
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
fn lower_expr_distinguishes_enum_constructors_from_enum_typed_variables() {
    let status_ty = E::Ty::Enum(
        "Status".to_owned(),
        vec!["Open".to_owned(), "Closed".to_owned()],
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let ctor = lower_expr(
        &E::EExpr::Var(status_ty.clone(), "Open".to_owned(), None),
        &ctx,
    );
    assert!(matches!(
        ctor,
        IRExpr::Ctor {
            enum_name,
            ctor,
            ..
        } if enum_name == "Status" && ctor == "Open"
    ));

    let var = lower_expr(
        &E::EExpr::Var(status_ty.clone(), "current".to_owned(), None),
        &ctx,
    );
    assert!(matches!(
        var,
        IRExpr::Var { name, ty, .. }
            if name == "current"
                && matches!(ty, IRType::Enum { ref name, .. } if name == "Status")
    ));

    let qualified_ctor = lower_expr(
        &E::EExpr::Qual(
            status_ty.clone(),
            "Status".to_owned(),
            "Closed".to_owned(),
            None,
        ),
        &ctx,
    );
    assert!(matches!(
        qualified_ctor,
        IRExpr::Ctor {
            enum_name,
            ctor,
            ..
        } if enum_name == "Status" && ctor == "Closed"
    ));

    let qualified_enum_var = lower_expr(
        &E::EExpr::Qual(status_ty, "Status".to_owned(), "current".to_owned(), None),
        &ctx,
    );
    assert!(matches!(
        qualified_enum_var,
        IRExpr::Var { name, ty, .. }
            if name == "Status::current"
                && matches!(ty, IRType::Enum { ref name, .. } if name == "Status")
    ));

    let qualified_field = lower_expr(
        &E::EExpr::Qual(
            E::Ty::Builtin(E::BuiltinTy::Int),
            "Order".to_owned(),
            "total".to_owned(),
            None,
        ),
        &ctx,
    );
    assert!(matches!(
        qualified_field,
        IRExpr::Var { name, ty, .. } if name == "Order::total" && ty == IRType::Int
    ));
}

#[test]
fn lower_ty_treats_resolved_named_enum_as_enum_reference() {
    let expr_variants = vec![
        E::EVariant::Record(
            "Lit".to_owned(),
            vec![("value".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
        ),
        E::EVariant::Record(
            "Neg".to_owned(),
            vec![("inner".to_owned(), E::Ty::Named("Expr".to_owned()))],
        ),
    ];
    let mut variants = VariantInfo::new();
    variants.insert("Expr".to_owned(), expr_variants.as_slice());
    let ctx = LowerCtx::new(&variants, std::collections::HashSet::new());

    let lowered = lower_ty(&E::Ty::Named("Expr".to_owned()), &ctx);

    let IRType::Enum { name, variants } = lowered else {
        panic!("resolved named enum should lower to an enum reference");
    };
    assert_eq!(name, "Expr");
    assert_eq!(variants.len(), 2);
    assert!(
        variants.iter().all(|variant| variant.fields.is_empty()),
        "enum references should be shallow to avoid recursive type expansion"
    );
    assert!(
        !ctx.diagnostics.borrow().has_errors(),
        "resolved named enum references should not emit lower diagnostics"
    );
}

#[test]
fn lower_proc_and_query_preserve_parameter_refinement_predicates() {
    let refinement_ty = positive_int_refinement_ty();
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let proc = E::EProc {
        name: "fulfill".to_owned(),
        params: vec![("amount".to_owned(), refinement_ty.clone())],
        requires: None,
        nodes: vec![],
        edges: vec![],
        proc_uses: vec![],
        span: None,
    };
    let lowered_proc = super::system::lower_proc(&proc, &ctx);

    assert_eq!(lowered_proc.params[0].ty, IRType::Int);
    assert!(
        matches!(
            lowered_proc.requires,
            Some(IRExpr::BinOp { ref op, ref left, .. })
                if op == "OpGt"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "amount")
        ),
        "proc parameter refinement should lower into requires guard: {:?}",
        lowered_proc.requires
    );

    let query = E::EQuery {
        name: "positive".to_owned(),
        params: vec![("amount".to_owned(), refinement_ty)],
        body: E::EExpr::Lit(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::Literal::Bool(true),
            None,
        ),
        span: None,
    };
    let lowered_query = super::system::lower_query(&query, &ctx);

    assert_eq!(lowered_query.params[0].ty, IRType::Int);
    assert!(
        matches!(
            lowered_query.requires.as_slice(),
            [IRExpr::BinOp { op, left, .. }]
                if op == "OpGt"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "amount")
        ),
        "query parameter refinement should lower into query preconditions: {:?}",
        lowered_query.requires
    );
}

#[test]
fn lower_interface_strips_refinement_types_from_signature_params() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let interface = E::EInterface {
        name: "Gateway".to_owned(),
        commands: vec![E::ECommand {
            name: "authorize".to_owned(),
            params: vec![("amount".to_owned(), positive_int_refinement_ty())],
            return_type: Some(E::Ty::Builtin(E::BuiltinTy::Bool)),
            span: None,
        }],
        queries: vec![E::EQuerySig {
            name: "remaining".to_owned(),
            params: vec![("amount".to_owned(), positive_int_refinement_ty())],
            return_type: E::Ty::Builtin(E::BuiltinTy::Int),
            span: None,
        }],
        span: None,
    };

    let aliases = std::collections::HashMap::new();
    let er = empty_elab_result();
    let lowered = lower_interface(&interface, &er, &aliases, &ctx);

    assert_eq!(lowered.commands[0].params[0].ty, IRType::Int);
    assert_eq!(lowered.queries[0].params[0].ty, IRType::Int);
    assert!(
        !ctx.diagnostics.borrow().has_errors(),
        "interface refinement parameter stripping should not emit lower diagnostics"
    );
}

#[test]
fn lower_fn_preserves_contracts_decreases_and_refinement_requires() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ef = E::EFn {
        name: "discount".to_owned(),
        params: vec![("amount".to_owned(), positive_int_refinement_ty())],
        ret_ty: E::Ty::Builtin(E::BuiltinTy::Int),
        contracts: vec![
            E::EContract::Requires(gt_int_var("amount", 1)),
            E::EContract::Ensures(ge_int_var("result", 0)),
            E::EContract::Decreases {
                measures: vec![int_var("amount")],
                star: false,
            },
        ],
        body: int_var("amount"),
        span: None,
        file: None,
    };

    let lowered = lower_fn(&ef, &ctx);

    assert!(
        matches!(
            lowered.ty,
            IRType::Fn { ref param, ref result }
                if param.as_ref() == &IRType::Int && result.as_ref() == &IRType::Int
        ),
        "refined fn parameter should be stripped in fn type: {:?}",
        lowered.ty
    );
    assert!(
        matches!(
            lowered.body,
            IRExpr::Lam { ref param_type, .. } if param_type == &IRType::Int
        ),
        "refined fn parameter should be stripped in lambda body: {:?}",
        lowered.body
    );
    assert_eq!(lowered.requires.len(), 2);
    assert!(
        matches!(
            &lowered.requires[0],
            IRExpr::BinOp { op, left, .. }
                if op == "OpGt"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "amount")
        ),
        "refinement-derived requires should be prepended: {:?}",
        lowered.requires
    );
    assert!(
        matches!(
            &lowered.requires[1],
            IRExpr::BinOp { op, left, .. }
                if op == "OpGt"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "amount")
        ),
        "explicit requires should be preserved after refinement requires: {:?}",
        lowered.requires
    );
    assert!(
        matches!(
            lowered.ensures.as_slice(),
            [IRExpr::BinOp { op, left, .. }]
                if op == "OpGe"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "result")
        ),
        "ensures should be lowered: {:?}",
        lowered.ensures
    );
    let decreases = lowered.decreases.expect("decreases should lower");
    assert!(!decreases.star);
    assert_eq!(decreases.measures.len(), 1);
    assert!(matches!(
        &decreases.measures[0],
        IRExpr::Var { name, .. } if name == "amount"
    ));
}

#[test]
fn lower_while_preserves_invariants_and_decreases() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let while_expr = E::EExpr::While(
        Box::new(gt_int_var("amount", 0)),
        vec![
            E::EContract::Invariant(ge_int_var("amount", 0)),
            E::EContract::Decreases {
                measures: vec![int_var("amount")],
                star: true,
            },
        ],
        Box::new(E::EExpr::Block(vec![int_var("amount")], None)),
        None,
    );

    let lowered = lower_expr(&while_expr, &ctx);

    let IRExpr::While {
        invariants,
        decreases,
        ..
    } = lowered
    else {
        panic!("expected while expression to lower to IR while");
    };
    assert!(
        matches!(
            invariants.as_slice(),
            [IRExpr::BinOp { op, left, .. }]
                if op == "OpGe"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "amount")
        ),
        "while invariant should be lowered: {invariants:?}"
    );
    let decreases = decreases.expect("while decreases should lower");
    assert!(decreases.star);
    assert_eq!(decreases.measures.len(), 1);
    assert!(matches!(
        &decreases.measures[0],
        IRExpr::Var { name, .. } if name == "amount"
    ));
}

#[test]
fn lower_action_strips_refinement_params_and_adds_guard() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let action = E::EAction {
        name: "charge".to_owned(),
        refs: vec![],
        params: vec![("amount".to_owned(), positive_int_refinement_ty())],
        requires: vec![],
        ensures: vec![],
        body: vec![],
        span: None,
    };

    let lowered = lower_action(&action, &ctx);

    assert_eq!(lowered.params[0].ty, IRType::Int);
    assert!(
        matches!(
            lowered.guard,
            IRExpr::BinOp { ref op, ref left, .. }
                if op == "OpGt"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "amount")
        ),
        "action refinement predicate should lower into guard: {:?}",
        lowered.guard
    );
}

fn positive_int_refinement_ty() -> E::Ty {
    E::Ty::Refinement(
        Box::new(E::Ty::Builtin(E::BuiltinTy::Int)),
        Box::new(E::EExpr::BinOp(
            E::Ty::Builtin(E::BuiltinTy::Bool),
            E::BinOp::Gt,
            Box::new(E::EExpr::Var(
                E::Ty::Builtin(E::BuiltinTy::Int),
                "$".to_owned(),
                None,
            )),
            Box::new(E::EExpr::Lit(
                E::Ty::Builtin(E::BuiltinTy::Int),
                E::Literal::Int(0),
                None,
            )),
            None,
        )),
    )
}

fn int_var(name: &str) -> E::EExpr {
    E::EExpr::Var(E::Ty::Builtin(E::BuiltinTy::Int), name.to_owned(), None)
}

fn int_lit(value: i64) -> E::EExpr {
    E::EExpr::Lit(
        E::Ty::Builtin(E::BuiltinTy::Int),
        E::Literal::Int(value),
        None,
    )
}

fn gt_int_var(name: &str, value: i64) -> E::EExpr {
    E::EExpr::BinOp(
        E::Ty::Builtin(E::BuiltinTy::Bool),
        E::BinOp::Gt,
        Box::new(int_var(name)),
        Box::new(int_lit(value)),
        None,
    )
}

fn ge_int_var(name: &str, value: i64) -> E::EExpr {
    E::EExpr::BinOp(
        E::Ty::Builtin(E::BuiltinTy::Bool),
        E::BinOp::Ge,
        Box::new(int_var(name)),
        Box::new(int_lit(value)),
        None,
    )
}

fn bool_var(name: &str) -> E::EExpr {
    E::EExpr::Var(E::Ty::Builtin(E::BuiltinTy::Bool), name.to_owned(), None)
}

fn bool_lit(value: bool) -> E::EExpr {
    E::EExpr::Lit(
        E::Ty::Builtin(E::BuiltinTy::Bool),
        E::Literal::Bool(value),
        None,
    )
}

fn empty_system(name: &str) -> E::ESystem {
    E::ESystem {
        name: name.to_owned(),
        implements: None,
        deps: vec![],
        fields: vec![],
        store_params: vec![],
        scopes: vec![],
        commands: vec![],
        actions: vec![],
        queries: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
        proc_uses: vec![],
        span: None,
    }
}

#[test]
fn lower_system_preserves_composed_entities_and_scoped_names() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let aliases = std::collections::HashMap::new();
    let mut inventory = empty_system("Inventory");
    inventory.store_params = vec![E::EStoreParam {
        name: "products".to_owned(),
        entity_type: "Product".to_owned(),
        lo: Some(0),
        hi: Some(10),
    }];
    let mut billing = empty_system("Billing");
    billing.store_params = vec![E::EStoreParam {
        name: "orders".to_owned(),
        entity_type: "Order".to_owned(),
        lo: Some(0),
        hi: Some(10),
    }];
    let mut storefront = empty_system("Storefront");
    storefront.store_params = vec![E::EStoreParam {
        name: "carts".to_owned(),
        entity_type: "Cart".to_owned(),
        lo: Some(0),
        hi: Some(10),
    }];
    storefront.let_bindings = vec![
        E::ELetBinding {
            name: "inventory".to_owned(),
            system_type: "Inventory".to_owned(),
            store_bindings: vec![("products".to_owned(), "products".to_owned())],
        },
        E::ELetBinding {
            name: "inventory_read_model".to_owned(),
            system_type: "Inventory".to_owned(),
            store_bindings: vec![("products".to_owned(), "products".to_owned())],
        },
        E::ELetBinding {
            name: "billing".to_owned(),
            system_type: "Billing".to_owned(),
            store_bindings: vec![("orders".to_owned(), "orders".to_owned())],
        },
    ];
    storefront.commands = vec![E::ECommand {
        name: "checkout".to_owned(),
        params: vec![("amount".to_owned(), positive_int_refinement_ty())],
        return_type: Some(E::Ty::Builtin(E::BuiltinTy::Bool)),
        span: None,
    }];
    storefront.actions = vec![E::ESystemAction {
        name: "checkout".to_owned(),
        params: vec![("amount".to_owned(), positive_int_refinement_ty())],
        requires: vec![bool_var("can_ship")],
        body: vec![E::EEventAction::Expr(bool_var("internal_ok"))],
        return_expr: Some(bool_var("can_ship")),
        span: None,
    }];
    storefront.queries = vec![E::EQuery {
        name: "can_ship".to_owned(),
        params: vec![],
        body: bool_var("internal_ok"),
        span: None,
    }];
    storefront.preds = vec![E::EPred {
        name: "internal_ok".to_owned(),
        params: vec![],
        body: bool_var("can_ship"),
        span: None,
        file: None,
    }];
    storefront.derived_fields = vec![E::EDerived {
        name: "eligible".to_owned(),
        body: bool_var("can_ship"),
        ty: E::Ty::Builtin(E::BuiltinTy::Bool),
        span: None,
    }];
    storefront.invariants = vec![E::EInvariant {
        name: "safe".to_owned(),
        body: bool_var("can_ship"),
        span: None,
    }];
    let all_systems = vec![inventory, billing, storefront.clone()];

    let lowered = super::system::lower_system(&storefront, &all_systems, &aliases, &ctx);

    assert_eq!(lowered.store_params.len(), 1);
    assert_eq!(
        lowered.entities,
        vec!["Cart".to_owned(), "Product".to_owned(), "Order".to_owned()],
        "composed system entity types should be included without duplicate entries"
    );
    assert_eq!(lowered.commands[0].params[0].ty, IRType::Int);
    assert_eq!(lowered.actions[0].params[0].ty, IRType::Int);
    assert!(
        matches!(
            &lowered.actions[0].guard,
            IRExpr::BinOp { op, left, right, .. }
                if op == "OpAnd"
                    && matches!(left.as_ref(), IRExpr::BinOp { op, .. } if op == "OpGt")
                    && matches!(right.as_ref(), IRExpr::Var { name, .. } if name == "Storefront::can_ship")
        ),
        "action guard should combine refinement requires with qualified local query names: {:?}",
        lowered.actions[0].guard
    );
    assert!(
        matches!(
            lowered.actions[0].body.as_slice(),
            [IRAction::ExprStmt { expr: IRExpr::Var { name, .. } }]
                if name == "Storefront::internal_ok"
        ),
        "action bodies should qualify local pred/query references: {:?}",
        lowered.actions[0].body
    );
    assert!(
        matches!(
            lowered.actions[0].return_expr.as_ref(),
            Some(IRExpr::Var { name, .. }) if name == "Storefront::can_ship"
        ),
        "return expressions should qualify local pred/query references: {:?}",
        lowered.actions[0].return_expr
    );
    assert!(matches!(
        &lowered.derived_fields[0].body,
        IRExpr::Var { name, .. } if name == "Storefront::can_ship"
    ));
    assert!(matches!(
        &lowered.invariants[0].body,
        IRExpr::Var { name, .. } if name == "Storefront::can_ship"
    ));
    assert!(matches!(
        &lowered.preds[0].body,
        IRExpr::Var { name, .. } if name == "Storefront::can_ship"
    ));
    assert!(matches!(
        &lowered.queries[0].body,
        IRExpr::Var { name, .. } if name == "Storefront::internal_ok"
    ));
}

#[test]
fn lower_extern_preserves_may_params_and_local_fairness_assumptions() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ext = E::EExtern {
        name: "Gateway".to_owned(),
        implements: None,
        commands: vec![
            E::ECommand {
                name: "authorize".to_owned(),
                params: vec![("amount".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
                return_type: Some(E::Ty::Builtin(E::BuiltinTy::Bool)),
                span: None,
            },
            E::ECommand {
                name: "settle".to_owned(),
                params: vec![],
                return_type: None,
                span: None,
            },
        ],
        mays: vec![E::EMay {
            command: "authorize".to_owned(),
            returns: vec![bool_lit(true)],
            span: None,
        }],
        assumes: vec![
            E::EExternAssume::Fair(vec!["authorize".to_owned()], None),
            E::EExternAssume::StrongFair(vec!["settle".to_owned()], None),
            E::EExternAssume::Expr(bool_var("provider_ready"), None),
        ],
        span: None,
    };

    let lowered = super::system::lower_extern(&ext, &ctx);

    assert_eq!(lowered.commands.len(), 2);
    assert_eq!(lowered.actions.len(), 1);
    assert_eq!(lowered.actions[0].params.len(), 1);
    assert_eq!(lowered.actions[0].params[0].name, "amount");
    assert_eq!(lowered.actions[0].params[0].ty, IRType::Int);
    let pred_names: Vec<_> = lowered
        .preds
        .iter()
        .map(|pred| pred.name.as_str())
        .collect();
    assert!(
        pred_names.contains(&"__abide_extern_assume_wf__authorize"),
        "weak fairness assumption should lower to hidden local predicate: {pred_names:?}"
    );
    assert!(
        pred_names.contains(&"__abide_extern_assume_sf__settle"),
        "strong fairness assumption should lower to hidden local predicate: {pred_names:?}"
    );
    assert!(
        pred_names.contains(&"__abide_extern_assume_expr__3"),
        "expression assumption should lower to hidden local predicate: {pred_names:?}"
    );
}

#[test]
fn lower_program_proc_synthesizes_refined_params_and_outcome_actions() {
    let mut variants = VariantInfo::new();
    let payment_variants = vec![
        E::EVariant::Simple("ok".to_owned()),
        E::EVariant::Simple("fail".to_owned()),
    ];
    variants.insert("PaymentResult".to_owned(), payment_variants.as_slice());
    let ctx = LowerCtx::new(&variants, std::collections::HashSet::new());
    let aliases = std::collections::HashMap::new();
    let mut gateway = empty_system("Gateway");
    gateway.commands = vec![E::ECommand {
        name: "authorize".to_owned(),
        params: vec![("amount".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
        return_type: Some(E::Ty::Enum(
            "PaymentResult".to_owned(),
            vec!["ok".to_owned(), "fail".to_owned()],
        )),
        span: None,
    }];
    let mut program = empty_system("CheckoutProgram");
    program.let_bindings = vec![E::ELetBinding {
        name: "gateway".to_owned(),
        system_type: "Gateway".to_owned(),
        store_bindings: vec![],
    }];
    program.procs = vec![E::EProc {
        name: "checkout".to_owned(),
        params: vec![("amount".to_owned(), positive_int_refinement_ty())],
        requires: Some(gt_int_var("amount", 1)),
        nodes: vec![
            E::EProcNode {
                name: "charge".to_owned(),
                instance: "gateway".to_owned(),
                command: "authorize".to_owned(),
                args: vec![int_var("amount")],
            },
            E::EProcNode {
                name: "ship".to_owned(),
                instance: "self".to_owned(),
                command: "ship".to_owned(),
                args: vec![],
            },
        ],
        edges: vec![E::EProcEdge {
            target: "ship".to_owned(),
            condition: E::EProcDepCond::Fact {
                node: "charge".to_owned(),
                qualifier: Some("ok".to_owned()),
            },
        }],
        proc_uses: vec![],
        span: None,
    }];
    let all_systems = vec![gateway, program.clone()];

    let lowered = super::system::lower_system(&program, &all_systems, &aliases, &ctx);

    assert!(
        lowered
            .entities
            .iter()
            .any(|entity| entity.contains("checkout")),
        "program procs should add their hidden workflow entity to system entities: {:?}",
        lowered.entities
    );
    assert_eq!(lowered.procs[0].params.len(), 1);
    assert_eq!(lowered.procs[0].params[0].ty, IRType::Int);
    assert!(
        matches!(
            lowered.procs[0].requires.as_ref(),
            Some(IRExpr::BinOp { op, left, right, .. })
                if op == "OpAnd"
                    && matches!(left.as_ref(), IRExpr::BinOp { op, .. } if op == "OpGt")
                    && matches!(right.as_ref(), IRExpr::BinOp { op, .. } if op == "OpGt")
        ),
        "proc requires should include refinement and explicit guards: {:?}",
        lowered.procs[0].requires
    );
    assert!(
        lowered
            .commands
            .iter()
            .any(|command| command.name == "checkout" && command.params[0].ty == IRType::Int),
        "synthetic proc start command should use stripped refined params: {:?}",
        lowered.commands
    );
    let charge_action = lowered
        .actions
        .iter()
        .find(|action| {
            action.body.iter().any(|step| {
                matches!(
                    step,
                    IRAction::LetCrossCall { system, command, args, .. }
                        if system == "Gateway" && command == "authorize" && args.len() == 1
                )
            })
        })
        .expect("charge proc node should synthesize a cross-call action");
    assert!(
        charge_action
            .body
            .iter()
            .any(|step| matches!(step, IRAction::Match { arms, .. }
                if arms.iter().any(|arm| matches!(&arm.pattern, IRPattern::PCtor { name, .. } if name == "ok"))
                    && arms.iter().any(|arm| matches!(&arm.pattern, IRPattern::PWild)))),
        "outcome-bearing proc node should synthesize match arms for return variants and fallback: {:?}",
        charge_action.body
    );
    let ok_arm_transition = charge_action.body.iter().find_map(|step| {
        let IRAction::Match { arms, .. } = step else {
            return None;
        };
        arms.iter().find_map(|arm| {
            if !matches!(&arm.pattern, IRPattern::PCtor { name, .. } if name == "ok") {
                return None;
            }
            arm.body.iter().find_map(|body_step| {
                let IRAction::Choose { ops, .. } = body_step else {
                    return None;
                };
                ops.iter().find_map(|op| {
                    let IRAction::Apply { transition, .. } = op else {
                        return None;
                    };
                    Some(transition.as_str())
                })
            })
        })
    });
    assert!(
        ok_arm_transition.is_some_and(|transition| transition.contains("ok")),
        "ok outcome arm should apply an ok-specific workflow transition, got {:?}",
        charge_action.body
    );
}

#[test]
fn lower_program_preserves_interface_metadata_and_implementors() {
    let mut er = empty_elab_result();
    er.interfaces.push(E::EInterface {
        name: "PaymentProcessor".to_owned(),
        commands: vec![E::ECommand {
            name: "authorize".to_owned(),
            params: vec![("amount".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
            return_type: Some(E::Ty::Builtin(E::BuiltinTy::String)),
            span: None,
        }],
        queries: vec![],
        span: None,
    });
    er.systems.push(E::ESystem {
        name: "LocalGateway".to_owned(),
        implements: Some("PaymentProcessor".to_owned()),
        deps: vec![],
        fields: vec![],
        store_params: vec![],
        scopes: vec![],
        commands: vec![],
        actions: vec![],
        queries: vec![],
        fsm_decls: vec![],
        derived_fields: vec![],
        invariants: vec![],
        preds: vec![],
        let_bindings: vec![],
        procs: vec![],
        proc_uses: vec![],
        span: None,
    });
    er.externs.push(E::EExtern {
        name: "StripeGateway".to_owned(),
        implements: Some("PaymentProcessor".to_owned()),
        commands: vec![E::ECommand {
            name: "authorize".to_owned(),
            params: vec![("amount".to_owned(), E::Ty::Builtin(E::BuiltinTy::Int))],
            return_type: Some(E::Ty::Builtin(E::BuiltinTy::String)),
            span: None,
        }],
        mays: vec![],
        assumes: vec![],
        span: None,
    });

    let (program, diagnostics) = lower(&er);

    assert!(
        !diagnostics.has_errors(),
        "interface metadata lowering should not report diagnostics: {:?}",
        diagnostics.diagnostics
    );
    let interface = program.interfaces.first().expect("interface metadata");
    assert_eq!(interface.name, "PaymentProcessor");
    assert_eq!(interface.commands.len(), 1);
    assert_eq!(interface.commands[0].name, "authorize");
    assert_eq!(interface.commands[0].params.len(), 1);
    assert_eq!(interface.commands[0].return_type, Some(IRType::String));
    assert!(interface.queries.is_empty());
    assert_eq!(interface.implementors.len(), 2);
    assert_eq!(interface.implementors[0].name, "LocalGateway");
    assert_eq!(
        interface.implementors[0].kind,
        IRInterfaceImplementorKind::System
    );
    assert_eq!(interface.implementors[1].name, "StripeGateway");
    assert_eq!(
        interface.implementors[1].kind,
        IRInterfaceImplementorKind::Extern
    );
}

#[test]
fn lower_extern_reports_multi_segment_fairness_instead_of_dropping_it() {
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let span = Span { start: 10, end: 25 };
    let ext = E::EExtern {
        name: "Gateway".to_owned(),
        implements: None,
        commands: vec![
            E::ECommand {
                name: "authorize".to_owned(),
                params: vec![],
                return_type: None,
                span: None,
            },
            E::ECommand {
                name: "settle".to_owned(),
                params: vec![],
                return_type: None,
                span: None,
            },
        ],
        mays: vec![],
        assumes: vec![
            E::EExternAssume::Fair(
                vec!["Gateway".to_owned(), "authorize".to_owned()],
                Some(span),
            ),
            E::EExternAssume::StrongFair(
                vec!["Gateway".to_owned(), "settle".to_owned()],
                Some(span),
            ),
        ],
        span: None,
    };

    let lowered = super::system::lower_extern(&ext, &ctx);
    let diagnostics = ctx.take_diagnostics();

    assert!(
        diagnostics.has_errors(),
        "multi-segment extern fairness must produce a lower diagnostic"
    );
    assert!(
        diagnostics.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("fairness assumptions must reference a local command name")),
        "expected actionable local-command diagnostic, got: {:?}",
        diagnostics.diagnostics
    );
    assert!(
        lowered
            .preds
            .iter()
            .all(|pred| !pred.name.contains("Gateway")),
        "multi-segment fairness should not synthesize misleading hidden preds: {:?}",
        lowered.preds
    );
}

fn empty_elab_result() -> E::ElabResult {
    E::ElabResult {
        module_name: None,
        includes: vec![],
        use_decls: vec![],
        aliases: std::collections::HashMap::new(),
        types: vec![],
        entities: vec![],
        interfaces: vec![],
        externs: vec![],
        systems: vec![],
        preds: vec![],
        props: vec![],
        verifies: vec![],
        scenes: vec![],
        theorems: vec![],
        axioms: vec![],
        lemmas: vec![],
        consts: vec![],
        fns: vec![],
        under_blocks: vec![],
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
fn lower_expr_dispatches_only_supported_relation_qualified_calls() {
    let result_ty = E::Ty::Relation(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Builtin(E::BuiltinTy::String),
    ]);
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let field_call = lower_expr(
        &E::EExpr::QualCall(
            result_ty.clone(),
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
        ),
        &ctx,
    );
    assert!(
        matches!(
            field_call,
            IRExpr::BinOp { ref op, ref right, .. }
                if op == "OpRelationField"
                    && matches!(right.as_ref(), IRExpr::Var { name, .. } if name == "Order::status")
        ),
        "Rel::field should lower to the relation-field IR operator: {field_call:?}"
    );

    let tuple_set_ty = E::Ty::Set(Box::new(E::Ty::Tuple(vec![
        E::Ty::Entity("Order".to_owned()),
        E::Ty::Entity("Customer".to_owned()),
        E::Ty::Builtin(E::BuiltinTy::String),
    ])));
    let project_call = lower_expr(
        &E::EExpr::QualCall(
            result_ty.clone(),
            "Rel".to_owned(),
            "project".to_owned(),
            vec![
                E::EExpr::Var(tuple_set_ty, "order_customer_segment".to_owned(), None),
                int_lit(0),
                int_lit(2),
            ],
            None,
        ),
        &ctx,
    );
    assert!(
        matches!(
            project_call,
            IRExpr::BinOp { ref op, .. } if op == "OpRelProject"
        ),
        "Rel::project with at least two args should lower to the relation-project IR operator: {project_call:?}"
    );

    let rel_project_without_columns = lower_expr(
        &E::EExpr::QualCall(
            result_ty.clone(),
            "Rel".to_owned(),
            "project".to_owned(),
            vec![E::EExpr::Var(
                E::Ty::Set(Box::new(E::Ty::Tuple(vec![
                    E::Ty::Entity("Order".to_owned()),
                    E::Ty::Builtin(E::BuiltinTy::String),
                ]))),
                "order_status".to_owned(),
                None,
            )],
            None,
        ),
        &ctx,
    );
    assert!(
        !matches!(rel_project_without_columns, IRExpr::BinOp { ref op, .. } if op == "OpRelProject"),
        "Rel::project without projection columns should stay off the relation-project path: {rel_project_without_columns:?}"
    );

    let set_project = lower_expr(
        &E::EExpr::QualCall(
            result_ty,
            "Set".to_owned(),
            "project".to_owned(),
            vec![E::EExpr::Var(
                E::Ty::Set(Box::new(E::Ty::Builtin(E::BuiltinTy::Int))),
                "xs".to_owned(),
                None,
            )],
            None,
        ),
        &ctx,
    );
    assert!(
        !matches!(set_project, IRExpr::BinOp { ref op, .. } if op == "OpRelProject"),
        "non-Rel project calls should stay off the Rel::project path: {set_project:?}"
    );
}

#[test]
fn lower_match_patterns_resolve_enum_constructor_binders_through_or_patterns() {
    let status_ty = E::Ty::Enum(
        "Status".to_owned(),
        vec!["Open".to_owned(), "Closed".to_owned(), "Paused".to_owned()],
    );
    let match_expr = E::EExpr::Match(
        Box::new(E::EExpr::Var(status_ty.clone(), "status".to_owned(), None)),
        vec![
            (E::EPattern::Var("Open".to_owned()), None, bool_lit(true)),
            (
                E::EPattern::Or(
                    Box::new(E::EPattern::Var("Closed".to_owned())),
                    Box::new(E::EPattern::Var("Paused".to_owned())),
                ),
                None,
                bool_lit(false),
            ),
            (
                E::EPattern::Var("other_status".to_owned()),
                None,
                bool_lit(false),
            ),
        ],
        None,
    );
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());

    let lowered = lower_expr(&match_expr, &ctx);

    let IRExpr::Match { arms, .. } = lowered else {
        panic!("expected match expression");
    };
    assert!(matches!(
        &arms[0].pattern,
        IRPattern::PCtor { name, fields } if name == "Open" && fields.is_empty()
    ));
    assert!(matches!(
        &arms[1].pattern,
        IRPattern::POr { left, right }
            if matches!(left.as_ref(), IRPattern::PCtor { name, .. } if name == "Closed")
                && matches!(right.as_ref(), IRPattern::PCtor { name, .. } if name == "Paused")
    ));
    assert!(matches!(
        &arms[2].pattern,
        IRPattern::PVar { name } if name == "other_status"
    ));
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
        activations: vec![],
        initial_constraints: vec![],
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
fn lower_scene_records_textual_order_for_unordered_when_actions() {
    let es = E::EScene {
        name: "sc".to_owned(),
        stores: vec![],
        let_bindings: vec![E::ELetBinding {
            name: "doors".to_owned(),
            system_type: "Doors".to_owned(),
            store_bindings: vec![],
        }],
        givens: vec![],
        whens: vec![
            E::ESceneWhen::Action {
                var: "doors_close".to_owned(),
                system: "Doors".to_owned(),
                event: "close".to_owned(),
                args: vec![],
                card: Some("one".to_owned()),
            },
            E::ESceneWhen::Action {
                var: "doors_open".to_owned(),
                system: "Doors".to_owned(),
                event: "open".to_owned(),
                args: vec![],
                card: Some("one".to_owned()),
            },
        ],
        thens: vec![],
        given_constraints: vec![],
        activations: vec![],
        span: None,
        file: None,
    };
    let vi = VariantInfo::new();
    let ctx = LowerCtx::new(&vi, std::collections::HashSet::new());
    let ir = lower_scene(&es, &std::collections::HashMap::new(), &ctx);

    assert_eq!(ir.ordering.len(), 1);
    assert!(
        matches!(
            &ir.ordering[0],
            IRExpr::BinOp { op, left, right, .. }
                if op == "OpSeq"
                    && matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "doors_close")
                    && matches!(right.as_ref(), IRExpr::Var { name, .. } if name == "doors_open")
        ),
        "unordered when actions should lower with textual OpSeq ordering, got: {:?}",
        ir.ordering
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
