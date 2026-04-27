use std::collections::{HashMap, HashSet};

use super::*;
use crate::verify::{encode, walkers};

mod macro_impl;
mod nested;

pub(crate) use self::macro_impl::try_encode_step_inner;
use self::macro_impl::*;

/// Encode a system event as a single transition step.
///
/// Processes the event guard, then each `IRAction` in the event body:
/// - `Choose` — existential over active slots matching filter, with per-slot framing
/// - `ForAll` — conjunction over all active slots
/// - `Apply` — resolve entity and action, encode with per-slot framing
/// - `Create` — delegate to `encode_create`
/// - `CrossCall` — resolve target system event and encode inline
/// - `ExprStmt` — encode as boolean constraint
///
/// Frames all entity slots NOT touched by the event.
#[allow(clippy::too_many_lines)]
pub fn encode_step(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
) -> Bool {
    try_encode_step(pool, vctx, entities, all_systems, event, step)
        .unwrap_or_else(|msg| panic!("{msg}"))
}

#[allow(clippy::too_many_lines)]
pub fn try_encode_step(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
) -> Result<Bool, String> {
    let (formula, touched) =
        try_encode_step_inner(pool, vctx, entities, all_systems, event, step, 0, None)?;
    Ok(apply_global_frame(pool, entities, &touched, step, formula))
}

/// Encode an event with specific parameter values (for scene checking).
///
/// Scene events supply concrete argument values (resolved from given bindings)
/// rather than fresh unconstrained Z3 variables.
#[allow(clippy::implicit_hasher)]
pub fn encode_step_with_params(
    pool: &SlotPool,
    vctx: &VerifyContext,
    entities: &[IREntity],
    all_systems: &[IRSystem],
    event: &IRStep,
    step: usize,
    params: HashMap<String, SmtValue>,
) -> Bool {
    let (formula, touched) = encode_step_inner(
        pool,
        vctx,
        entities,
        all_systems,
        event,
        step,
        0,
        Some(params),
    );
    apply_global_frame(pool, entities, &touched, step, formula)
}

/// Apply global frame for untouched slots to an event formula.
/// Called once at the top level — never inside recursive `CrossCall` encoding.
pub(crate) fn apply_global_frame(
    pool: &SlotPool,
    entities: &[IREntity],
    touched: &HashSet<(String, usize)>,
    step: usize,
    formula: Bool,
) -> Bool {
    let frame = frame_untouched_slots(pool, entities, touched, step);
    let mut all = vec![formula];
    all.extend(frame);
    let refs: Vec<&Bool> = all.iter().collect();
    smt::bool_and(&refs)
}

/// Encode a non-Apply nested action within the bound context of a Choose or
/// `ForAll` iteration. The bound variable's fields at the given slot are made
/// available via params so nested expressions can reference them (e.g., `o.id`
/// inside `choose o: Order { create Receipt { order_id = o.id } }`).
///
/// Returns `(formulas, additional_touched)` where formulas should be conjoined
/// with the current slot's constraints and `additional_touched` contains entity
/// slots that were modified by the nested action (for global frame tracking).
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRActionMatchArm, IRActionMatchScrutinee, IRCreateField, IRField, IRPattern, IRProgram,
        IRStoreParam, IRTransition, IRTypeEntry, IRUpdate, IRVariant,
    };
    use crate::verify::smt::{self, AbideSolver, SatResult};

    fn make_step_test_entity() -> IREntity {
        IREntity {
            name: "Order".to_owned(),
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
                name: "set_total".to_owned(),
                refs: vec![],
                params: vec![IRTransParam {
                    name: "next".to_owned(),
                    ty: IRType::Int,
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "total".to_owned(),
                    value: IRExpr::Var {
                        name: "next".to_owned(),
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

    fn make_step_test_vctx() -> VerifyContext {
        VerifyContext::from_ir(&IRProgram {
            types: vec![
                IRTypeEntry {
                    name: "Status".to_owned(),
                    ty: IRType::Enum {
                        name: "Status".to_owned(),
                        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
                    },
                },
                IRTypeEntry {
                    name: "Decision".to_owned(),
                    ty: IRType::Enum {
                        name: "Decision".to_owned(),
                        variants: vec![IRVariant::simple("Set"), IRVariant::simple("Skip")],
                    },
                },
            ],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        })
    }

    #[test]
    fn contains_macro_actions_recurses_through_nested_blocks() {
        let actions = vec![IRAction::Choose {
            var: "o".to_owned(),
            entity: "Order".to_owned(),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            ops: vec![IRAction::Match {
                scrutinee: crate::ir::types::IRActionMatchScrutinee::Var {
                    name: "result".to_owned(),
                },
                arms: vec![],
            }],
        }];

        assert!(contains_macro_actions(&actions));
        assert!(!contains_macro_actions(&[IRAction::ExprStmt {
            expr: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
        }]));
    }

    #[test]
    fn step_scope_metadata_and_branch_param_merging_resolve_expected_bindings() {
        let event = IRStep {
            name: "tick".to_owned(),
            params: vec![
                IRTransParam {
                    name: "order".to_owned(),
                    ty: IRType::Entity {
                        name: "Order".to_owned(),
                    },
                },
                IRTransParam {
                    name: "limit".to_owned(),
                    ty: IRType::Int,
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
        let system = IRSystem {
            name: "Shop".to_owned(),
            store_params: vec![IRStoreParam {
                name: "orders".to_owned(),
                entity_type: "Order".to_owned(),
            }],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![event.clone()],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };

        let (system_name, entity_params, store_params) =
            step_scope_metadata(std::slice::from_ref(&system), &system.steps[0]);
        assert_eq!(system_name, "Shop");
        assert_eq!(entity_params.get("order"), Some(&"Order".to_owned()));
        assert_eq!(store_params.get("orders"), Some(&"Order".to_owned()));
        assert!(event_param_is_entity("order", &entity_params));
        assert!(!event_param_is_entity("limit", &entity_params));

        let merged = merged_branch_params(
            &HashMap::from([("x".to_owned(), smt::int_val(1))]),
            &HashMap::from([
                ("x".to_owned(), smt::int_val(2)),
                ("y".to_owned(), smt::int_val(3)),
            ]),
        );
        let solver = AbideSolver::new();
        solver.assert(&smt::smt_eq(merged.get("x").expect("x"), &smt::int_val(2)).expect("x eq"));
        solver.assert(&smt::smt_eq(merged.get("y").expect("y"), &smt::int_val(3)).expect("y eq"));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn fresh_smt_value_covers_scalar_and_dynamic_types() {
        assert!(matches!(
            fresh_smt_value("b", &IRType::Bool),
            SmtValue::Bool(_)
        ));
        assert!(matches!(
            fresh_smt_value("i", &IRType::Int),
            SmtValue::Int(_)
        ));
        assert!(matches!(
            fresh_smt_value("r", &IRType::Real),
            SmtValue::Real(_)
        ));
        assert!(matches!(
            fresh_smt_value(
                "m",
                &IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                }
            ),
            SmtValue::Array(_)
        ));
    }

    #[test]
    fn try_encode_macro_value_expr_handles_choose_let_and_ifelse() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
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

        let (choice, choice_constraints) = try_encode_macro_value_expr(
            &ctx,
            &IRExpr::Choose {
                var: "x".to_owned(),
                domain: IRType::Int,
                predicate: Some(Box::new(IRExpr::BinOp {
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
                })),
                ty: IRType::Int,
                span: None,
            },
            0,
        )
        .expect("choose expr");
        assert!(matches!(choice, SmtValue::Int(_)));
        assert_eq!(choice_constraints.len(), 1);

        let (let_value, let_constraints) = try_encode_macro_value_expr(
            &ctx,
            &IRExpr::Let {
                bindings: vec![crate::ir::types::LetBinding {
                    name: "tmp".to_owned(),
                    ty: IRType::Int,
                    expr: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 2 },
                        span: None,
                    },
                }],
                body: Box::new(IRExpr::BinOp {
                    op: "OpAdd".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "tmp".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 5 },
                        span: None,
                    }),
                    ty: IRType::Int,
                    span: None,
                }),
                span: None,
            },
            0,
        )
        .expect("let expr");
        assert!(let_constraints.is_empty());
        let let_solver = AbideSolver::new();
        let_solver.assert(&smt::smt_eq(&let_value, &smt::int_val(7)).expect("let eq"));
        assert_eq!(let_solver.check(), SatResult::Sat);

        let (if_value, if_constraints) = try_encode_macro_value_expr(
            &ctx,
            &IRExpr::IfElse {
                cond: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                then_body: Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 3 },
                    span: None,
                }),
                else_body: Some(Box::new(IRExpr::Lit {
                    ty: IRType::Int,
                    value: LitVal::Int { value: 9 },
                    span: None,
                })),
                span: None,
            },
            0,
        )
        .expect("if expr");
        assert!(if_constraints.is_empty());
        let if_solver = AbideSolver::new();
        if_solver.assert(&smt::smt_eq(&if_value, &smt::int_val(3)).expect("if eq"));
        assert_eq!(if_solver.check(), SatResult::Sat);

        let (match_value, match_constraints) = try_encode_macro_value_expr(
            &ctx,
            &IRExpr::Match {
                scrutinee: Box::new(IRExpr::Ctor {
                    enum_name: "Decision".to_owned(),
                    ctor: "Set".to_owned(),
                    args: vec![],
                    span: None,
                }),
                arms: vec![
                    crate::ir::types::IRMatchArm {
                        pattern: IRPattern::PCtor {
                            name: "Set".to_owned(),
                            fields: vec![],
                        },
                        guard: Some(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        body: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 11 },
                            span: None,
                        },
                    },
                    crate::ir::types::IRMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: IRExpr::Lit {
                            ty: IRType::Int,
                            value: LitVal::Int { value: 0 },
                            span: None,
                        },
                    },
                ],
                span: None,
            },
            0,
        )
        .expect("match expr");
        assert_eq!(match_constraints.len(), 1);
        let match_solver = AbideSolver::new();
        match_solver.assert(&match_constraints[0]);
        match_solver.assert(&smt::smt_eq(&match_value, &smt::int_val(11)).expect("match eq"));
        assert_eq!(match_solver.check(), SatResult::Sat);
    }

    #[test]
    fn try_encode_nested_op_covers_create_expr_and_nested_quantified_blocks() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 2_usize)]),
            1,
        );
        let params = HashMap::from([("o.total".to_owned(), smt::int_val(1))]);

        let (expr_formulas, expr_touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &IRAction::ExprStmt {
                expr: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
            },
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("expr nested op");
        assert_eq!(expr_formulas.len(), 1);
        assert!(expr_touched.is_empty());

        let (create_formulas, create_touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &IRAction::Create {
                entity: "Order".to_owned(),
                fields: vec![IRCreateField {
                    name: "total".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Int,
                        value: LitVal::Int { value: 7 },
                        span: None,
                    },
                }],
            },
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("create nested op");
        assert!(!create_formulas.is_empty());
        assert!(create_touched.contains(&("Order".to_owned(), 0)));
        assert!(create_touched.contains(&("Order".to_owned(), 1)));

        let apply = IRAction::Apply {
            target: "inner".to_owned(),
            transition: "set_total".to_owned(),
            refs: vec![],
            args: vec![IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 3 },
                span: None,
            }],
        };
        let choose = IRAction::Choose {
            var: "inner".to_owned(),
            entity: "Order".to_owned(),
            filter: Box::new(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            }),
            ops: vec![apply.clone()],
        };
        let forall = IRAction::ForAll {
            var: "inner".to_owned(),
            entity: "Order".to_owned(),
            ops: vec![apply],
        };

        for op in [choose, forall] {
            let (formulas, touched) = nested::try_encode_nested_op(
                &pool,
                &vctx,
                std::slice::from_ref(&entity),
                &[],
                &op,
                "o",
                "Order",
                &entity,
                0,
                0,
                &params,
                0,
                &[],
            )
            .expect("nested block op");
            assert!(!formulas.is_empty());
            assert!(touched.contains(&("Order".to_owned(), 0)));
            assert!(touched.contains(&("Order".to_owned(), 1)));
        }

        let err = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &IRAction::LetCrossCall {
                name: "x".to_owned(),
                system: "Missing".to_owned(),
                command: "noop".to_owned(),
                args: vec![],
            },
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect_err("let crosscall nested op is unsupported");
        assert!(err.contains("not yet supported"));
    }

    #[test]
    fn try_encode_nested_op_resolves_apply_targets_and_crosscalls() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 2_usize)]),
            1,
        );
        let params = HashMap::from([("o.total".to_owned(), smt::int_val(1))]);

        let direct_apply = IRAction::Apply {
            target: "o".to_owned(),
            transition: "set_total".to_owned(),
            args: vec![int_lit(6)],
            refs: vec![],
        };
        let (formulas, touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &direct_apply,
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("direct bound apply");
        assert!(touched.contains(&("Order".to_owned(), 0)));
        assert_formula_allows_next_total(&pool, &formulas[0], 0, 6);

        let outer_apply = IRAction::Apply {
            target: "outer".to_owned(),
            transition: "set_total".to_owned(),
            args: vec![int_lit(8)],
            refs: vec![],
        };
        let (formulas, touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &outer_apply,
            "inner",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[("outer", "Order", &entity, 1)],
        )
        .expect("outer bound apply");
        assert!(touched.contains(&("Order".to_owned(), 1)));
        assert_formula_allows_next_total(&pool, &formulas[0], 1, 8);

        let fallback_apply = IRAction::Apply {
            target: "Order".to_owned(),
            transition: "set_total".to_owned(),
            args: vec![int_lit(4)],
            refs: vec![],
        };
        let (formulas, touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &fallback_apply,
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("fallback entity apply");
        assert!(touched.contains(&("Order".to_owned(), 0)));
        assert!(touched.contains(&("Order".to_owned(), 1)));
        assert_formula_allows_next_total(&pool, &formulas[0], 1, 4);

        let relay = IRSystem {
            name: "Relay".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "set_from_relay".to_owned(),
                params: vec![IRTransParam {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
                }],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Apply {
                    target: "Order".to_owned(),
                    transition: "set_total".to_owned(),
                    args: vec![IRExpr::Var {
                        name: "amount".to_owned(),
                        ty: IRType::Int,
                        span: None,
                    }],
                    refs: vec![],
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
        let cross_call = IRAction::CrossCall {
            system: "Relay".to_owned(),
            command: "set_from_relay".to_owned(),
            args: vec![int_lit(10)],
        };
        let (formulas, touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            std::slice::from_ref(&relay),
            &cross_call,
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("cross call");
        assert!(touched.contains(&("Order".to_owned(), 0)));
        assert!(touched.contains(&("Order".to_owned(), 1)));
        assert_formula_allows_next_total(&pool, &formulas[0], 0, 10);
    }

    #[test]
    fn try_encode_nested_op_crosscall_handles_missing_and_arity_mismatch() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 1_usize)]),
            1,
        );
        let params = HashMap::new();
        let missing = IRAction::CrossCall {
            system: "Missing".to_owned(),
            command: "noop".to_owned(),
            args: vec![],
        };
        let (formulas, touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &[],
            &missing,
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("missing cross-call target is ignored by encoder");
        assert!(formulas.is_empty());
        assert!(touched.is_empty());

        let relay = IRSystem {
            name: "Relay".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![IRStep {
                name: "needs_arg".to_owned(),
                params: vec![IRTransParam {
                    name: "amount".to_owned(),
                    ty: IRType::Int,
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
        let mismatched = IRAction::CrossCall {
            system: "Relay".to_owned(),
            command: "needs_arg".to_owned(),
            args: vec![],
        };
        let (formulas, touched) = nested::try_encode_nested_op(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            std::slice::from_ref(&relay),
            &mismatched,
            "o",
            "Order",
            &entity,
            0,
            0,
            &params,
            0,
            &[],
        )
        .expect("arity mismatch creates false branch");
        assert!(touched.is_empty());
        let solver = AbideSolver::new();
        solver.assert(&formulas[0]);
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    fn assert_formula_allows_next_total(
        pool: &SlotPool,
        formula: &Bool,
        slot: usize,
        next_total: i64,
    ) {
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", slot, 0) {
            solver.assert(active);
        }
        solver.assert(formula);
        solver.assert(
            &smt::smt_eq(
                pool.field_at("Order", slot, "total", 1)
                    .expect("next total"),
                &smt::int_val(next_total),
            )
            .expect("next total eq"),
        );
        assert_eq!(solver.check(), SatResult::Sat);
    }

    fn decision_system(return_expr: Option<IRExpr>) -> IRSystem {
        IRSystem {
            name: "DecisionWorker".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec![],
            commands: vec![],
            steps: vec![IRStep {
                name: "decide".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![],
                return_expr,
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

    fn make_shop_system(step: IRStep) -> IRSystem {
        IRSystem {
            name: "Shop".to_owned(),
            store_params: vec![],
            fields: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            steps: vec![step],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        }
    }

    fn int_lit(value: i64) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        }
    }

    #[test]
    fn try_encode_step_inner_macro_handles_let_crosscall_match_apply() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let decision = decision_system(Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Set".to_owned(),
            args: vec![],
            span: None,
        }));
        let relay = make_shop_system(IRStep {
            name: "relay".to_owned(),
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
                                name: "Set".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: vec![IRAction::Apply {
                                target: "Order".to_owned(),
                                transition: "set_total".to_owned(),
                                args: vec![int_lit(7)],
                                refs: vec![],
                            }],
                        },
                        IRActionMatchArm {
                            pattern: IRPattern::PWild,
                            guard: None,
                            body: vec![IRAction::Apply {
                                target: "Order".to_owned(),
                                transition: "set_total".to_owned(),
                                args: vec![int_lit(1)],
                                refs: vec![],
                            }],
                        },
                    ],
                },
            ],
            return_expr: None,
        });
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 1_usize)]),
            1,
        );
        let systems = vec![relay.clone(), decision];
        let (formula, touched) = try_encode_step_inner(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &systems,
            &relay.steps[0],
            0,
            0,
            None,
        )
        .expect("macro step");
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
            solver.assert(active);
        }
        solver.assert(&formula);
        solver.assert(
            &smt::smt_eq(
                pool.field_at("Order", 0, "total", 1).expect("next total"),
                &smt::int_val(7),
            )
            .expect("next total eq"),
        );
        assert_eq!(solver.check(), SatResult::Sat);
        assert!(touched.contains(&("Order".to_owned(), 0)));
    }

    #[test]
    fn try_encode_step_inner_macro_rejects_choose_scoped_crosscall_match() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let decision = decision_system(Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Set".to_owned(),
            args: vec![],
            span: None,
        }));
        let relay = make_shop_system(IRStep {
            name: "relay_choose".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::Choose {
                var: "order".to_owned(),
                entity: "Order".to_owned(),
                filter: Box::new(IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                }),
                ops: vec![
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
                        arms: vec![IRActionMatchArm {
                            pattern: IRPattern::PCtor {
                                name: "Set".to_owned(),
                                fields: vec![],
                            },
                            guard: None,
                            body: vec![IRAction::Apply {
                                target: "order".to_owned(),
                                transition: "set_total".to_owned(),
                                args: vec![int_lit(9)],
                                refs: vec![],
                            }],
                        }],
                    },
                ],
            }],
            return_expr: None,
        });
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 1_usize)]),
            1,
        );
        let systems = vec![relay.clone(), decision];
        let err = try_encode_step_inner(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &systems,
            &relay.steps[0],
            0,
            0,
            None,
        )
        .expect_err("nested macro choose should fail");
        assert!(err.contains("not yet supported inside choose/for blocks"));
    }

    #[test]
    fn try_encode_step_inner_macro_handles_crosscall_match_scrutinee() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let decision = decision_system(Some(IRExpr::Ctor {
            enum_name: "Decision".to_owned(),
            ctor: "Set".to_owned(),
            args: vec![],
            span: None,
        }));
        let relay = make_shop_system(IRStep {
            name: "relay_match".to_owned(),
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
                        body: vec![IRAction::Apply {
                            target: "Order".to_owned(),
                            transition: "set_total".to_owned(),
                            args: vec![int_lit(3)],
                            refs: vec![],
                        }],
                    },
                    IRActionMatchArm {
                        pattern: IRPattern::PWild,
                        guard: None,
                        body: vec![IRAction::Apply {
                            target: "Order".to_owned(),
                            transition: "set_total".to_owned(),
                            args: vec![int_lit(0)],
                            refs: vec![],
                        }],
                    },
                ],
            }],
            return_expr: None,
        });
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 1_usize)]),
            1,
        );
        let systems = vec![relay.clone(), decision];
        let (formula, _) = try_encode_step_inner(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &systems,
            &relay.steps[0],
            0,
            0,
            None,
        )
        .expect("macro match step");
        let solver = AbideSolver::new();
        if let Some(SmtValue::Bool(active)) = pool.active_at("Order", 0, 0) {
            solver.assert(active);
        }
        solver.assert(&formula);
        solver.assert(
            &smt::smt_eq(
                pool.field_at("Order", 0, "total", 1).expect("next total"),
                &smt::int_val(3),
            )
            .expect("next total eq"),
        );
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn try_encode_step_inner_macro_rejects_binding_commands_without_return_values() {
        let entity = make_step_test_entity();
        let vctx = make_step_test_vctx();
        let decision = decision_system(None);
        let relay = make_shop_system(IRStep {
            name: "relay_err".to_owned(),
            params: vec![],
            guard: IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
            body: vec![IRAction::LetCrossCall {
                name: "decision".to_owned(),
                system: "DecisionWorker".to_owned(),
                command: "decide".to_owned(),
                args: vec![],
            }],
            return_expr: None,
        });
        let pool = create_slot_pool(
            std::slice::from_ref(&entity),
            &HashMap::from([(entity.name.clone(), 1_usize)]),
            1,
        );
        let systems = vec![relay.clone(), decision];
        let err = try_encode_step_inner(
            &pool,
            &vctx,
            std::slice::from_ref(&entity),
            &systems,
            &relay.steps[0],
            0,
            0,
            None,
        )
        .expect_err("binding without return should fail");
        assert!(err.contains("return a value"));
    }
}
