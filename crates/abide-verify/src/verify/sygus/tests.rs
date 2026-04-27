use super::*;
use crate::ir::types::{IRProgram, IRTransition, IRUpdate, IRVariant, LitVal};
use crate::verify::context::VerifyContext;
use crate::verify::ic3;
use crate::verify::solver::{active_solver_family, set_active_solver_family, SolverFamily};
use crate::verify::transition::{solve_transition_obligation, TransitionObligation};

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

#[test]
fn sygus_core_reports_unsupported_shapes_before_solver_setup() {
    use crate::ir::types::{IRCommand, IRDerivedField, IRFsm, IRStoreParam};

    let mut derived_entity = make_counter_entity();
    derived_entity.derived_fields.push(IRDerivedField {
        name: "double".to_owned(),
        body: IRExpr::Var {
            name: "x".to_owned(),
            ty: IRType::Int,
            span: None,
        },
        ty: IRType::Int,
    });
    let err = try_cvc5_sygus_single_entity_inner(&derived_entity, &non_negative_property(), 0)
        .expect_err("derived fields unsupported");
    assert!(err.contains("derived fields"));

    let mut fsm_entity = make_counter_entity();
    fsm_entity.fsm_decls.push(IRFsm {
        field: "x".to_owned(),
        enum_name: "CounterState".to_owned(),
        transitions: vec![],
    });
    let err = try_cvc5_sygus_single_entity_inner(&fsm_entity, &non_negative_property(), 0)
        .expect_err("fsm unsupported");
    assert!(err.contains("FSM"));

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

    let mut system = make_counter_system();
    system.commands.push(IRCommand {
        name: "inc".to_owned(),
        params: vec![],
        return_type: None,
    });
    let err = try_cvc5_sygus_system_safety_inner(&system, &non_negative_property(), 0)
        .expect_err("commands unsupported");
    assert!(err.contains("command declarations"));

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
        steps: vec![IRStep {
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
    let status_ty = IRType::Enum {
        name: "Status".to_owned(),
        variants: vec![IRVariant::simple("Pending"), IRVariant::simple("Done")],
    };
    IRSystem {
        name: "StatusSys".to_owned(),
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
        steps: vec![IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
            IRStep {
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
        matches!(result, Ic3Result::Unknown(ref msg) if msg.contains("only supports Bool and fieldless-enum step params")),
        "expected honest Unknown for unsupported SyGuS shape, got: {result:?}"
    );
}

#[test]
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
fn cvc5_sygus_pooled_system_safety_supports_nested_choose_ref_binding() {
    let system = IRSystem {
        name: "CounterRefPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        steps: vec![
            IRStep {
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
            IRStep {
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
fn cvc5_sygus_pooled_system_safety_supports_forall_with_nested_choose_ref_binding() {
    let system = IRSystem {
        name: "CounterNestedRefPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        steps: vec![
            IRStep {
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
            IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_supports_crosscall_leaf_step() {
    let mut root = make_pooled_counter_system();
    root.name = "CounterRelayPool".to_owned();
    root.steps[1] = IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_supports_crosscall_step_args() {
    let mut root = make_pooled_bool_param_counter_system();
    root.name = "CounterArgRelayPool".to_owned();
    root.steps[1] = IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_supports_nested_crosscall_chain() {
    let mut root = make_pooled_counter_system();
    root.name = "CounterRelayPool".to_owned();
    root.steps[1] = IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_returns_unknown_for_crosscall_cycle() {
    let mut root = make_pooled_counter_system();
    root.name = "CounterCycleRoot".to_owned();
    root.steps[1] = IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_supports_let_crosscall_binding() {
    let entity = make_pooled_bool_param_counter_entity();
    let relay = IRSystem {
        name: "CounterLetRelayPool".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_supports_callee_system_fields() {
    let entity = make_pooled_bool_param_counter_entity();
    let root = IRSystem {
        name: "CounterFieldRoot".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_system_pooled_safety_supports_callee_store_params() {
    let entity = make_pooled_bool_param_counter_entity();
    let root = IRSystem {
        name: "CounterStoreRoot".to_owned(),
        store_params: vec![],
        fields: vec![],
        entities: vec!["Counter".to_owned()],
        commands: vec![],
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
        steps: vec![
            IRStep {
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
            IRStep {
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
        steps: vec![IRStep {
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
fn cvc5_sygus_multi_pooled_system_safety_supports_forall_cross_entity_ref_binding() {
    let mut system = make_multi_pooled_system();
    system.name = "CounterMarkerForallPool".to_owned();
    system.steps[2] = IRStep {
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
fn cvc5_sygus_multi_pooled_system_safety_supports_cross_entity_ref_with_transition_args() {
    let mut system = make_multi_pooled_system();
    system.steps[2].body = vec![IRAction::Choose {
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
fn cvc5_sygus_system_safety_returns_unknown_for_int_step_params() {
    let mut system = make_counter_system();
    system.steps[0].params.push(IRTransParam {
        name: "delta".to_owned(),
        ty: IRType::Int,
    });
    let property = non_negative_property();

    let result = try_cvc5_sygus_system_safety(&system, &property, 5_000);
    assert!(
        matches!(result, Ic3Result::Unknown(ref msg) if msg.contains("only supports Bool and fieldless-enum step params")),
        "expected honest Unknown for unsupported int step params, got: {result:?}"
    );
}
