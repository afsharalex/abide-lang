//! Variable qualification — rewrite query/pred references to system-qualified names.

use std::collections::{HashMap, HashSet};

use super::super::types::{
    IRAction, IRActionMatchArm, IRActionMatchScrutinee, IRCreateField, IRExpr, IRMatchArm,
    LetBinding,
};

/// Collect variable names bound by an IR pattern (PVar, PCtor fields, POr).
pub(super) fn collect_ir_pattern_binders(
    pat: &super::super::types::IRPattern,
    bound: &mut HashSet<String>,
) {
    match pat {
        super::super::types::IRPattern::PVar { name } => {
            bound.insert(name.clone());
        }
        super::super::types::IRPattern::PCtor { fields, .. } => {
            for f in fields {
                collect_ir_pattern_binders(&f.pattern, bound);
            }
        }
        super::super::types::IRPattern::POr { left, right } => {
            collect_ir_pattern_binders(left, bound);
            collect_ir_pattern_binders(right, bound);
        }
        super::super::types::IRPattern::PWild => {}
    }
}

/// Rewrite bare `Var` names that match system query names to their
/// system-qualified form. Operates on `IRExpr` at IR lowering time,
/// so the DefEnv at verification time resolves the correct query.
///
/// Scope-aware: `bound` tracks locally bound variables (from step/query
/// params, `Lam`, `Let`, `Forall`, `Exists`, `One`, `Lone`, `VarDecl`,
/// `Aggregate`, `SetComp`, `Match` patterns, `Choose`/`ForAll` actions)
/// and does NOT rename them even if they shadow a query name.
///
/// Uses a complete recursive walk — every IRExpr variant is handled
/// so new variants cause a compile error (no catch-all).
pub(super) fn qualify_query_vars_scoped(
    expr: &IRExpr,
    renames: &HashMap<String, String>,
    bound: &HashSet<String>,
) -> IRExpr {
    let r = |e: &IRExpr| qualify_query_vars_scoped(e, renames, bound);
    match expr {
        // ── Leaf nodes ──────────────────────────────────────────────
        IRExpr::Lit { .. } | IRExpr::Sorry { .. } | IRExpr::Todo { .. } => expr.clone(),

        IRExpr::Var { name, ty, span } => {
            // Don't rename if the name is shadowed by a local binding
            if bound.contains(name) {
                expr.clone()
            } else if let Some(qualified) = renames.get(name) {
                IRExpr::Var {
                    name: qualified.clone(),
                    ty: ty.clone(),
                    span: *span,
                }
            } else {
                expr.clone()
            }
        }

        // ── Constructor — recurse into field-value args ─────────────
        IRExpr::Ctor {
            enum_name,
            ctor,
            args,
            span,
        } => IRExpr::Ctor {
            enum_name: enum_name.clone(),
            ctor: ctor.clone(),
            args: args.iter().map(|(n, v)| (n.clone(), r(v))).collect(),
            span: *span,
        },

        // ── Binary / Unary / Application ────────────────────────────
        IRExpr::BinOp {
            op,
            left,
            right,
            ty,
            span,
        } => IRExpr::BinOp {
            op: op.clone(),
            left: Box::new(r(left)),
            right: Box::new(r(right)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::UnOp {
            op,
            operand,
            ty,
            span,
        } => IRExpr::UnOp {
            op: op.clone(),
            operand: Box::new(r(operand)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::App {
            func,
            arg,
            ty,
            span,
        } => IRExpr::App {
            func: Box::new(r(func)),
            arg: Box::new(r(arg)),
            ty: ty.clone(),
            span: *span,
        },

        // ── Lambda / Let — extend bound set ─────────────────────────
        IRExpr::Lam {
            param,
            param_type,
            body,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(param.clone());
            IRExpr::Lam {
                param: param.clone(),
                param_type: param_type.clone(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                span: *span,
            }
        }
        IRExpr::Let {
            bindings,
            body,
            span,
        } => {
            let mut inner_bound = bound.clone();
            for b in bindings {
                inner_bound.insert(b.name.clone());
            }
            IRExpr::Let {
                bindings: bindings
                    .iter()
                    .map(|b| LetBinding {
                        name: b.name.clone(),
                        ty: b.ty.clone(),
                        expr: qualify_query_vars_scoped(&b.expr, renames, &inner_bound),
                    })
                    .collect(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                span: *span,
            }
        }

        // ── Quantifiers — extend bound set ──────────────────────────
        IRExpr::Forall {
            var,
            domain,
            body,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::Forall {
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                span: *span,
            }
        }
        IRExpr::Exists {
            var,
            domain,
            body,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::Exists {
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                span: *span,
            }
        }
        IRExpr::One {
            var,
            domain,
            body,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::One {
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                span: *span,
            }
        }
        IRExpr::Lone {
            var,
            domain,
            body,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::Lone {
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                span: *span,
            }
        }
        IRExpr::Choose {
            var,
            domain,
            predicate,
            ty,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::Choose {
                var: var.clone(),
                domain: domain.clone(),
                predicate: predicate
                    .as_ref()
                    .map(|pred| Box::new(qualify_query_vars_scoped(pred, renames, &inner_bound))),
                ty: ty.clone(),
                span: *span,
            }
        }

        // ── Field access / Prime ────────────────────────────────────
        IRExpr::Field {
            expr: e,
            field,
            ty,
            span,
        } => IRExpr::Field {
            expr: Box::new(r(e)),
            field: field.clone(),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::Prime { expr: e, span } => IRExpr::Prime {
            expr: Box::new(r(e)),
            span: *span,
        },

        // ── Temporal operators ──────────────────────────────────────
        IRExpr::Always { body, span } => IRExpr::Always {
            body: Box::new(r(body)),
            span: *span,
        },
        IRExpr::Eventually { body, span } => IRExpr::Eventually {
            body: Box::new(r(body)),
            span: *span,
        },
        IRExpr::Until { left, right, span } => IRExpr::Until {
            left: Box::new(r(left)),
            right: Box::new(r(right)),
            span: *span,
        },
        IRExpr::Historically { body, span } => IRExpr::Historically {
            body: Box::new(r(body)),
            span: *span,
        },
        IRExpr::Once { body, span } => IRExpr::Once {
            body: Box::new(r(body)),
            span: *span,
        },
        IRExpr::Previously { body, span } => IRExpr::Previously {
            body: Box::new(r(body)),
            span: *span,
        },
        IRExpr::Since { left, right, span } => IRExpr::Since {
            left: Box::new(r(left)),
            right: Box::new(r(right)),
            span: *span,
        },

        // ── Aggregator — var binds in body/in_filter ─────────────────
        IRExpr::Aggregate {
            kind,
            var,
            domain,
            body,
            in_filter,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::Aggregate {
                kind: *kind,
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(qualify_query_vars_scoped(body, renames, &inner_bound)),
                in_filter: in_filter
                    .as_ref()
                    .map(|f| Box::new(qualify_query_vars_scoped(f, renames, &inner_bound))),
                span: *span,
            }
        }

        // ── Saw — recurse into Some args ────────────────────────────
        IRExpr::Saw {
            system_name,
            event_name,
            args,
            span,
        } => IRExpr::Saw {
            system_name: system_name.clone(),
            event_name: event_name.clone(),
            args: args
                .iter()
                .map(|a| a.as_ref().map(|e| Box::new(r(e))))
                .collect(),
            span: *span,
        },

        // ── Match — collect pattern binders into inner scope ────────
        IRExpr::Match {
            scrutinee,
            arms,
            span,
        } => IRExpr::Match {
            scrutinee: Box::new(r(scrutinee)),
            arms: arms
                .iter()
                .map(|arm| {
                    let mut arm_bound = bound.clone();
                    collect_ir_pattern_binders(&arm.pattern, &mut arm_bound);
                    IRMatchArm {
                        pattern: arm.pattern.clone(),
                        guard: arm
                            .guard
                            .as_ref()
                            .map(|g| qualify_query_vars_scoped(g, renames, &arm_bound)),
                        body: qualify_query_vars_scoped(&arm.body, renames, &arm_bound),
                    }
                })
                .collect(),
            span: *span,
        },

        // ── Map / Index / Card ──────────────────────────────────────
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            span,
        } => IRExpr::MapUpdate {
            map: Box::new(r(map)),
            key: Box::new(r(key)),
            value: Box::new(r(value)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::Index { map, key, ty, span } => IRExpr::Index {
            map: Box::new(r(map)),
            key: Box::new(r(key)),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::Card { expr: e, span } => IRExpr::Card {
            expr: Box::new(r(e)),
            span: *span,
        },

        // ── Collection literals ─────────────────────────────────────
        IRExpr::SetLit { elements, ty, span } => IRExpr::SetLit {
            elements: elements.iter().map(&r).collect(),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::SeqLit { elements, ty, span } => IRExpr::SeqLit {
            elements: elements.iter().map(&r).collect(),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::MapLit { entries, ty, span } => IRExpr::MapLit {
            entries: entries.iter().map(|(k, v)| (r(k), r(v))).collect(),
            ty: ty.clone(),
            span: *span,
        },
        IRExpr::SetComp {
            var,
            domain,
            filter,
            projection,
            ty,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRExpr::SetComp {
                var: var.clone(),
                domain: domain.clone(),
                filter: Box::new(qualify_query_vars_scoped(filter, renames, &inner_bound)),
                projection: projection
                    .as_ref()
                    .map(|p| Box::new(qualify_query_vars_scoped(p, renames, &inner_bound))),
                ty: ty.clone(),
                span: *span,
            }
        }

        // ── Assert / Assume ─────────────────────────────────────────
        IRExpr::Assert { expr: e, span } => IRExpr::Assert {
            expr: Box::new(r(e)),
            span: *span,
        },
        IRExpr::Assume { expr: e, span } => IRExpr::Assume {
            expr: Box::new(r(e)),
            span: *span,
        },

        // ── Imperative constructs ───────────────────────────────────
        IRExpr::Block { exprs, span } => IRExpr::Block {
            exprs: exprs.iter().map(&r).collect(),
            span: *span,
        },
        IRExpr::VarDecl {
            name,
            ty,
            init,
            rest,
            span,
        } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(name.clone());
            IRExpr::VarDecl {
                name: name.clone(),
                ty: ty.clone(),
                init: Box::new(r(init)),
                rest: Box::new(qualify_query_vars_scoped(rest, renames, &inner_bound)),
                span: *span,
            }
        }
        IRExpr::While {
            cond,
            invariants,
            decreases,
            body,
            span,
        } => IRExpr::While {
            cond: Box::new(r(cond)),
            invariants: invariants.iter().map(&r).collect(),
            decreases: decreases.clone(),
            body: Box::new(r(body)),
            span: *span,
        },
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            span,
        } => IRExpr::IfElse {
            cond: Box::new(r(cond)),
            then_body: Box::new(r(then_body)),
            else_body: else_body.as_ref().map(|e| Box::new(r(e))),
            span: *span,
        },
    }
}

/// Rewrite bare query Var names inside IRAction trees.
/// Scope-aware: `bound` tracks locally bound variables from step params,
/// Choose/ForAll binders, etc.
pub(super) fn qualify_action_query_vars(
    action: &IRAction,
    renames: &HashMap<String, String>,
    bound: &HashSet<String>,
) -> IRAction {
    match action {
        IRAction::Choose {
            var,
            entity,
            filter,
            ops,
        } => {
            // Choose binds `var` in its filter and body ops
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRAction::Choose {
                var: var.clone(),
                entity: entity.clone(),
                filter: Box::new(qualify_query_vars_scoped(filter, renames, &inner_bound)),
                ops: ops
                    .iter()
                    .map(|a| qualify_action_query_vars(a, renames, &inner_bound))
                    .collect(),
            }
        }
        IRAction::ForAll { var, entity, ops } => {
            // ForAll binds `var` in its body ops
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            IRAction::ForAll {
                var: var.clone(),
                entity: entity.clone(),
                ops: ops
                    .iter()
                    .map(|a| qualify_action_query_vars(a, renames, &inner_bound))
                    .collect(),
            }
        }
        IRAction::Create { entity, fields } => IRAction::Create {
            entity: entity.clone(),
            fields: fields
                .iter()
                .map(|f| IRCreateField {
                    name: f.name.clone(),
                    value: qualify_query_vars_scoped(&f.value, renames, bound),
                })
                .collect(),
        },
        IRAction::LetCrossCall {
            name,
            system,
            command,
            args,
        } => IRAction::LetCrossCall {
            name: name.clone(),
            system: system.clone(),
            command: command.clone(),
            args: args
                .iter()
                .map(|a| qualify_query_vars_scoped(a, renames, bound))
                .collect(),
        },
        IRAction::Apply {
            target,
            transition,
            refs,
            args,
        } => IRAction::Apply {
            target: target.clone(),
            transition: transition.clone(),
            refs: refs.clone(),
            args: args
                .iter()
                .map(|a| qualify_query_vars_scoped(a, renames, bound))
                .collect(),
        },
        IRAction::CrossCall {
            system,
            command,
            args,
        } => IRAction::CrossCall {
            system: system.clone(),
            command: command.clone(),
            args: args
                .iter()
                .map(|a| qualify_query_vars_scoped(a, renames, bound))
                .collect(),
        },
        IRAction::Match { scrutinee, arms } => IRAction::Match {
            scrutinee: match scrutinee {
                IRActionMatchScrutinee::Var { name } => {
                    IRActionMatchScrutinee::Var { name: name.clone() }
                }
                IRActionMatchScrutinee::CrossCall {
                    system,
                    command,
                    args,
                } => IRActionMatchScrutinee::CrossCall {
                    system: system.clone(),
                    command: command.clone(),
                    args: args
                        .iter()
                        .map(|a| qualify_query_vars_scoped(a, renames, bound))
                        .collect(),
                },
            },
            arms: arms
                .iter()
                .map(|arm| {
                    let mut arm_bound = bound.clone();
                    collect_ir_pattern_binders(&arm.pattern, &mut arm_bound);
                    IRActionMatchArm {
                        pattern: arm.pattern.clone(),
                        guard: arm
                            .guard
                            .as_ref()
                            .map(|g| qualify_query_vars_scoped(g, renames, &arm_bound)),
                        body: arm
                            .body
                            .iter()
                            .map(|a| qualify_action_query_vars(a, renames, &arm_bound))
                            .collect(),
                    }
                })
                .collect(),
        },
        IRAction::ExprStmt { expr } => IRAction::ExprStmt {
            expr: qualify_query_vars_scoped(expr, renames, bound),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{IRFieldPat, IRPattern, IRType, LitVal};

    fn int_var(name: &str) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty: IRType::Int,
            span: None,
        }
    }

    #[test]
    fn collect_ir_pattern_binders_recurses_through_ctor_and_or_patterns() {
        let pat = IRPattern::POr {
            left: Box::new(IRPattern::PCtor {
                name: "Some".to_owned(),
                fields: vec![IRFieldPat {
                    name: "value".to_owned(),
                    pattern: IRPattern::PVar {
                        name: "x".to_owned(),
                    },
                }],
            }),
            right: Box::new(IRPattern::PVar {
                name: "y".to_owned(),
            }),
        };

        let mut bound = HashSet::new();
        collect_ir_pattern_binders(&pat, &mut bound);

        assert!(bound.contains("x"));
        assert!(bound.contains("y"));
        assert_eq!(bound.len(), 2);
    }

    #[test]
    fn qualify_query_vars_scoped_rewrites_only_free_names() {
        let mut renames = HashMap::new();
        renames.insert("payable".to_owned(), "Billing::payable".to_owned());
        renames.insert("ready".to_owned(), "Billing::ready".to_owned());

        let expr = IRExpr::Match {
            scrutinee: Box::new(int_var("payable")),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PVar {
                    name: "payable".to_owned(),
                },
                guard: Some(int_var("ready")),
                body: IRExpr::Let {
                    bindings: vec![LetBinding {
                        name: "ready".to_owned(),
                        ty: IRType::Int,
                        expr: int_var("payable"),
                    }],
                    body: Box::new(IRExpr::BinOp {
                        op: "OpAdd".to_owned(),
                        left: Box::new(int_var("ready")),
                        right: Box::new(int_var("payable")),
                        ty: IRType::Int,
                        span: None,
                    }),
                    span: None,
                },
            }],
            span: None,
        };

        let rewritten = qualify_query_vars_scoped(&expr, &renames, &HashSet::new());

        let IRExpr::Match {
            scrutinee, arms, ..
        } = rewritten
        else {
            panic!("expected Match");
        };
        assert!(matches!(
            scrutinee.as_ref(),
            IRExpr::Var { name, .. } if name == "Billing::payable"
        ));

        let arm = &arms[0];
        assert!(matches!(
            arm.guard.as_ref(),
            Some(IRExpr::Var { name, .. }) if name == "Billing::ready"
        ));

        let IRExpr::Let { bindings, body, .. } = &arm.body else {
            panic!("expected Let body");
        };
        assert!(matches!(
            &bindings[0].expr,
            IRExpr::Var { name, .. } if name == "payable"
        ));

        let IRExpr::BinOp { left, right, .. } = body.as_ref() else {
            panic!("expected BinOp in let body");
        };
        assert!(matches!(
            left.as_ref(),
            IRExpr::Var { name, .. } if name == "ready"
        ));
        assert!(matches!(
            right.as_ref(),
            IRExpr::Var { name, .. } if name == "payable"
        ));
    }

    #[test]
    fn qualify_action_query_vars_respects_choose_and_forall_binders() {
        let mut renames = HashMap::new();
        renames.insert("ready".to_owned(), "Billing::ready".to_owned());
        renames.insert("shared".to_owned(), "Billing::shared".to_owned());

        let action = IRAction::Choose {
            var: "ready".to_owned(),
            entity: "Order".to_owned(),
            filter: Box::new(int_var("ready")),
            ops: vec![
                IRAction::Create {
                    entity: "Order".to_owned(),
                    fields: vec![IRCreateField {
                        name: "status".to_owned(),
                        value: int_var("shared"),
                    }],
                },
                IRAction::ForAll {
                    var: "shared".to_owned(),
                    entity: "Order".to_owned(),
                    ops: vec![IRAction::ExprStmt {
                        expr: IRExpr::BinOp {
                            op: "OpAdd".to_owned(),
                            left: Box::new(int_var("shared")),
                            right: Box::new(int_var("ready")),
                            ty: IRType::Int,
                            span: None,
                        },
                    }],
                },
                IRAction::CrossCall {
                    system: "billing".to_owned(),
                    command: "charge".to_owned(),
                    args: vec![int_var("shared")],
                },
            ],
        };

        let rewritten = qualify_action_query_vars(&action, &renames, &HashSet::new());

        let IRAction::Choose { filter, ops, .. } = rewritten else {
            panic!("expected Choose");
        };
        assert!(matches!(
            filter.as_ref(),
            IRExpr::Var { name, .. } if name == "ready"
        ));

        let IRAction::Create { fields, .. } = &ops[0] else {
            panic!("expected Create");
        };
        assert!(matches!(
            &fields[0].value,
            IRExpr::Var { name, .. } if name == "Billing::shared"
        ));

        let IRAction::ForAll {
            ops: nested_ops, ..
        } = &ops[1]
        else {
            panic!("expected ForAll");
        };
        let IRAction::ExprStmt { expr } = &nested_ops[0] else {
            panic!("expected ExprStmt");
        };
        let IRExpr::BinOp { left, right, .. } = expr else {
            panic!("expected BinOp");
        };
        assert!(matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "shared"));
        assert!(matches!(right.as_ref(), IRExpr::Var { name, .. } if name == "ready"));

        let IRAction::CrossCall { args, .. } = &ops[2] else {
            panic!("expected CrossCall");
        };
        assert!(matches!(
            &args[0],
            IRExpr::Var { name, .. } if name == "Billing::shared"
        ));
    }

    #[test]
    fn qualify_query_vars_scoped_preserves_var_decl_binders() {
        let mut renames = HashMap::new();
        renames.insert("count".to_owned(), "Stats::count".to_owned());

        let expr = IRExpr::VarDecl {
            name: "count".to_owned(),
            ty: IRType::Int,
            init: Box::new(IRExpr::Lit {
                ty: IRType::Int,
                value: LitVal::Int { value: 1 },
                span: None,
            }),
            rest: Box::new(IRExpr::BinOp {
                op: "OpAdd".to_owned(),
                left: Box::new(int_var("count")),
                right: Box::new(IRExpr::Var {
                    name: "count_total".to_owned(),
                    ty: IRType::Int,
                    span: None,
                }),
                ty: IRType::Int,
                span: None,
            }),
            span: None,
        };

        let rewritten = qualify_query_vars_scoped(&expr, &renames, &HashSet::new());
        let IRExpr::VarDecl { rest, .. } = rewritten else {
            panic!("expected VarDecl");
        };
        let IRExpr::BinOp { left, right, .. } = rest.as_ref() else {
            panic!("expected BinOp");
        };
        assert!(matches!(left.as_ref(), IRExpr::Var { name, .. } if name == "count"));
        assert!(matches!(right.as_ref(), IRExpr::Var { name, .. } if name == "count_total"));
    }
}
