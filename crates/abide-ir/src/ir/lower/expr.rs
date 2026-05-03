//! Expression lowering — EExpr to IRExpr.

use super::super::types::{
    IRAggKind, IRExpr, IRFieldPat, IRMatchArm, IRPattern, IRRelCompBinding, IRType, LetBinding,
    LitVal,
};
use super::{lower_ty, lower_while_contracts, LowerCtx};
use crate::elab::types as E;

pub(super) fn card_from_text(s: Option<&str>) -> super::super::types::Cardinality {
    use super::super::types::Cardinality;
    match s {
        None | Some("one") => Cardinality::Named("one".to_owned()),
        Some("lone") => Cardinality::Named("lone".to_owned()),
        Some("some") => Cardinality::Named("some".to_owned()),
        Some("no") => Cardinality::Named("no".to_owned()),
        Some(n) => match n.parse::<i64>() {
            Ok(i) => Cardinality::Exact { exactly: i },
            Err(_) => Cardinality::Named("one".to_owned()),
        },
    }
}

pub(super) fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().to_string() + c.as_str(),
    }
}

#[allow(clippy::too_many_lines)]
pub(super) fn lower_expr(e: &E::EExpr, ctx: &LowerCtx<'_>) -> IRExpr {
    match e {
        E::EExpr::Lit(ty, lit, sp) => IRExpr::Lit {
            ty: lower_ty(ty, ctx),
            value: lower_lit(lit),
            span: *sp,
        },
        E::EExpr::Var(ty, n, sp) => {
            // Check if this is a constructor of an enum type
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                        args: vec![],
                        span: *sp,
                    };
                }
            }
            IRExpr::Var {
                name: n.clone(),
                ty: lower_ty(ty, ctx),
                span: *sp,
            }
        }
        E::EExpr::Field(ty, expr, f, sp) => IRExpr::Field {
            expr: Box::new(lower_expr(expr, ctx)),
            field: f.clone(),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Prime(_, expr, sp) => IRExpr::Prime {
            expr: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::BinOp(ty, op, a, b, sp) => {
            // Type-directed operator overloading: when both operands have
            // Set type, override arithmetic ops to set ops. This is done HERE
            // (not in the SMT layer) because the elaborated types distinguish
            // Set<T> from Map<K,Bool> and Seq<Bool>, which are all Array<_,Bool>
            // at the SMT level.
            let resolved_op = match (op, a.ty(), b.ty()) {
                (E::BinOp::Mul, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetIntersect".to_owned(),
                (E::BinOp::Sub, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetDiff".to_owned(),
                (E::BinOp::Le, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetSubset".to_owned(),
                (E::BinOp::Add, E::Ty::Set(_), E::Ty::Set(_)) => "OpSetUnion".to_owned(),
                (E::BinOp::Mul, E::Ty::Relation(_), E::Ty::Relation(_)) => {
                    "OpSetIntersect".to_owned()
                }
                (E::BinOp::Sub, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetDiff".to_owned(),
                (E::BinOp::Le, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetSubset".to_owned(),
                (E::BinOp::Add, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetUnion".to_owned(),
                _ => format!("{:?}", lower_binop(*op)),
            };
            IRExpr::BinOp {
                op: resolved_op,
                left: Box::new(lower_expr(a, ctx)),
                right: Box::new(lower_expr(b, ctx)),
                ty: lower_ty(ty, ctx),
                span: *sp,
            }
        }
        E::EExpr::UnOp(ty, op, expr, sp) => IRExpr::UnOp {
            op: format!("{:?}", lower_unop(*op)),
            operand: Box::new(lower_expr(expr, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Call(ty, f, args, sp) => {
            // Newtype constructor calls are transparent: UserId("x") → "x".
            // The constructor is an identity function, so just lower the arg.
            if args.len() == 1 {
                if let E::EExpr::Var(_, name, _) = f.as_ref() {
                    if ctx.newtypes.contains(name.as_str()) {
                        return lower_expr(&args[0], ctx);
                    }
                }
            }
            let lowered_f = lower_expr(f, ctx);
            let ir_ty = lower_ty(ty, ctx);
            let outer_span = *sp;
            args.iter().fold(lowered_f, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg, ctx)),
                ty: ir_ty.clone(),
                span: outer_span,
            })
        }
        E::EExpr::CallR(ty, f, refs, args, sp) => {
            let lowered_f = lower_expr(f, ctx);
            let ir_ty = lower_ty(ty, ctx);
            let outer_span = *sp;
            let with_refs = refs.iter().fold(lowered_f, |acc, r| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(r, ctx)),
                ty: ir_ty.clone(),
                span: outer_span,
            });
            args.iter().fold(with_refs, |acc, arg| IRExpr::App {
                func: Box::new(acc),
                arg: Box::new(lower_expr(arg, ctx)),
                ty: ir_ty.clone(),
                span: outer_span,
            })
        }
        E::EExpr::QualCall(ty, type_name, func_name, args, sp) => {
            if type_name == "Rel" && func_name == "field" {
                let lowered_store =
                    args.first()
                        .map(|arg| lower_expr(arg, ctx))
                        .unwrap_or_else(|| IRExpr::Var {
                            name: crate::messages::collection_op_unsupported_arity(
                                type_name,
                                func_name,
                                args.len(),
                            )
                            .clone(),
                            ty: lower_ty(ty, ctx),
                            span: *sp,
                        });
                let selector_name = match args.get(1) {
                    Some(E::EExpr::Qual(_, owner, field, _)) => format!("{owner}::{field}"),
                    _ => crate::messages::collection_op_unsupported_arity(
                        type_name,
                        func_name,
                        args.len(),
                    )
                    .clone(),
                };
                return IRExpr::BinOp {
                    op: "OpRelationField".to_owned(),
                    left: Box::new(lowered_store),
                    right: Box::new(IRExpr::Var {
                        name: selector_name,
                        ty: IRType::String,
                        span: *sp,
                    }),
                    ty: lower_ty(ty, ctx),
                    span: *sp,
                };
            }
            if type_name == "Rel" && func_name == "project" && args.len() >= 2 {
                let relation = lower_expr(&args[0], ctx);
                let columns = if args.len() == 2 {
                    lower_expr(&args[1], ctx)
                } else {
                    let lowered_columns: Vec<IRExpr> =
                        args[1..].iter().map(|arg| lower_expr(arg, ctx)).collect();
                    let tuple_ty = IRType::Tuple {
                        elements: vec![IRType::Int; lowered_columns.len()],
                    };
                    lowered_columns.into_iter().fold(
                        IRExpr::Var {
                            name: "Tuple".to_owned(),
                            ty: tuple_ty.clone(),
                            span: *sp,
                        },
                        |acc, arg| IRExpr::App {
                            func: Box::new(acc),
                            arg: Box::new(arg),
                            ty: tuple_ty.clone(),
                            span: *sp,
                        },
                    )
                };
                return IRExpr::BinOp {
                    op: "OpRelProject".to_owned(),
                    left: Box::new(relation),
                    right: Box::new(columns),
                    ty: lower_ty(ty, ctx),
                    span: *sp,
                };
            }
            let op = format!("Op{type_name}{}", capitalize(func_name));
            let lowered_args: Vec<IRExpr> = args.iter().map(|a| lower_expr(a, ctx)).collect();
            match lowered_args.len() {
                1 => IRExpr::UnOp {
                    op,
                    operand: Box::new(lowered_args.into_iter().next().unwrap()),
                    ty: lower_ty(ty, ctx),
                    span: *sp,
                },
                2 => {
                    let mut iter = lowered_args.into_iter();
                    IRExpr::BinOp {
                        op,
                        left: Box::new(iter.next().unwrap()),
                        right: Box::new(iter.next().unwrap()),
                        ty: lower_ty(ty, ctx),
                        span: *sp,
                    }
                }
                0 | 3.. => {
                    // Emit the qualified call name as a Var so the verifier
                    // reports a clear error rather than silently mislowering.
                    IRExpr::Var {
                        name: crate::messages::collection_op_unsupported_arity(
                            type_name,
                            func_name,
                            lowered_args.len(),
                        )
                        .clone(),
                        ty: lower_ty(ty, ctx),
                        span: *sp,
                    }
                }
            }
        }
        E::EExpr::Qual(ty, s, n, sp) => {
            if let E::Ty::Enum(enum_name, ctors) = ty {
                if ctors.contains(n) {
                    return IRExpr::Ctor {
                        enum_name: enum_name.clone(),
                        ctor: n.clone(),
                        args: vec![],
                        span: *sp,
                    };
                }
            }
            IRExpr::Var {
                name: format!("{s}::{n}"),
                ty: lower_ty(ty, ctx),
                span: *sp,
            }
        }
        E::EExpr::Quant(_, q, v, vty, body, sp) => {
            let lowered = lower_expr(body, ctx);
            let vt = lower_ty(vty, ctx);
            match q {
                E::Quantifier::All => IRExpr::Forall {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::Exists | E::Quantifier::Some => IRExpr::Exists {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::One => IRExpr::One {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::Lone => IRExpr::Lone {
                    var: v.clone(),
                    domain: vt,
                    body: Box::new(lowered),
                    span: *sp,
                },
                E::Quantifier::No => IRExpr::UnOp {
                    op: "OpNot".to_owned(),
                    operand: Box::new(IRExpr::Exists {
                        var: v.clone(),
                        domain: vt,
                        body: Box::new(lowered),
                        span: *sp,
                    }),
                    ty: IRType::Bool,
                    span: *sp,
                },
            }
        }
        E::EExpr::Always(_, expr, sp) => IRExpr::Always {
            body: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Eventually(_, expr, sp) => IRExpr::Eventually {
            body: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Until(_, left, right, sp) => IRExpr::Until {
            left: Box::new(lower_expr(left, ctx)),
            right: Box::new(lower_expr(right, ctx)),
            span: *sp,
        },
        // / — past-time temporal operators.
        E::EExpr::Historically(_, expr, sp) => IRExpr::Historically {
            body: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Once(_, expr, sp) => IRExpr::Once {
            body: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Previously(_, expr, sp) => IRExpr::Previously {
            body: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Since(_, left, right, sp) => IRExpr::Since {
            left: Box::new(lower_expr(left, ctx)),
            right: Box::new(lower_expr(right, ctx)),
            span: *sp,
        },
        E::EExpr::Assert(_, expr, sp) => IRExpr::Assert {
            expr: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Assume(_, expr, sp) => IRExpr::Assume {
            expr: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::NamedPair(_, _, expr, _) => lower_expr(expr, ctx),
        E::EExpr::Assign(_, lhs, rhs, sp) => IRExpr::BinOp {
            op: "OpEq".to_owned(),
            left: Box::new(lower_expr(lhs, ctx)),
            right: Box::new(lower_expr(rhs, ctx)),
            ty: IRType::Bool,
            span: *sp,
        },
        E::EExpr::Seq(ty, a, b, sp) => IRExpr::BinOp {
            op: "OpSeq".to_owned(),
            left: Box::new(lower_expr(a, ctx)),
            right: Box::new(lower_expr(b, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::SameStep(ty, a, b, sp) => IRExpr::BinOp {
            op: "OpSameStep".to_owned(),
            left: Box::new(lower_expr(a, ctx)),
            right: Box::new(lower_expr(b, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Let(binds, body, sp) => {
            let bs = binds
                .iter()
                .map(|(n, mt, e)| LetBinding {
                    name: n.clone(),
                    ty: mt.as_ref().map_or(IRType::String, |t| lower_ty(t, ctx)),
                    expr: lower_expr(e, ctx),
                })
                .collect();
            IRExpr::Let {
                bindings: bs,
                body: Box::new(lower_expr(body, ctx)),
                span: *sp,
            }
        }
        E::EExpr::Lam(params, _mret, body, sp) => {
            if params.is_empty() {
                return lower_expr(body, ctx);
            }
            params
                .iter()
                .rev()
                .fold(lower_expr(body, ctx), |acc, (pn, pt)| IRExpr::Lam {
                    param: pn.clone(),
                    param_type: lower_ty(pt, ctx),
                    body: Box::new(acc),
                    span: *sp,
                })
        }
        E::EExpr::Unresolved(n, sp) => IRExpr::Var {
            name: n.clone(),
            ty: IRType::String,
            span: *sp,
        },
        E::EExpr::TupleLit(ty, es, sp) => {
            let lowered: Vec<IRExpr> = es.iter().map(|e| lower_expr(e, ctx)).collect();
            let tuple_ty = lower_ty(ty, ctx);
            let outer_span = *sp;
            lowered.into_iter().fold(
                IRExpr::Var {
                    name: "Tuple".to_owned(),
                    ty: tuple_ty.clone(),
                    span: outer_span,
                },
                |acc, arg| IRExpr::App {
                    func: Box::new(acc),
                    arg: Box::new(arg),
                    ty: tuple_ty.clone(),
                    span: outer_span,
                },
            )
        }
        E::EExpr::In(_ty, e, s, sp) => {
            // `e in S` → `Index(S, e)` which returns Bool (Set<T> = Array<T, Bool>)
            IRExpr::Index {
                map: Box::new(lower_expr(s, ctx)),
                key: Box::new(lower_expr(e, ctx)),
                ty: IRType::Bool,
                span: *sp,
            }
        }
        E::EExpr::Card(_ty, expr, sp) => IRExpr::Card {
            expr: Box::new(lower_expr(expr, ctx)),
            span: *sp,
        },
        E::EExpr::Pipe(ty, a, f, sp) => IRExpr::App {
            func: Box::new(lower_expr(f, ctx)),
            arg: Box::new(lower_expr(a, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Match(scrutinee, arms, sp) => {
            let scrut_ty = scrutinee.ty();
            IRExpr::Match {
                scrutinee: Box::new(lower_expr(scrutinee, ctx)),
                arms: arms
                    .iter()
                    .map(|(pat, guard, body)| IRMatchArm {
                        pattern: lower_pattern_for_scrutinee(pat, &scrut_ty),
                        guard: guard.as_ref().map(|g| lower_expr(g, ctx)),
                        body: lower_expr(body, ctx),
                    })
                    .collect(),
                span: *sp,
            }
        }
        E::EExpr::Choose(ty, binder, domain_ty, predicate, sp) => IRExpr::Choose {
            var: binder.clone(),
            domain: lower_ty(domain_ty, ctx),
            predicate: predicate
                .as_ref()
                .map(|pred| Box::new(lower_expr(pred, ctx))),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::MapUpdate(ty, m, k, v, sp) => IRExpr::MapUpdate {
            map: Box::new(lower_expr(m, ctx)),
            key: Box::new(lower_expr(k, ctx)),
            value: Box::new(lower_expr(v, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Index(ty, m, k, sp) => IRExpr::Index {
            map: Box::new(lower_expr(m, ctx)),
            key: Box::new(lower_expr(k, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::SetComp(ty, proj, var, domain, source, filter, sp) => IRExpr::SetComp {
            var: var.clone(),
            domain: lower_ty(domain, ctx),
            source: source
                .as_ref()
                .map(|source| Box::new(lower_expr(source, ctx))),
            filter: Box::new(lower_expr(filter, ctx)),
            projection: proj.as_ref().map(|p| Box::new(lower_expr(p, ctx))),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::RelComp(ty, projection, bindings, filter, sp) => IRExpr::RelComp {
            projection: Box::new(lower_expr(projection, ctx)),
            bindings: bindings
                .iter()
                .map(|binding| IRRelCompBinding {
                    var: binding.var.clone(),
                    domain: lower_ty(&binding.domain, ctx),
                    source: binding
                        .source
                        .as_ref()
                        .map(|source| Box::new(lower_expr(source, ctx))),
                })
                .collect(),
            filter: Box::new(lower_expr(filter, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::SetLit(ty, elems, sp) => IRExpr::SetLit {
            elements: elems.iter().map(|e| lower_expr(e, ctx)).collect(),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::SeqLit(ty, elems, sp) => IRExpr::SeqLit {
            elements: elems.iter().map(|e| lower_expr(e, ctx)).collect(),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::MapLit(ty, entries, sp) => IRExpr::MapLit {
            entries: entries
                .iter()
                .map(|(k, v)| (lower_expr(k, ctx), lower_expr(v, ctx)))
                .collect(),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Sorry(sp) => IRExpr::Sorry { span: *sp },
        E::EExpr::Todo(sp) => IRExpr::Todo { span: *sp },
        // Imperative constructs
        E::EExpr::Block(items, sp) => IRExpr::Block {
            exprs: items.iter().map(|e| lower_expr(e, ctx)).collect(),
            span: *sp,
        },
        E::EExpr::VarDecl(name, ty, init, rest, sp) => IRExpr::VarDecl {
            name: name.clone(),
            ty: ty.as_ref().map_or(IRType::String, |t| lower_ty(t, ctx)),
            init: Box::new(lower_expr(init, ctx)),
            rest: Box::new(lower_expr(rest, ctx)),
            span: *sp,
        },
        E::EExpr::While(cond, contracts, body, sp) => {
            let (invariants, decreases) = lower_while_contracts(contracts, ctx);
            IRExpr::While {
                cond: Box::new(lower_expr(cond, ctx)),
                invariants,
                decreases,
                body: Box::new(lower_expr(body, ctx)),
                span: *sp,
            }
        }
        E::EExpr::IfElse(cond, then_body, else_body, sp) => IRExpr::IfElse {
            cond: Box::new(lower_expr(cond, ctx)),
            then_body: Box::new(lower_expr(then_body, ctx)),
            else_body: else_body.as_ref().map(|e| Box::new(lower_expr(e, ctx))),
            span: *sp,
        },
        // / — arithmetic aggregators.
        E::EExpr::Aggregate(_, kind, var, domain, body, in_filter, sp) => {
            let ir_kind = match kind {
                crate::ast::AggKind::Sum => IRAggKind::Sum,
                crate::ast::AggKind::Product => IRAggKind::Product,
                crate::ast::AggKind::Min => IRAggKind::Min,
                crate::ast::AggKind::Max => IRAggKind::Max,
                crate::ast::AggKind::Count => IRAggKind::Count,
            };
            IRExpr::Aggregate {
                kind: ir_kind,
                var: var.clone(),
                domain: lower_ty(domain, ctx),
                body: Box::new(lower_expr(body, ctx)),
                in_filter: in_filter.as_ref().map(|f| Box::new(lower_expr(f, ctx))),
                span: *sp,
            }
        }
        // / — saw operator.
        E::EExpr::Saw(_, sys, evt, args, sp) => IRExpr::Saw {
            system_name: sys.clone(),
            event_name: evt.clone(),
            args: args
                .iter()
                .map(|a| a.as_ref().map(|e| Box::new(lower_expr(e, ctx))))
                .collect(),
            span: *sp,
        },
        E::EExpr::CtorRecord(ty, qual, ctor_name, fields, sp) => {
            // Determine the enum name from the qualifier or the resolved type
            let enum_name = if let Some(q) = qual {
                q.clone()
            } else if let E::Ty::Enum(en, _) = ty {
                en.clone()
            } else {
                // Search through known enum types for this constructor name
                ctx.variants
                    .keys()
                    .find(|ename| {
                        ctx.variants.get(*ename).is_some_and(|variants| {
                            variants.iter().any(|v| match v {
                                E::EVariant::Simple(n)
                                | E::EVariant::Record(n, _)
                                | E::EVariant::Param(n, _) => n == ctor_name,
                            })
                        })
                    })
                    .cloned()
                    .unwrap_or_default()
            };
            IRExpr::Ctor {
                enum_name,
                ctor: ctor_name.clone(),
                args: fields
                    .iter()
                    .map(|(fname, fexpr)| (fname.clone(), lower_expr(fexpr, ctx)))
                    .collect(),
                span: *sp,
            }
        }
        E::EExpr::StructCtor(_, name, _, sp) => {
            // StructCtor should only appear in system field defaults, where
            // flatten_system_fields() destructures it. If we reach here,
            // the elab check pass failed to reject a StructCtor in a
            // general expression position.
            panic!(
                "internal: StructCtor `{name}` reached lower_expr (should have been rejected at elab check; span={sp:?})"
            )
        }
    }
}

pub(super) fn lower_pattern(pat: &E::EPattern) -> IRPattern {
    match pat {
        E::EPattern::Var(name) => IRPattern::PVar { name: name.clone() },
        E::EPattern::Ctor(name, fields) => IRPattern::PCtor {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(fname, fpat)| IRFieldPat {
                    name: fname.clone(),
                    pattern: lower_pattern(fpat),
                })
                .collect(),
        },
        E::EPattern::Wild => IRPattern::PWild,
        E::EPattern::Or(left, right) => IRPattern::POr {
            left: Box::new(lower_pattern(left)),
            right: Box::new(lower_pattern(right)),
        },
    }
}

fn lower_pattern_for_scrutinee(pat: &E::EPattern, scrutinee_ty: &E::Ty) -> IRPattern {
    match pat {
        E::EPattern::Var(name) if enum_contains_constructor(scrutinee_ty, name) => {
            IRPattern::PCtor {
                name: name.clone(),
                fields: Vec::new(),
            }
        }
        E::EPattern::Or(left, right) => IRPattern::POr {
            left: Box::new(lower_pattern_for_scrutinee(left, scrutinee_ty)),
            right: Box::new(lower_pattern_for_scrutinee(right, scrutinee_ty)),
        },
        _ => lower_pattern(pat),
    }
}

fn enum_contains_constructor(ty: &E::Ty, name: &str) -> bool {
    match ty {
        E::Ty::Enum(_, constructors) => constructors.iter().any(|ctor| ctor == name),
        E::Ty::Alias(_, inner) | E::Ty::Refinement(inner, _) => {
            enum_contains_constructor(inner, name)
        }
        _ => false,
    }
}

pub(super) fn lower_lit(lit: &E::Literal) -> LitVal {
    match lit {
        E::Literal::Int(i) => LitVal::Int { value: *i },
        E::Literal::Real(d) => LitVal::Real { value: *d },
        E::Literal::Float(d) => LitVal::Float { value: *d },
        E::Literal::Str(s) => LitVal::Str { value: s.clone() },
        E::Literal::Bool(b) => LitVal::Bool { value: *b },
    }
}

/// Operator names match Haskell's `show` output for differential testing.
#[allow(clippy::enum_variant_names)]
enum IRBinOp {
    OpAdd,
    OpSub,
    OpMul,
    OpDiv,
    OpMod,
    OpEq,
    OpNEq,
    OpLt,
    OpGt,
    OpLe,
    OpGe,
    OpAnd,
    OpOr,
    OpImplies,
    OpUnord,
    OpConc,
    OpXor,
    OpDiamond,
    OpDisjoint,
}

impl std::fmt::Debug for IRBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OpAdd => write!(f, "OpAdd"),
            Self::OpSub => write!(f, "OpSub"),
            Self::OpMul => write!(f, "OpMul"),
            Self::OpDiv => write!(f, "OpDiv"),
            Self::OpMod => write!(f, "OpMod"),
            Self::OpEq => write!(f, "OpEq"),
            Self::OpNEq => write!(f, "OpNEq"),
            Self::OpLt => write!(f, "OpLt"),
            Self::OpGt => write!(f, "OpGt"),
            Self::OpLe => write!(f, "OpLe"),
            Self::OpGe => write!(f, "OpGe"),
            Self::OpAnd => write!(f, "OpAnd"),
            Self::OpOr => write!(f, "OpOr"),
            Self::OpImplies => write!(f, "OpImplies"),
            Self::OpUnord => write!(f, "OpUnord"),
            Self::OpConc => write!(f, "OpConc"),
            Self::OpXor => write!(f, "OpXor"),
            Self::OpDiamond => write!(f, "OpDiamond"),
            Self::OpDisjoint => write!(f, "OpDisjoint"),
        }
    }
}

fn lower_binop(op: E::BinOp) -> IRBinOp {
    match op {
        E::BinOp::Add => IRBinOp::OpAdd,
        E::BinOp::Sub => IRBinOp::OpSub,
        E::BinOp::Mul => IRBinOp::OpMul,
        E::BinOp::Div => IRBinOp::OpDiv,
        E::BinOp::Mod => IRBinOp::OpMod,
        E::BinOp::Eq => IRBinOp::OpEq,
        E::BinOp::NEq => IRBinOp::OpNEq,
        E::BinOp::Lt => IRBinOp::OpLt,
        E::BinOp::Gt => IRBinOp::OpGt,
        E::BinOp::Le => IRBinOp::OpLe,
        E::BinOp::Ge => IRBinOp::OpGe,
        E::BinOp::And => IRBinOp::OpAnd,
        E::BinOp::Or => IRBinOp::OpOr,
        E::BinOp::Implies => IRBinOp::OpImplies,
        E::BinOp::Unord => IRBinOp::OpUnord,
        E::BinOp::Conc => IRBinOp::OpConc,
        E::BinOp::Xor => IRBinOp::OpXor,
        E::BinOp::Diamond => IRBinOp::OpDiamond,
        E::BinOp::Disjoint => IRBinOp::OpDisjoint,
    }
}

#[allow(clippy::enum_variant_names)]
enum IRUnOp {
    OpNot,
    OpNeg,
}

impl std::fmt::Debug for IRUnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OpNot => write!(f, "OpNot"),
            Self::OpNeg => write!(f, "OpNeg"),
        }
    }
}

fn lower_unop(op: E::UnOp) -> IRUnOp {
    match op {
        E::UnOp::Not => IRUnOp::OpNot,
        E::UnOp::Neg => IRUnOp::OpNeg,
    }
}
