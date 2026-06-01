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

pub(super) fn lower_expr(e: &E::EExpr, ctx: &LowerCtx<'_>) -> IRExpr {
    match e {
        E::EExpr::Lit(ty, lit, sp) => IRExpr::Lit {
            ty: lower_ty(ty, ctx),
            value: lower_lit(lit),
            span: *sp,
        },
        E::EExpr::Var(ty, n, sp) => lower_var_expr(ty, n, *sp, ctx),
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
        E::EExpr::BinOp(ty, op, a, b, sp) => lower_binop_expr(ty, *op, a, b, *sp, ctx),
        E::EExpr::UnOp(ty, op, expr, sp) => IRExpr::UnOp {
            op: format!("{:?}", lower_unop(*op)),
            operand: Box::new(lower_expr(expr, ctx)),
            ty: lower_ty(ty, ctx),
            span: *sp,
        },
        E::EExpr::Call(ty, f, args, sp) => lower_call_expr(ty, f, args, *sp, ctx),
        E::EExpr::CallR(ty, f, refs, args, sp) => lower_call_ref_expr(ty, f, refs, args, *sp, ctx),
        E::EExpr::QualCall(ty, type_name, func_name, args, sp) => {
            lower_qualified_call_expr(ty, type_name, func_name, args, *sp, ctx)
        }
        E::EExpr::Qual(ty, s, n, sp) => lower_qualified_expr(ty, s, n, *sp, ctx),
        E::EExpr::Quant(_, q, v, vty, body, sp) => lower_quant_expr(*q, v, vty, body, *sp, ctx),
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
        E::EExpr::Let(binds, body, sp) => lower_let_expr(binds, body, *sp, ctx),
        E::EExpr::Lam(params, _mret, body, sp) => lower_lambda_expr(params, body, *sp, ctx),
        E::EExpr::Unresolved(n, sp) => IRExpr::Var {
            name: n.clone(),
            ty: IRType::String,
            span: *sp,
        },
        E::EExpr::TupleLit(ty, es, sp) => lower_tuple_lit_expr(ty, es, *sp, ctx),
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
        E::EExpr::Match(scrutinee, arms, sp) => lower_match_expr(scrutinee, arms, *sp, ctx),
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
        E::EExpr::SetComp(ty, proj, var, domain, source, filter, sp) => lower_set_comp_expr(
            SetCompLowering {
                ty,
                projection: proj,
                var,
                domain,
                source,
                filter,
                span: *sp,
            },
            ctx,
        ),
        E::EExpr::RelComp(ty, projection, bindings, filter, sp) => {
            lower_rel_comp_expr(ty, projection, bindings, filter, *sp, ctx)
        }
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
            lower_while_expr(cond, contracts, body, *sp, ctx)
        }
        E::EExpr::IfElse(cond, then_body, else_body, sp) => IRExpr::IfElse {
            cond: Box::new(lower_expr(cond, ctx)),
            then_body: Box::new(lower_expr(then_body, ctx)),
            else_body: else_body.as_ref().map(|e| Box::new(lower_expr(e, ctx))),
            span: *sp,
        },
        // / — arithmetic aggregators.
        E::EExpr::Aggregate(_, kind, var, domain, body, in_filter, sp) => {
            lower_aggregate_expr(*kind, var, domain, body, in_filter, *sp, ctx)
        }
        E::EExpr::Saw(_, sys, evt, args, sp) => lower_saw_expr(sys, evt, args, *sp, ctx),
        E::EExpr::CtorRecord(ty, qual, ctor_name, fields, sp) => {
            lower_ctor_record_expr(ty, qual.as_deref(), ctor_name, fields, *sp, ctx)
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

fn lower_var_expr(
    ty: &E::Ty,
    name: &str,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    if enum_constructors(ty).is_some_and(|ctors| ctors.iter().any(|ctor| ctor == name)) {
        let E::Ty::Enum(enum_name, _) = ty else {
            unreachable!("constructor lookup only succeeds for enum types");
        };
        return IRExpr::Ctor {
            enum_name: enum_name.clone(),
            ctor: name.to_owned(),
            args: vec![],
            span,
        };
    }
    IRExpr::Var {
        name: name.to_owned(),
        ty: lower_ty(ty, ctx),
        span,
    }
}

fn enum_constructors(ty: &E::Ty) -> Option<&[String]> {
    match ty {
        E::Ty::Enum(_, ctors) => Some(ctors),
        _ => None,
    }
}

fn lower_binop_expr(
    ty: &E::Ty,
    op: E::BinOp,
    left: &E::EExpr,
    right: &E::EExpr,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::BinOp {
        op: resolved_binop_name(op, left.ty(), right.ty()),
        left: Box::new(lower_expr(left, ctx)),
        right: Box::new(lower_expr(right, ctx)),
        ty: lower_ty(ty, ctx),
        span,
    }
}

fn resolved_binop_name(op: E::BinOp, left_ty: E::Ty, right_ty: E::Ty) -> String {
    match (op, left_ty, right_ty) {
        (E::BinOp::Mul, E::Ty::Set(_), E::Ty::Set(_))
        | (E::BinOp::Mul, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetIntersect".to_owned(),
        (E::BinOp::Sub, E::Ty::Set(_), E::Ty::Set(_))
        | (E::BinOp::Sub, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetDiff".to_owned(),
        (E::BinOp::Le, E::Ty::Set(_), E::Ty::Set(_))
        | (E::BinOp::Le, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetSubset".to_owned(),
        (E::BinOp::Add, E::Ty::Set(_), E::Ty::Set(_))
        | (E::BinOp::Add, E::Ty::Relation(_), E::Ty::Relation(_)) => "OpSetUnion".to_owned(),
        _ => format!("{:?}", lower_binop(op)),
    }
}

fn lower_call_expr(
    ty: &E::Ty,
    func: &E::EExpr,
    args: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    if let Some(arg) = transparent_newtype_arg(func, args, ctx) {
        return lower_expr(arg, ctx);
    }
    apply_args(lower_expr(func, ctx), args, lower_ty(ty, ctx), span, ctx)
}

fn transparent_newtype_arg<'a>(
    func: &E::EExpr,
    args: &'a [E::EExpr],
    ctx: &LowerCtx<'_>,
) -> Option<&'a E::EExpr> {
    let [arg] = args else {
        return None;
    };
    match func {
        E::EExpr::Var(_, name, _) if ctx.newtypes.contains(name.as_str()) => Some(arg),
        _ => None,
    }
}

fn lower_call_ref_expr(
    ty: &E::Ty,
    func: &E::EExpr,
    refs: &[E::EExpr],
    args: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let ir_ty = lower_ty(ty, ctx);
    let with_refs = apply_args(lower_expr(func, ctx), refs, ir_ty.clone(), span, ctx);
    apply_args(with_refs, args, ir_ty, span, ctx)
}

fn apply_args(
    base: IRExpr,
    args: &[E::EExpr],
    ty: IRType,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    args.iter().fold(base, |acc, arg| IRExpr::App {
        func: Box::new(acc),
        arg: Box::new(lower_expr(arg, ctx)),
        ty: ty.clone(),
        span,
    })
}

fn lower_qualified_call_expr(
    ty: &E::Ty,
    type_name: &str,
    func_name: &str,
    args: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    if type_name == "Rel" && func_name == "field" {
        return lower_relation_field_call(ty, type_name, func_name, args, span, ctx);
    }
    if type_name == "Rel" && func_name == "project" && args.len() >= 2 {
        return lower_relation_project_call(ty, args, span, ctx);
    }
    lower_builtin_qualified_call(ty, type_name, func_name, args, span, ctx)
}

fn lower_relation_field_call(
    ty: &E::Ty,
    type_name: &str,
    func_name: &str,
    args: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let unsupported = || {
        crate::messages::collection_op_unsupported_arity(type_name, func_name, args.len()).clone()
    };
    let lowered_store = args
        .first()
        .map(|arg| lower_expr(arg, ctx))
        .unwrap_or_else(|| IRExpr::Var {
            name: unsupported(),
            ty: lower_ty(ty, ctx),
            span,
        });
    let selector_name = match args.get(1) {
        Some(E::EExpr::Qual(_, owner, field, _)) => format!("{owner}::{field}"),
        _ => unsupported(),
    };
    IRExpr::BinOp {
        op: "OpRelationField".to_owned(),
        left: Box::new(lowered_store),
        right: Box::new(IRExpr::Var {
            name: selector_name,
            ty: IRType::String,
            span,
        }),
        ty: lower_ty(ty, ctx),
        span,
    }
}

fn lower_relation_project_call(
    ty: &E::Ty,
    args: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::BinOp {
        op: "OpRelProject".to_owned(),
        left: Box::new(lower_expr(&args[0], ctx)),
        right: Box::new(lower_relation_projection_columns(&args[1..], span, ctx)),
        ty: lower_ty(ty, ctx),
        span,
    }
}

fn lower_relation_projection_columns(
    columns: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    if let [column] = columns {
        return lower_expr(column, ctx);
    }
    let lowered_columns: Vec<IRExpr> = columns.iter().map(|arg| lower_expr(arg, ctx)).collect();
    let tuple_ty = IRType::Tuple {
        elements: vec![IRType::Int; lowered_columns.len()],
    };
    lowered_columns.into_iter().fold(
        IRExpr::Var {
            name: "Tuple".to_owned(),
            ty: tuple_ty.clone(),
            span,
        },
        |acc, arg| IRExpr::App {
            func: Box::new(acc),
            arg: Box::new(arg),
            ty: tuple_ty.clone(),
            span,
        },
    )
}

fn lower_builtin_qualified_call(
    ty: &E::Ty,
    type_name: &str,
    func_name: &str,
    args: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let op = format!("Op{type_name}{}", capitalize(func_name));
    let lowered_args: Vec<IRExpr> = args.iter().map(|arg| lower_expr(arg, ctx)).collect();
    match lowered_args.as_slice() {
        [_] => IRExpr::UnOp {
            op,
            operand: Box::new(lowered_args.into_iter().next().unwrap()),
            ty: lower_ty(ty, ctx),
            span,
        },
        [_, _] => {
            let mut iter = lowered_args.into_iter();
            IRExpr::BinOp {
                op,
                left: Box::new(iter.next().unwrap()),
                right: Box::new(iter.next().unwrap()),
                ty: lower_ty(ty, ctx),
                span,
            }
        }
        [] | [_, _, ..] => IRExpr::Var {
            name: crate::messages::collection_op_unsupported_arity(
                type_name,
                func_name,
                lowered_args.len(),
            )
            .clone(),
            ty: lower_ty(ty, ctx),
            span,
        },
    }
}

fn lower_qualified_expr(
    ty: &E::Ty,
    scope: &str,
    name: &str,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    if enum_constructors(ty).is_some_and(|ctors| ctors.iter().any(|ctor| ctor == name)) {
        let E::Ty::Enum(enum_name, _) = ty else {
            unreachable!("constructor lookup only succeeds for enum types");
        };
        return IRExpr::Ctor {
            enum_name: enum_name.clone(),
            ctor: name.to_owned(),
            args: vec![],
            span,
        };
    }
    IRExpr::Var {
        name: format!("{scope}::{name}"),
        ty: lower_ty(ty, ctx),
        span,
    }
}

fn lower_quant_expr(
    quantifier: E::Quantifier,
    var: &str,
    var_ty: &E::Ty,
    body: &E::EExpr,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let lowered = lower_expr(body, ctx);
    let domain = lower_ty(var_ty, ctx);
    match quantifier {
        E::Quantifier::All => IRExpr::Forall {
            var: var.to_owned(),
            domain,
            body: Box::new(lowered),
            span,
        },
        E::Quantifier::Exists | E::Quantifier::Some => IRExpr::Exists {
            var: var.to_owned(),
            domain,
            body: Box::new(lowered),
            span,
        },
        E::Quantifier::One => IRExpr::One {
            var: var.to_owned(),
            domain,
            body: Box::new(lowered),
            span,
        },
        E::Quantifier::Lone => IRExpr::Lone {
            var: var.to_owned(),
            domain,
            body: Box::new(lowered),
            span,
        },
        E::Quantifier::No => IRExpr::UnOp {
            op: "OpNot".to_owned(),
            operand: Box::new(IRExpr::Exists {
                var: var.to_owned(),
                domain,
                body: Box::new(lowered),
                span,
            }),
            ty: IRType::Bool,
            span,
        },
    }
}

fn lower_let_expr(
    binds: &[(String, Option<E::Ty>, E::EExpr)],
    body: &E::EExpr,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::Let {
        bindings: binds
            .iter()
            .map(|(name, ty, expr)| LetBinding {
                name: name.clone(),
                ty: ty.as_ref().map_or(IRType::String, |ty| lower_ty(ty, ctx)),
                expr: lower_expr(expr, ctx),
            })
            .collect(),
        body: Box::new(lower_expr(body, ctx)),
        span,
    }
}

fn lower_lambda_expr(
    params: &[(String, E::Ty)],
    body: &E::EExpr,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    if params.is_empty() {
        return lower_expr(body, ctx);
    }
    params
        .iter()
        .rev()
        .fold(lower_expr(body, ctx), |acc, (param, ty)| IRExpr::Lam {
            param: param.clone(),
            param_type: lower_ty(ty, ctx),
            body: Box::new(acc),
            span,
        })
}

fn lower_tuple_lit_expr(
    ty: &E::Ty,
    elements: &[E::EExpr],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let tuple_ty = lower_ty(ty, ctx);
    let tuple_ctor = IRExpr::Var {
        name: "Tuple".to_owned(),
        ty: tuple_ty.clone(),
        span,
    };
    elements
        .iter()
        .map(|element| lower_expr(element, ctx))
        .fold(tuple_ctor, |acc, arg| IRExpr::App {
            func: Box::new(acc),
            arg: Box::new(arg),
            ty: tuple_ty.clone(),
            span,
        })
}

fn lower_match_expr(
    scrutinee: &E::EExpr,
    arms: &[(E::EPattern, Option<E::EExpr>, E::EExpr)],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let scrutinee_ty = scrutinee.ty();
    IRExpr::Match {
        scrutinee: Box::new(lower_expr(scrutinee, ctx)),
        arms: arms
            .iter()
            .map(|(pat, guard, body)| IRMatchArm {
                pattern: lower_pattern_for_scrutinee(pat, &scrutinee_ty),
                guard: guard.as_ref().map(|guard| lower_expr(guard, ctx)),
                body: lower_expr(body, ctx),
            })
            .collect(),
        span,
    }
}

struct SetCompLowering<'a> {
    ty: &'a E::Ty,
    projection: &'a Option<Box<E::EExpr>>,
    var: &'a str,
    domain: &'a E::Ty,
    source: &'a Option<Box<E::EExpr>>,
    filter: &'a E::EExpr,
    span: Option<crate::span::Span>,
}

fn lower_set_comp_expr(input: SetCompLowering<'_>, ctx: &LowerCtx<'_>) -> IRExpr {
    IRExpr::SetComp {
        var: input.var.to_owned(),
        domain: lower_ty(input.domain, ctx),
        source: input
            .source
            .as_ref()
            .map(|source| Box::new(lower_expr(source, ctx))),
        filter: Box::new(lower_expr(input.filter, ctx)),
        projection: input
            .projection
            .as_ref()
            .map(|projection| Box::new(lower_expr(projection, ctx))),
        ty: lower_ty(input.ty, ctx),
        span: input.span,
    }
}

fn lower_rel_comp_expr(
    ty: &E::Ty,
    projection: &E::EExpr,
    bindings: &[E::ERelCompBinding],
    filter: &E::EExpr,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::RelComp {
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
        span,
    }
}

fn lower_while_expr(
    cond: &E::EExpr,
    contracts: &[E::EContract],
    body: &E::EExpr,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    let (invariants, decreases) = lower_while_contracts(contracts, ctx);
    IRExpr::While {
        cond: Box::new(lower_expr(cond, ctx)),
        invariants,
        decreases,
        body: Box::new(lower_expr(body, ctx)),
        span,
    }
}

fn lower_aggregate_expr(
    kind: crate::ast::AggKind,
    var: &str,
    domain: &E::Ty,
    body: &E::EExpr,
    in_filter: &Option<Box<E::EExpr>>,
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::Aggregate {
        kind: lower_agg_kind(kind),
        var: var.to_owned(),
        domain: lower_ty(domain, ctx),
        body: Box::new(lower_expr(body, ctx)),
        in_filter: in_filter
            .as_ref()
            .map(|filter| Box::new(lower_expr(filter, ctx))),
        span,
    }
}

fn lower_agg_kind(kind: crate::ast::AggKind) -> IRAggKind {
    match kind {
        crate::ast::AggKind::Sum => IRAggKind::Sum,
        crate::ast::AggKind::Product => IRAggKind::Product,
        crate::ast::AggKind::Min => IRAggKind::Min,
        crate::ast::AggKind::Max => IRAggKind::Max,
        crate::ast::AggKind::Count => IRAggKind::Count,
    }
}

fn lower_saw_expr(
    system_name: &str,
    event_name: &str,
    args: &[Option<Box<E::EExpr>>],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::Saw {
        system_name: system_name.to_owned(),
        event_name: event_name.to_owned(),
        args: args
            .iter()
            .map(|arg| arg.as_ref().map(|expr| Box::new(lower_expr(expr, ctx))))
            .collect(),
        span,
    }
}

fn lower_ctor_record_expr(
    ty: &E::Ty,
    qualifier: Option<&str>,
    ctor_name: &str,
    fields: &[(String, E::EExpr)],
    span: Option<crate::span::Span>,
    ctx: &LowerCtx<'_>,
) -> IRExpr {
    IRExpr::Ctor {
        enum_name: resolve_ctor_record_enum_name(ty, qualifier, ctor_name, ctx),
        ctor: ctor_name.to_owned(),
        args: fields
            .iter()
            .map(|(field, expr)| (field.clone(), lower_expr(expr, ctx)))
            .collect(),
        span,
    }
}

fn resolve_ctor_record_enum_name(
    ty: &E::Ty,
    qualifier: Option<&str>,
    ctor_name: &str,
    ctx: &LowerCtx<'_>,
) -> String {
    if let Some(qualifier) = qualifier {
        return qualifier.to_owned();
    }
    if let E::Ty::Enum(enum_name, _) = ty {
        return enum_name.clone();
    }
    ctx.variants
        .keys()
        .find(|enum_name| variant_list_contains_ctor(ctx, enum_name, ctor_name))
        .cloned()
        .unwrap_or_default()
}

fn variant_list_contains_ctor(ctx: &LowerCtx<'_>, enum_name: &str, ctor_name: &str) -> bool {
    ctx.variants.get(enum_name).is_some_and(|variants| {
        variants.iter().any(|variant| match variant {
            E::EVariant::Simple(name)
            | E::EVariant::Record(name, _)
            | E::EVariant::Param(name, _) => name == ctor_name,
        })
    })
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
