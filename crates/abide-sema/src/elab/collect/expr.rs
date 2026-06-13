//! Expression collection — AST expressions to elaborated expressions.

use super::resolve_type_ref;
use crate::ast;
use crate::elab::types::{
    BinOp, BuiltinTy, EContract, EExpr, EPattern, ERelCompBinding, ESetCompBinder, Literal, Ty,
    UnOp,
};

/// Recognize qualified built-in collection calls: `Set::union`, `Map::domain`, etc.
/// Returns Some(EExpr) if recognized, None if not a built-in.
pub(super) fn collect_qualified_call(
    type_name: &str,
    func_name: &str,
    args: Vec<EExpr>,
    sp: Option<crate::span::Span>,
) -> Option<EExpr> {
    let u = Ty::Error;
    let bool_ty = Ty::Builtin(BuiltinTy::Bool);
    let qc = |ty: Ty| {
        Some(EExpr::QualCall(
            ty,
            type_name.to_owned(),
            func_name.to_owned(),
            args,
            sp,
        ))
    };
    match (type_name, func_name) {
        // Relation operations on the first-class finite relation type.
        ("Rel", "join" | "transpose" | "closure" | "reach" | "product" | "project" | "field") => {
            qc(u)
        }
        // Set operations (2-arg: set × set → set/bool)
        ("Set", "union" | "intersect" | "diff") => qc(u),
        ("Set", "member" | "subset" | "disjoint") => qc(bool_ty),
        // Seq operations
        ("Seq", "head") => qc(u),   // 1-arg: seq → elem
        ("Seq", "tail") => qc(u),   // 1-arg: seq → seq
        ("Seq", "concat") => qc(u), // 2-arg: seq × seq → seq
        ("Seq", "length") => qc(Ty::Builtin(BuiltinTy::Int)), // 1-arg: seq → int
        ("Seq", "empty") => qc(bool_ty), // 1-arg: seq → bool
        // Map operations
        ("Map", "has") => qc(bool_ty), // 2-arg: map × key → bool
        ("Map", "domain" | "range" | "merge") => qc(u), // map → set / map × map → map
        _ => None,
    }
}

/// Desugar `in expr` on a quantifier body at collection time.
/// When `in_expr` is Some, wraps the body with a membership guard:
/// `all`: `(x in S) implies body`
/// others: `(x in S) and body`
/// When `in_expr` is None, returns the body unchanged.
pub(super) fn quant_guard_body(
    var: &str,
    in_expr: &Option<Box<ast::Expr>>,
    body: &ast::Expr,
    use_implies: bool,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let collected_body = collect_expr(body);
    match in_expr {
        Some(coll_expr) => {
            let var_ref = EExpr::Var(Ty::Error, var.to_owned(), sp);
            let membership = EExpr::In(
                Ty::Builtin(BuiltinTy::Bool),
                Box::new(var_ref),
                Box::new(collect_expr(coll_expr)),
                sp,
            );
            let op = if use_implies {
                BinOp::Implies
            } else {
                BinOp::And
            };
            EExpr::BinOp(
                Ty::Builtin(BuiltinTy::Bool),
                op,
                Box::new(membership),
                Box::new(collected_body),
                sp,
            )
        }
        None => collected_body,
    }
}

fn collect_set_comp_binder(binder: &ast::SetCompBinder) -> ESetCompBinder {
    match binder {
        ast::SetCompBinder::Name(name) => ESetCompBinder::Var(name.clone()),
        ast::SetCompBinder::Wildcard => ESetCompBinder::Wild,
        ast::SetCompBinder::Tuple(items) => {
            ESetCompBinder::Tuple(items.iter().map(collect_set_comp_binder).collect())
        }
    }
}

fn error_ty() -> Ty {
    Ty::Error
}

fn bool_ty() -> Ty {
    Ty::Builtin(BuiltinTy::Bool)
}

fn int_ty() -> Ty {
    Ty::Builtin(BuiltinTy::Int)
}

fn collect_call_expr(
    callee: &ast::Expr,
    args: &[ast::Expr],
    sp: Option<crate::span::Span>,
) -> EExpr {
    if let ast::ExprKind::Var(name) = &callee.kind {
        match name.as_str() {
            "Set" => return EExpr::SetLit(error_ty(), args.iter().map(collect_expr).collect(), sp),
            "Rel" => {
                return EExpr::SetLit(
                    Ty::Relation(Vec::new()),
                    args.iter().map(collect_expr).collect(),
                    sp,
                );
            }
            "Seq" => return EExpr::SeqLit(error_ty(), args.iter().map(collect_expr).collect(), sp),
            "Map" if args.len() % 2 == 0 => {
                let collected: Vec<EExpr> = args.iter().map(collect_expr).collect();
                let entries = collected
                    .chunks_exact(2)
                    .map(|pair| (pair[0].clone(), pair[1].clone()))
                    .collect();
                return EExpr::MapLit(error_ty(), entries, sp);
            }
            _ => {}
        }
    }

    if let ast::ExprKind::Qual2(type_name, func_name) = &callee.kind {
        let collected_args: Vec<EExpr> = args.iter().map(collect_expr).collect();
        if let Some(e) = collect_qualified_call(type_name, func_name, collected_args, sp) {
            return e;
        }
    }

    EExpr::Call(
        error_ty(),
        Box::new(collect_expr(callee)),
        args.iter().map(collect_expr).collect(),
        sp,
    )
}

fn collect_quantifier_expr(
    quantifier: crate::elab::types::Quantifier,
    var: &str,
    ty: &ast::TypeRef,
    in_expr: &Option<Box<ast::Expr>>,
    body: &ast::Expr,
    use_implies: bool,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let guarded = quant_guard_body(var, in_expr, body, use_implies, sp);
    EExpr::Quant(
        bool_ty(),
        quantifier,
        var.to_owned(),
        resolve_type_ref(ty),
        Box::new(guarded),
        sp,
    )
}

fn collect_aggregate_expr(
    kind: ast::AggKind,
    var: &str,
    ty: &ast::TypeRef,
    in_expr: &Option<Box<ast::Expr>>,
    body: &ast::Expr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let in_filter = in_expr.as_ref().map(|coll_expr| {
        let var_ref = EExpr::Var(Ty::Error, var.to_owned(), sp);
        Box::new(EExpr::In(
            bool_ty(),
            Box::new(var_ref),
            Box::new(collect_expr(coll_expr)),
            sp,
        ))
    });
    EExpr::Aggregate(
        int_ty(),
        kind,
        var.to_owned(),
        resolve_type_ref(ty),
        Box::new(collect_expr(body)),
        in_filter,
        sp,
    )
}

fn collect_let_expr(
    binds: &[ast::LetBind],
    body: &ast::Expr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let bs = binds
        .iter()
        .map(|lb| {
            (
                lb.name.clone(),
                lb.ty.as_ref().map(resolve_type_ref),
                collect_expr(&lb.value),
            )
        })
        .collect();
    EExpr::Let(bs, Box::new(collect_expr(body)), sp)
}

fn collect_lambda_expr(
    params: &[ast::TypedParam],
    ret_ty: Option<&ast::TypeRef>,
    body: &ast::Expr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let ps = params
        .iter()
        .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
        .collect();
    EExpr::Lam(
        ps,
        ret_ty.map(resolve_type_ref),
        Box::new(collect_expr(body)),
        sp,
    )
}

fn collect_match_expr(
    scrutinee: &ast::Expr,
    arms: &[ast::MatchArm],
    sp: Option<crate::span::Span>,
) -> EExpr {
    let scrut = collect_expr(scrutinee);
    let earms = arms
        .iter()
        .map(|arm| {
            let pat = collect_pattern(&arm.pattern);
            let guard = arm.guard.as_ref().map(|g| collect_expr(g));
            let body = collect_expr(&arm.body);
            (pat, guard, body)
        })
        .collect();
    EExpr::Match(Box::new(scrut), earms, sp)
}

fn collect_set_comp_expr(
    projection: &Option<Box<ast::Expr>>,
    binder: &ast::SetCompBinder,
    domain: &Option<ast::TypeRef>,
    source: &Option<Box<ast::Expr>>,
    filter: &ast::Expr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let dom = domain.as_ref().map_or(Ty::Error, resolve_type_ref);
    let proj = projection.as_ref().map(|p| Box::new(collect_expr(p)));
    EExpr::SetComp(
        error_ty(),
        proj,
        collect_set_comp_binder(binder),
        dom,
        source.as_ref().map(|expr| Box::new(collect_expr(expr))),
        Box::new(collect_expr(filter)),
        sp,
    )
}

fn collect_rel_comp_expr(
    projection: &ast::Expr,
    bindings: &[ast::RelCompBinding],
    filter: &ast::Expr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    EExpr::RelComp(
        Ty::Relation(Vec::new()),
        Box::new(collect_expr(projection)),
        bindings
            .iter()
            .map(|binding| ERelCompBinding {
                var: binding.var.clone(),
                domain: resolve_type_ref(&binding.domain),
                source: binding
                    .source
                    .as_ref()
                    .map(|expr| Box::new(collect_expr(expr))),
            })
            .collect(),
        Box::new(collect_expr(filter)),
        sp,
    )
}

fn collect_saw_expr(path: &[String], args: &[ast::SawArg], sp: Option<crate::span::Span>) -> EExpr {
    let (evt, prefix) = path
        .split_last()
        .map_or(("", &[][..]), |(last, prefix)| (last.as_str(), prefix));
    let sys = prefix.join("::");
    let elab_args = args
        .iter()
        .map(|a| match a {
            ast::SawArg::Wild(_) => None,
            ast::SawArg::Expr(e) => Some(Box::new(collect_expr(e))),
        })
        .collect();
    EExpr::Saw(bool_ty(), sys, evt.to_owned(), elab_args, sp)
}

fn collect_control_expr(kind: &ast::ExprKind, sp: Option<crate::span::Span>) -> Option<EExpr> {
    match kind {
        ast::ExprKind::Block(items) => Some(collect_block_items(items)),
        ast::ExprKind::VarDecl { name, ty, init } => {
            let ty_e = ty.as_ref().map(resolve_type_ref);
            Some(EExpr::VarDecl(
                name.clone(),
                ty_e,
                Box::new(collect_expr(init)),
                Box::new(EExpr::Sorry(sp)),
                sp,
            ))
        }
        ast::ExprKind::While {
            cond,
            contracts,
            body,
        } => {
            let contracts_e = contracts.iter().map(collect_contract).collect();
            Some(EExpr::While(
                Box::new(collect_expr(cond)),
                contracts_e,
                Box::new(collect_expr(body)),
                sp,
            ))
        }
        ast::ExprKind::IfElse {
            cond,
            then_body,
            else_body,
        } => Some(EExpr::IfElse(
            Box::new(collect_expr(cond)),
            Box::new(collect_expr(then_body)),
            else_body.as_ref().map(|e| Box::new(collect_expr(e))),
            sp,
        )),
        _ => None,
    }
}

pub(super) fn collect_expr(expr: &ast::Expr) -> EExpr {
    let u = error_ty;
    let sp = Some(expr.span);

    match &expr.kind {
        ast::ExprKind::Error(_) => EExpr::Todo(sp),
        ast::ExprKind::Var(n) => EExpr::Var(u(), n.clone(), sp),
        ast::ExprKind::Int(i) => EExpr::Lit(int_ty(), Literal::Int(*i), sp),
        ast::ExprKind::Real(d) => EExpr::Lit(Ty::Builtin(BuiltinTy::Real), Literal::Real(*d), sp),
        ast::ExprKind::Float(s) => EExpr::Lit(
            Ty::Builtin(BuiltinTy::Float),
            Literal::Float(parse_float_text(s)),
            sp,
        ),
        ast::ExprKind::Str(s) => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::String), Literal::Str(s.clone()), sp)
        }
        ast::ExprKind::True => EExpr::Lit(bool_ty(), Literal::Bool(true), sp),
        ast::ExprKind::False => EExpr::Lit(bool_ty(), Literal::Bool(false), sp),

        ast::ExprKind::Qual2(s, n) => EExpr::Qual(u(), s.clone(), n.clone(), sp),
        ast::ExprKind::Qual3(s, t, n) => EExpr::Qual(u(), format!("{s}::{t}"), n.clone(), sp),
        ast::ExprKind::State1(c) => EExpr::Var(u(), c.clone(), sp),
        ast::ExprKind::State1Record(c, fields) => EExpr::CtorRecord(
            u(),
            None,
            c.clone(),
            fields
                .iter()
                .map(|(n, e)| (n.clone(), collect_expr(e)))
                .collect(),
            sp,
        ),
        ast::ExprKind::State2(t, c) => EExpr::Qual(u(), t.clone(), c.clone(), sp),
        ast::ExprKind::State2Record(t, c, fields) => EExpr::CtorRecord(
            u(),
            Some(t.clone()),
            c.clone(),
            fields
                .iter()
                .map(|(n, e)| (n.clone(), collect_expr(e)))
                .collect(),
            sp,
        ),
        ast::ExprKind::State3(s, t, c) => EExpr::Qual(u(), format!("{s}::{t}"), c.clone(), sp),

        ast::ExprKind::Field(e, f) => EExpr::Field(u(), Box::new(collect_expr(e)), f.clone(), sp),
        ast::ExprKind::Prime(e) => EExpr::Prime(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Call(callee, args) => collect_call_expr(callee, args, sp),
        ast::ExprKind::CallR(callee, refs, args) => EExpr::CallR(
            u(),
            Box::new(collect_expr(callee)),
            refs.iter().map(collect_expr).collect(),
            args.iter().map(collect_expr).collect(),
            sp,
        ),

        // Unary ops
        ast::ExprKind::Neg(e) => EExpr::UnOp(int_ty(), UnOp::Neg, Box::new(collect_expr(e)), sp),
        ast::ExprKind::Not(e) => EExpr::UnOp(bool_ty(), UnOp::Not, Box::new(collect_expr(e)), sp),
        ast::ExprKind::Card(e) => EExpr::Card(u(), Box::new(collect_expr(e)), sp),

        // Binary ops: arithmetic
        ast::ExprKind::Add(a, b) => bin_op(u(), BinOp::Add, a, b, sp),
        ast::ExprKind::Sub(a, b) => bin_op(u(), BinOp::Sub, a, b, sp),
        ast::ExprKind::Mul(a, b) => bin_op(u(), BinOp::Mul, a, b, sp),
        ast::ExprKind::Div(a, b) => bin_op(u(), BinOp::Div, a, b, sp),
        ast::ExprKind::Mod(a, b) => bin_op(u(), BinOp::Mod, a, b, sp),
        ast::ExprKind::Diamond(a, b) => bin_op(u(), BinOp::Diamond, a, b, sp),
        ast::ExprKind::Disjoint(a, b) => bin_op(bool_ty(), BinOp::Disjoint, a, b, sp),

        // Binary ops: comparison (result is Bool)
        ast::ExprKind::Eq(a, b) => bin_op(bool_ty(), BinOp::Eq, a, b, sp),
        ast::ExprKind::NEq(a, b) => bin_op(bool_ty(), BinOp::NEq, a, b, sp),
        ast::ExprKind::Lt(a, b) => bin_op(bool_ty(), BinOp::Lt, a, b, sp),
        ast::ExprKind::Gt(a, b) => bin_op(bool_ty(), BinOp::Gt, a, b, sp),
        ast::ExprKind::Le(a, b) => bin_op(bool_ty(), BinOp::Le, a, b, sp),
        ast::ExprKind::Ge(a, b) => bin_op(bool_ty(), BinOp::Ge, a, b, sp),

        // Binary ops: logical (result is Bool)
        ast::ExprKind::And(a, b) => bin_op(bool_ty(), BinOp::And, a, b, sp),
        ast::ExprKind::Or(a, b) => bin_op(bool_ty(), BinOp::Or, a, b, sp),
        ast::ExprKind::Impl(a, b) => bin_op(bool_ty(), BinOp::Implies, a, b, sp),

        // Binary ops: composition
        ast::ExprKind::Unord(a, b) => bin_op(u(), BinOp::Unord, a, b, sp),
        ast::ExprKind::Conc(a, b) => bin_op(u(), BinOp::Conc, a, b, sp),
        ast::ExprKind::Xor(a, b) => bin_op(u(), BinOp::Xor, a, b, sp),

        // Membership
        ast::ExprKind::In(a, b) => EExpr::In(
            bool_ty(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),

        // Temporal
        ast::ExprKind::Always(e) => EExpr::Always(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Eventually(e) => EExpr::Eventually(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Until(l, r) => EExpr::Until(
            u(),
            Box::new(collect_expr(l)),
            Box::new(collect_expr(r)),
            sp,
        ),
        // / — past-time temporal operators.
        ast::ExprKind::Historically(e) => EExpr::Historically(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Once(e) => EExpr::Once(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Previously(e) => EExpr::Previously(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Since(l, r) => EExpr::Since(
            u(),
            Box::new(collect_expr(l)),
            Box::new(collect_expr(r)),
            sp,
        ),
        // / — saw operator.
        ast::ExprKind::Saw(path, args) => collect_saw_expr(path, args, sp),
        ast::ExprKind::AssertExpr(e) => EExpr::Assert(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::AssumeExpr(e) => EExpr::Assume(u(), Box::new(collect_expr(e)), sp),

        // Assignment
        ast::ExprKind::Assign(a, b) => EExpr::Assign(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),
        ast::ExprKind::NamedPair(n, e) => {
            EExpr::NamedPair(u(), n.clone(), Box::new(collect_expr(e)), sp)
        }
        ast::ExprKind::Seq(a, b) => EExpr::Seq(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),
        ast::ExprKind::SameStep(a, b) => EExpr::SameStep(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),
        ast::ExprKind::Pipe(a, b) => EExpr::Pipe(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),

        // Quantifiers — `all x: T | P(x)` or `all x: T in S | P(x)`.
        // When `in_expr` is present, desugar by guarding the body:
        // all: `(x in S) implies P(x)`
        // others: `(x in S) and P(x)`
        ast::ExprKind::All(v, tr, in_expr, body) => collect_quantifier_expr(
            crate::elab::types::Quantifier::All,
            v,
            tr,
            in_expr,
            body,
            true,
            sp,
        ),
        ast::ExprKind::Exists(v, tr, in_expr, body) => collect_quantifier_expr(
            crate::elab::types::Quantifier::Exists,
            v,
            tr,
            in_expr,
            body,
            false,
            sp,
        ),
        ast::ExprKind::SomeQ(v, tr, in_expr, body) => collect_quantifier_expr(
            crate::elab::types::Quantifier::Some,
            v,
            tr,
            in_expr,
            body,
            false,
            sp,
        ),
        ast::ExprKind::NoQ(v, tr, in_expr, body) => collect_quantifier_expr(
            crate::elab::types::Quantifier::No,
            v,
            tr,
            in_expr,
            body,
            false,
            sp,
        ),
        ast::ExprKind::OneQ(v, tr, in_expr, body) => collect_quantifier_expr(
            crate::elab::types::Quantifier::One,
            v,
            tr,
            in_expr,
            body,
            false,
            sp,
        ),
        ast::ExprKind::LoneQ(v, tr, in_expr, body) => collect_quantifier_expr(
            crate::elab::types::Quantifier::Lone,
            v,
            tr,
            in_expr,
            body,
            false,
            sp,
        ),
        // arithmetic aggregator.
        ast::ExprKind::Aggregate(kind, var, ty, in_expr, body) => {
            collect_aggregate_expr(*kind, var, ty, in_expr, body, sp)
        }

        // Let bindings
        ast::ExprKind::Let(binds, body) => collect_let_expr(binds, body, sp),

        // Lambda
        ast::ExprKind::Lambda(params, body) => collect_lambda_expr(params, None, body, sp),
        ast::ExprKind::LambdaT(params, ret_ty, body) => {
            collect_lambda_expr(params, Some(ret_ty), body, sp)
        }

        // Tuple literal
        ast::ExprKind::TupleLit(es) => {
            EExpr::TupleLit(u(), es.iter().map(collect_expr).collect(), sp)
        }

        // Match expression
        ast::ExprKind::Match(scrutinee, arms) => collect_match_expr(scrutinee, arms, sp),
        ast::ExprKind::Choose(binder, ty, predicate) => EExpr::Choose(
            resolve_type_ref(ty),
            binder.clone(),
            resolve_type_ref(ty),
            predicate.as_ref().map(|pred| Box::new(collect_expr(pred))),
            sp,
        ),

        // Map/collection operations
        ast::ExprKind::MapUpdate(m, k, v) => EExpr::MapUpdate(
            u(),
            Box::new(collect_expr(m)),
            Box::new(collect_expr(k)),
            Box::new(collect_expr(v)),
            sp,
        ),
        ast::ExprKind::Index(m, k) => EExpr::Index(
            u(),
            Box::new(collect_expr(m)),
            Box::new(collect_expr(k)),
            sp,
        ),
        ast::ExprKind::SetComp {
            projection,
            binder,
            domain,
            source,
            filter,
        } => collect_set_comp_expr(projection, binder, domain, source, filter, sp),
        ast::ExprKind::RelComp {
            projection,
            bindings,
            filter,
        } => collect_rel_comp_expr(projection, bindings, filter, sp),

        // Imperative constructs
        ast::ExprKind::Block(_)
        | ast::ExprKind::VarDecl { .. }
        | ast::ExprKind::While { .. }
        | ast::ExprKind::IfElse { .. } => {
            collect_control_expr(&expr.kind, sp).expect("control expression should collect")
        }

        // struct constructor
        ast::ExprKind::StructCtor(name, fields) => EExpr::StructCtor(
            Ty::Named(name.clone()),
            name.clone(),
            fields
                .iter()
                .map(|(n, e)| (n.clone(), collect_expr(e)))
                .collect(),
            sp,
        ),

        // Stubs
        ast::ExprKind::Sorry => EExpr::Sorry(sp),
        ast::ExprKind::Todo => EExpr::Todo(sp),
    }
}

/// Build nested `VarDecl` continuations from a flat block item list.
///
/// When a `VarDecl` appears in a block, its continuation is the remaining items.
/// Non-VarDecl items are sequenced into a Block.
pub(super) fn collect_block_items(items: &[ast::Expr]) -> EExpr {
    match items {
        [] => EExpr::Sorry(None),
        [single] => collect_expr(single),
        [first, rest @ ..] => {
            if let ast::ExprKind::VarDecl { name, ty, init } = &first.kind {
                let init_e = collect_expr(init);
                let rest_e = collect_block_items(rest);
                let ty_e = ty.as_ref().map(resolve_type_ref);
                EExpr::VarDecl(
                    name.clone(),
                    ty_e,
                    Box::new(init_e),
                    Box::new(rest_e),
                    Some(first.span),
                )
            } else {
                let first_e = collect_expr(first);
                let rest_e = collect_block_items(rest);
                EExpr::Block(vec![first_e, rest_e], Some(first.span))
            }
        }
    }
}

pub(super) fn collect_pattern(pat: &ast::Pattern) -> EPattern {
    match pat {
        ast::Pattern::Var(name, _) => EPattern::Var(name.clone()),
        ast::Pattern::Wild(_) => EPattern::Wild,
        ast::Pattern::Ctor(name, fields, _has_rest, _) => {
            let fps = fields
                .iter()
                .map(|fp| (fp.name.clone(), collect_pattern(&fp.pattern)))
                .collect();
            EPattern::Ctor(name.clone(), fps)
        }
        ast::Pattern::Or(left, right, _) => EPattern::Or(
            Box::new(collect_pattern(left)),
            Box::new(collect_pattern(right)),
        ),
    }
}

pub(super) fn bin_op(
    ty: Ty,
    op: BinOp,
    a: &ast::Expr,
    b: &ast::Expr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    EExpr::BinOp(
        ty,
        op,
        Box::new(collect_expr(a)),
        Box::new(collect_expr(b)),
        sp,
    )
}

pub(super) fn parse_float_text(s: &str) -> f64 {
    let stripped = s.strip_suffix('f').unwrap_or(s);
    stripped.parse().unwrap_or(0.0)
}

fn collect_contract(c: &ast::Contract) -> EContract {
    match c {
        ast::Contract::Requires { expr, .. } => EContract::Requires(collect_expr(expr)),
        ast::Contract::Ensures { expr, .. } => EContract::Ensures(collect_expr(expr)),
        ast::Contract::Decreases { measures, star, .. } => EContract::Decreases {
            measures: measures.iter().map(collect_expr).collect(),
            star: *star,
        },
        ast::Contract::Invariant { expr, .. } => EContract::Invariant(collect_expr(expr)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> crate::span::Span {
        crate::span::Span { start: 0, end: 0 }
    }

    fn expr(kind: ast::ExprKind) -> ast::Expr {
        ast::Expr { kind, span: span() }
    }

    fn var(name: &str) -> ast::Expr {
        expr(ast::ExprKind::Var(name.to_owned()))
    }

    fn int(value: i64) -> ast::Expr {
        expr(ast::ExprKind::Int(value))
    }

    #[test]
    fn collect_qualified_call_recognizes_collection_builtins() {
        let cases = [
            ("Rel", "join", Ty::Error),
            ("Set", "union", Ty::Error),
            ("Set", "member", Ty::Builtin(BuiltinTy::Bool)),
            ("Seq", "head", Ty::Error),
            ("Seq", "tail", Ty::Error),
            ("Seq", "concat", Ty::Error),
            ("Seq", "length", Ty::Builtin(BuiltinTy::Int)),
            ("Seq", "empty", Ty::Builtin(BuiltinTy::Bool)),
            ("Map", "has", Ty::Builtin(BuiltinTy::Bool)),
            ("Map", "domain", Ty::Error),
        ];

        for (namespace, name, expected_ty) in cases {
            let collected = collect_qualified_call(
                namespace,
                name,
                vec![EExpr::Lit(
                    Ty::Builtin(BuiltinTy::Int),
                    Literal::Int(1),
                    None,
                )],
                None,
            )
            .unwrap_or_else(|| panic!("{namespace}::{name} should be a builtin"));

            assert!(
                matches!(
                    collected,
                    EExpr::QualCall(ref ty, ref actual_namespace, ref actual_name, ref args, _)
                        if ty_matches(ty, &expected_ty)
                            && actual_namespace == namespace
                            && actual_name == name
                            && args.len() == 1
                ),
                "{namespace}::{name} should collect as QualCall with {expected_ty:?}, got {collected:?}"
            );
        }

        assert!(
            collect_qualified_call("Seq", "unknown", vec![], None).is_none(),
            "unknown qualified collection calls should not be treated as builtins"
        );
    }

    fn ty_matches(actual: &Ty, expected: &Ty) -> bool {
        match (actual, expected) {
            (Ty::Error, Ty::Error) => true,
            (Ty::Builtin(actual), Ty::Builtin(expected)) => actual == expected,
            _ => false,
        }
    }

    #[test]
    fn collect_map_literal_preserves_odd_arity_call_for_validation() {
        let even = collect_expr(&expr(ast::ExprKind::Call(
            Box::new(var("Map")),
            vec![int(1), int(10)],
        )));
        let EExpr::MapLit(_, entries, _) = even else {
            panic!("even Map call should collect as a map literal");
        };
        assert_eq!(entries.len(), 1);

        let odd = collect_expr(&expr(ast::ExprKind::Call(
            Box::new(var("Map")),
            vec![int(1), int(10), int(2)],
        )));
        let EExpr::Call(_, callee, args, _) = odd else {
            panic!("odd Map call should remain a call for validation, got {odd:?}");
        };
        assert!(
            matches!(callee.as_ref(), EExpr::Var(_, name, _) if name == "Map"),
            "callee should remain Map, got {callee:?}"
        );
        assert_eq!(
            args.len(),
            3,
            "odd Map call should preserve every source argument"
        );
    }

    #[test]
    fn collect_collection_literal_calls_by_constructor_name() {
        let set = collect_expr(&expr(ast::ExprKind::Call(
            Box::new(var("Set")),
            vec![int(1)],
        )));
        assert!(
            matches!(set, EExpr::SetLit(Ty::Error, ref items, _) if items.len() == 1),
            "Set(...) should collect as a set literal, got {set:?}"
        );

        let rel = collect_expr(&expr(ast::ExprKind::Call(
            Box::new(var("Rel")),
            vec![expr(ast::ExprKind::TupleLit(vec![int(1), int(2)]))],
        )));
        assert!(
            matches!(rel, EExpr::SetLit(Ty::Relation(ref columns), ref items, _) if columns.is_empty() && items.len() == 1),
            "Rel(...) should collect as a relation literal, got {rel:?}"
        );

        let seq = collect_expr(&expr(ast::ExprKind::Call(
            Box::new(var("Seq")),
            vec![int(1)],
        )));
        assert!(
            matches!(seq, EExpr::SeqLit(Ty::Error, ref items, _) if items.len() == 1),
            "Seq(...) should collect as a sequence literal, got {seq:?}"
        );
    }

    #[test]
    fn collect_saw_expr_preserves_path_shape_and_argument_kinds() {
        let unqualified = collect_saw_expr(&["created".to_owned()], &[], None);
        assert!(
            matches!(unqualified, EExpr::Saw(_, ref system, ref event, ref args, _) if system.is_empty() && event == "created" && args.is_empty()),
            "unqualified saw path should use an empty system name, got {unqualified:?}"
        );

        let two_segment = collect_saw_expr(
            &["Gateway".to_owned(), "authorize".to_owned()],
            &[
                ast::SawArg::Wild(span()),
                ast::SawArg::Expr(expr(ast::ExprKind::True)),
            ],
            None,
        );
        assert!(
            matches!(two_segment, EExpr::Saw(_, ref system, ref event, ref args, _)
                if system == "Gateway"
                    && event == "authorize"
                    && args.len() == 2
                    && args[0].is_none()
                    && matches!(args[1].as_deref(), Some(EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(true), _)))),
            "two-segment saw path should preserve wildcard and expression args, got {two_segment:?}"
        );

        let scoped = collect_saw_expr(
            &[
                "Commerce".to_owned(),
                "Gateway".to_owned(),
                "authorize".to_owned(),
            ],
            &[],
            None,
        );
        assert!(
            matches!(scoped, EExpr::Saw(_, ref system, ref event, ref args, _) if system == "Commerce::Gateway" && event == "authorize" && args.is_empty()),
            "multi-segment saw path should join all but the event name, got {scoped:?}"
        );
    }

    #[test]
    fn collect_control_expr_covers_block_var_while_and_if_else() {
        let block = collect_expr(&expr(ast::ExprKind::Block(vec![int(1), int(2)])));
        assert!(
            matches!(block, EExpr::Block(ref items, _) if items.len() == 2),
            "multi-item block should collect as a block, got {block:?}"
        );

        let var_decl = collect_expr(&expr(ast::ExprKind::VarDecl {
            name: "x".to_owned(),
            ty: None,
            init: Box::new(int(1)),
        }));
        assert!(
            matches!(var_decl, EExpr::VarDecl(ref name, None, ref init, ref body, _)
                if name == "x"
                    && matches!(init.as_ref(), EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(1), _))
                    && matches!(body.as_ref(), EExpr::Sorry(_))),
            "var declaration should collect init and placeholder body, got {var_decl:?}"
        );

        let while_expr = collect_expr(&expr(ast::ExprKind::While {
            cond: Box::new(expr(ast::ExprKind::True)),
            contracts: vec![],
            body: Box::new(expr(ast::ExprKind::Block(vec![int(1)]))),
        }));
        assert!(
            matches!(while_expr, EExpr::While(ref cond, ref contracts, ref body, _)
                if matches!(cond.as_ref(), EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(true), _))
                    && contracts.is_empty()
                    && matches!(body.as_ref(), EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(1), _))),
            "while expression should collect condition, contracts, and body, got {while_expr:?}"
        );

        let if_else = collect_expr(&expr(ast::ExprKind::IfElse {
            cond: Box::new(expr(ast::ExprKind::True)),
            then_body: Box::new(int(1)),
            else_body: Some(Box::new(int(2))),
        }));
        assert!(
            matches!(if_else, EExpr::IfElse(ref cond, ref then_body, Some(ref else_body), _)
                if matches!(cond.as_ref(), EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(true), _))
                    && matches!(then_body.as_ref(), EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(1), _))
                    && matches!(else_body.as_ref(), EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(2), _))),
            "if/else expression should collect all branches, got {if_else:?}"
        );
    }
}
