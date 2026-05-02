//! Expression collection — AST expressions to elaborated expressions.

use super::resolve_type_ref;
use crate::ast;
use crate::elab::types::{
    BinOp, BuiltinTy, EContract, EExpr, EPattern, ERelCompBinding, Literal, Ty, UnOp,
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

#[allow(clippy::too_many_lines)]
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

pub(super) fn collect_expr(expr: &ast::Expr) -> EExpr {
    let u = || Ty::Error;
    let bool_ty = || Ty::Builtin(BuiltinTy::Bool);
    let int_ty = || Ty::Builtin(BuiltinTy::Int);
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
        ast::ExprKind::Call(callee, args) => {
            // Recognize collection literals: Set(1, 2, 3), Seq(1, 2), Map(k1, v1, k2, v2)
            if let ast::ExprKind::Var(name) = &callee.kind {
                match name.as_str() {
                    "Set" => {
                        return EExpr::SetLit(u(), args.iter().map(collect_expr).collect(), sp);
                    }
                    "Rel" => {
                        return EExpr::SetLit(
                            Ty::Relation(Vec::new()),
                            args.iter().map(collect_expr).collect(),
                            sp,
                        );
                    }
                    "Seq" => {
                        return EExpr::SeqLit(u(), args.iter().map(collect_expr).collect(), sp);
                    }
                    "Map" => {
                        // Map literal: pairs of (key, value) args
                        let collected: Vec<EExpr> = args.iter().map(collect_expr).collect();
                        let entries: Vec<(EExpr, EExpr)> = collected
                            .chunks(2)
                            .filter_map(|pair| {
                                if pair.len() == 2 {
                                    Some((pair[0].clone(), pair[1].clone()))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        return EExpr::MapLit(u(), entries, sp);
                    }
                    _ => {}
                }
            }
            // Recognize qualified built-in calls: Set::union(s1, s2), Map::domain(m), etc.
            if let ast::ExprKind::Qual2(type_name, func_name) = &callee.kind {
                let collected_args: Vec<EExpr> = args.iter().map(collect_expr).collect();
                if let Some(e) = collect_qualified_call(type_name, func_name, collected_args, sp) {
                    return e;
                }
            }
            EExpr::Call(
                u(),
                Box::new(collect_expr(callee)),
                args.iter().map(collect_expr).collect(),
                sp,
            )
        }
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
        ast::ExprKind::Saw(path, args) => {
            // Path forms currently intended for the boundary slice:
            // ["Extern", "command"] (qualified). Unqualified and 3+ segment
            // shapes are preserved here so resolution can reject them with the
            // dedicated extern-boundary diagnostic.
            let (sys, evt) = match path.len() {
                2 => (path[0].clone(), path[1].clone()),
                1 => (String::new(), path[0].clone()),
                _ => {
                    // 3+ segments: store as-is and let resolve_expr reject.
                    // Use first as sys placeholder, last as event placeholder.
                    (
                        path[..path.len() - 1].join("::"),
                        path.last().cloned().unwrap_or_default(),
                    )
                }
            };
            let elab_args: Vec<Option<Box<EExpr>>> = args
                .iter()
                .map(|a| match a {
                    ast::SawArg::Wild(_) => None,
                    ast::SawArg::Expr(e) => Some(Box::new(collect_expr(e))),
                })
                .collect();
            EExpr::Saw(bool_ty(), sys, evt, elab_args, sp)
        }
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
        ast::ExprKind::All(v, tr, in_expr, body) => {
            let guarded = quant_guard_body(v, in_expr, body, true, sp);
            EExpr::Quant(
                bool_ty(),
                crate::elab::types::Quantifier::All,
                v.clone(),
                resolve_type_ref(tr),
                Box::new(guarded),
                sp,
            )
        }
        ast::ExprKind::Exists(v, tr, in_expr, body) => {
            let guarded = quant_guard_body(v, in_expr, body, false, sp);
            EExpr::Quant(
                bool_ty(),
                crate::elab::types::Quantifier::Exists,
                v.clone(),
                resolve_type_ref(tr),
                Box::new(guarded),
                sp,
            )
        }
        ast::ExprKind::SomeQ(v, tr, in_expr, body) => {
            let guarded = quant_guard_body(v, in_expr, body, false, sp);
            EExpr::Quant(
                bool_ty(),
                crate::elab::types::Quantifier::Some,
                v.clone(),
                resolve_type_ref(tr),
                Box::new(guarded),
                sp,
            )
        }
        ast::ExprKind::NoQ(v, tr, in_expr, body) => {
            let guarded = quant_guard_body(v, in_expr, body, false, sp);
            EExpr::Quant(
                bool_ty(),
                crate::elab::types::Quantifier::No,
                v.clone(),
                resolve_type_ref(tr),
                Box::new(guarded),
                sp,
            )
        }
        ast::ExprKind::OneQ(v, tr, in_expr, body) => {
            let guarded = quant_guard_body(v, in_expr, body, false, sp);
            EExpr::Quant(
                bool_ty(),
                crate::elab::types::Quantifier::One,
                v.clone(),
                resolve_type_ref(tr),
                Box::new(guarded),
                sp,
            )
        }
        ast::ExprKind::LoneQ(v, tr, in_expr, body) => {
            let guarded = quant_guard_body(v, in_expr, body, false, sp);
            EExpr::Quant(
                bool_ty(),
                crate::elab::types::Quantifier::Lone,
                v.clone(),
                resolve_type_ref(tr),
                Box::new(guarded),
                sp,
            )
        }
        // arithmetic aggregator.
        ast::ExprKind::Aggregate(kind, var, ty, in_expr, body) => {
            let result_ty = Ty::Builtin(crate::elab::types::BuiltinTy::Int);
            let in_filter = in_expr.as_ref().map(|coll_expr| {
                let var_ref = EExpr::Var(Ty::Error, var.clone(), sp);
                Box::new(EExpr::In(
                    Ty::Builtin(crate::elab::types::BuiltinTy::Bool),
                    Box::new(var_ref),
                    Box::new(collect_expr(coll_expr)),
                    sp,
                ))
            });
            EExpr::Aggregate(
                result_ty,
                *kind,
                var.clone(),
                resolve_type_ref(ty),
                Box::new(collect_expr(body)),
                in_filter,
                sp,
            )
        }

        // Let bindings
        ast::ExprKind::Let(binds, body) => {
            let bs: Vec<(String, Option<Ty>, EExpr)> = binds
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

        // Lambda
        ast::ExprKind::Lambda(params, body) => {
            let ps: Vec<(String, Ty)> = params
                .iter()
                .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
                .collect();
            EExpr::Lam(ps, None, Box::new(collect_expr(body)), sp)
        }
        ast::ExprKind::LambdaT(params, ret_ty, body) => {
            let ps: Vec<(String, Ty)> = params
                .iter()
                .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
                .collect();
            EExpr::Lam(
                ps,
                Some(resolve_type_ref(ret_ty)),
                Box::new(collect_expr(body)),
                sp,
            )
        }

        // Tuple literal
        ast::ExprKind::TupleLit(es) => {
            EExpr::TupleLit(u(), es.iter().map(collect_expr).collect(), sp)
        }

        // Match expression
        ast::ExprKind::Match(scrutinee, arms) => {
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
            var,
            domain,
            source,
            filter,
        } => {
            let dom = domain.as_ref().map_or(Ty::Error, resolve_type_ref);
            let proj = projection.as_ref().map(|p| Box::new(collect_expr(p)));
            EExpr::SetComp(
                u(),
                proj,
                var.clone(),
                dom,
                source.as_ref().map(|expr| Box::new(collect_expr(expr))),
                Box::new(collect_expr(filter)),
                sp,
            )
        }
        ast::ExprKind::RelComp {
            projection,
            bindings,
            filter,
        } => EExpr::RelComp(
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
        ),

        // Imperative constructs
        ast::ExprKind::Block(items) => collect_block_items(items),
        ast::ExprKind::VarDecl { name, ty, init } => {
            // Standalone VarDecl outside a block (shouldn't happen in practice,
            // but handle gracefully by wrapping with a Sorry continuation).
            let ty_e = ty.as_ref().map(resolve_type_ref);
            EExpr::VarDecl(
                name.clone(),
                ty_e,
                Box::new(collect_expr(init)),
                Box::new(EExpr::Sorry(sp)),
                sp,
            )
        }
        ast::ExprKind::While {
            cond,
            contracts,
            body,
        } => {
            let contracts_e = contracts.iter().map(collect_contract).collect();
            EExpr::While(
                Box::new(collect_expr(cond)),
                contracts_e,
                Box::new(collect_expr(body)),
                sp,
            )
        }
        ast::ExprKind::IfElse {
            cond,
            then_body,
            else_body,
        } => EExpr::IfElse(
            Box::new(collect_expr(cond)),
            Box::new(collect_expr(then_body)),
            else_body.as_ref().map(|e| Box::new(collect_expr(e))),
            sp,
        ),

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
