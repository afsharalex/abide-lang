//! Expression resolution — name and constructor resolution in expression trees.

use super::super::types::{BinOp, EExpr, EPattern, Literal, Ty};
use std::collections::HashMap;

use super::Ctx;

fn infer_field_type(ctx: &Ctx, base: &EExpr, field_name: &str) -> Ty {
    let entity_name: Option<String> = match base.ty() {
        Ty::Entity(name) => Some(name.clone()),
        Ty::Named(name) if ctx.entities.contains_key(name.as_str()) => Some(name.clone()),
        other => {
            let name = other.name();
            ctx.entities.contains_key(name).then(|| name.to_owned())
        }
    };

    if let Some(entity_name) = entity_name {
        if let Some(entity) = ctx.entities.get(entity_name.as_str()) {
            if let Some(field) = entity.fields.iter().find(|f| f.name == field_name) {
                return field.ty.clone();
            }
        }
    }

    Ty::Error
}

fn infer_qualcall_type(ctx: &Ctx, type_name: &str, func_name: &str, args: &[EExpr]) -> Ty {
    let bool_ty = Ty::Builtin(crate::elab::types::BuiltinTy::Bool);
    let int_ty = Ty::Builtin(crate::elab::types::BuiltinTy::Int);
    match (type_name, func_name) {
        ("Rel", "join") => infer_relation_join_type(args),
        ("Rel", "product") => infer_relation_product_type(args),
        ("Rel", "project") => infer_relation_project_type(args),
        ("Rel", "transpose") => infer_relation_transpose_type(args),
        ("Rel", "closure" | "reach") => infer_relation_closure_type(args),
        ("Rel", "field") => infer_relation_field_type(ctx, args),
        ("Set", "union" | "intersect" | "diff") => args
            .first()
            .map(|arg| arg.ty().clone())
            .unwrap_or(Ty::Error),
        ("Set", "member" | "subset" | "disjoint") => bool_ty,
        ("Seq", "head") => match args.first().map(EExpr::ty) {
            Some(Ty::Seq(element)) => element.as_ref().clone(),
            _ => Ty::Error,
        },
        ("Seq", "tail" | "concat") => args
            .first()
            .map(|arg| arg.ty().clone())
            .unwrap_or(Ty::Error),
        ("Seq", "length") => int_ty,
        ("Seq", "empty") => bool_ty,
        ("Map", "has") => bool_ty,
        ("Map", "domain") => match args.first().map(EExpr::ty) {
            Some(Ty::Map(key, _)) => Ty::Set(Box::new(key.as_ref().clone())),
            _ => Ty::Error,
        },
        ("Map", "range") => match args.first().map(EExpr::ty) {
            Some(Ty::Map(_, value)) => Ty::Set(Box::new(value.as_ref().clone())),
            _ => Ty::Error,
        },
        ("Map", "merge") => args
            .first()
            .map(|arg| arg.ty().clone())
            .unwrap_or(Ty::Error),
        _ => Ty::Error,
    }
}

fn relation_columns(ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Relation(columns) => Some(columns.clone()),
        Ty::Set(element) => match element.as_ref() {
            Ty::Tuple(columns) => Some(columns.clone()),
            column => Some(vec![column.clone()]),
        },
        _ => None,
    }
}

fn relation_type_from_columns(columns: Vec<Ty>) -> Ty {
    match columns.as_slice() {
        [] => Ty::Error,
        _ => Ty::Relation(columns),
    }
}

fn relation_type_from_projection(projection: &EExpr) -> Ty {
    match projection.ty() {
        Ty::Tuple(columns) => relation_type_from_columns(columns.clone()),
        ty => relation_type_from_columns(vec![ty.clone()]),
    }
}

fn set_source_element_type(source_ty: &Ty) -> Ty {
    match source_ty {
        Ty::Set(element) | Ty::Seq(element) => element.as_ref().clone(),
        Ty::Map(key, value) => Ty::Tuple(vec![key.as_ref().clone(), value.as_ref().clone()]),
        Ty::Store(entity) => Ty::Entity(entity.clone()),
        _ => Ty::Error,
    }
}

fn infer_numeric_binop_type(op: crate::elab::types::BinOp, left: &Ty, right: &Ty) -> Option<Ty> {
    use crate::elab::types::BinOp;
    use crate::elab::types::BuiltinTy::{Float, Int, Real};

    if !matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
    ) {
        return None;
    }
    match (left, right) {
        (Ty::Builtin(Float), Ty::Builtin(_)) | (Ty::Builtin(_), Ty::Builtin(Float)) => {
            Some(Ty::Builtin(Float))
        }
        (Ty::Builtin(Real), Ty::Builtin(Int | Real)) | (Ty::Builtin(Int), Ty::Builtin(Real)) => {
            Some(Ty::Builtin(Real))
        }
        (Ty::Builtin(Int), Ty::Builtin(Int)) => Some(Ty::Builtin(Int)),
        _ => None,
    }
}

fn ty_same(left: &Ty, right: &Ty) -> bool {
    match (left, right) {
        (Ty::Builtin(left), Ty::Builtin(right)) => left == right,
        (Ty::Enum(left, _), Ty::Enum(right, _))
        | (Ty::Enum(left, _), Ty::Named(right))
        | (Ty::Named(left), Ty::Enum(right, _)) => left == right,
        (Ty::Entity(left), Ty::Entity(right))
        | (Ty::Named(left), Ty::Named(right))
        | (Ty::Entity(left), Ty::Named(right))
        | (Ty::Named(left), Ty::Entity(right)) => left == right,
        (Ty::Set(left), Ty::Set(right)) => ty_same(left, right),
        (Ty::Seq(left), Ty::Seq(right)) => ty_same(left, right),
        (Ty::Map(left_key, left_value), Ty::Map(right_key, right_value)) => {
            ty_same(left_key, right_key) && ty_same(left_value, right_value)
        }
        (Ty::Store(left), Ty::Store(right)) => left == right,
        (Ty::Relation(left), Ty::Relation(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right.iter())
                    .all(|(left, right)| ty_same(left, right))
        }
        (Ty::Tuple(left), Ty::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right.iter())
                    .all(|(left, right)| ty_same(left, right))
        }
        (Ty::Alias(_, left), right) | (right, Ty::Alias(_, left)) => ty_same(left, right),
        (Ty::Refinement(left, _), right) | (right, Ty::Refinement(left, _)) => ty_same(left, right),
        (Ty::Error, _) | (_, Ty::Error) => true,
        _ => false,
    }
}

fn infer_relation_join_type(args: &[EExpr]) -> Ty {
    let Some(left) = args.first().and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let Some(right) = args.get(1).and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let Some(left_join) = left.last() else {
        return Ty::Error;
    };
    let Some(right_join) = right.first() else {
        return Ty::Error;
    };
    if !ty_same(left_join, right_join) {
        return Ty::Error;
    }
    let mut columns = left[..left.len() - 1].to_vec();
    columns.extend(right[1..].iter().cloned());
    relation_type_from_columns(columns)
}

fn infer_relation_set_op_type(op: BinOp, left: &EExpr, right: &EExpr) -> Option<Ty> {
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }
    let left_columns = relation_columns(&left.ty())?;
    let right_columns = relation_columns(&right.ty())?;
    if left_columns.len() == right_columns.len()
        && left_columns
            .iter()
            .zip(right_columns.iter())
            .all(|(left, right)| ty_same(left, right))
    {
        Some(relation_type_from_columns(left_columns))
    } else {
        Some(Ty::Error)
    }
}

fn infer_relation_product_type(args: &[EExpr]) -> Ty {
    let Some(left) = args.first().and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let Some(right) = args.get(1).and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let mut columns = left;
    columns.extend(right);
    relation_type_from_columns(columns)
}

fn relation_project_indices(args: &[EExpr]) -> Option<Vec<usize>> {
    args.iter()
        .map(|arg| match arg {
            EExpr::Lit(_, Literal::Int(value), _) if *value >= 0 => Some(*value as usize),
            _ => None,
        })
        .collect()
}

fn infer_relation_project_type(args: &[EExpr]) -> Ty {
    let Some(source) = args.first().and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let Some(indices) = relation_project_indices(&args[1..]) else {
        return Ty::Error;
    };
    let mut columns = Vec::with_capacity(indices.len());
    for index in indices {
        let Some(column) = source.get(index) else {
            return Ty::Error;
        };
        columns.push(column.clone());
    }
    relation_type_from_columns(columns)
}

fn infer_relation_transpose_type(args: &[EExpr]) -> Ty {
    let Some(columns) = args.first().and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let [left, right] = columns.as_slice() else {
        return Ty::Error;
    };
    relation_type_from_columns(vec![right.clone(), left.clone()])
}

fn infer_relation_closure_type(args: &[EExpr]) -> Ty {
    let Some(columns) = args.first().and_then(|arg| relation_columns(&arg.ty())) else {
        return Ty::Error;
    };
    let [left, right] = columns.as_slice() else {
        return Ty::Error;
    };
    if ty_same(left, right) {
        relation_type_from_columns(columns)
    } else {
        Ty::Error
    }
}

fn infer_relation_field_type(ctx: &Ctx, args: &[EExpr]) -> Ty {
    let Some(store_arg) = args.first() else {
        return Ty::Error;
    };
    let Ty::Store(store_entity) = store_arg.ty() else {
        return Ty::Error;
    };
    let Some(EExpr::Qual(_, owner, field_name, _)) = args.get(1) else {
        return Ty::Error;
    };
    let owner = last_segment(owner);
    if owner != store_entity {
        return Ty::Error;
    }
    let Some(entity) = ctx.entities.get(owner) else {
        return Ty::Error;
    };
    let Some(field) = entity.fields.iter().find(|field| field.name == *field_name) else {
        return Ty::Error;
    };
    Ty::Relation(vec![Ty::Entity(entity.name.clone()), field.ty.clone()])
}

fn infer_index_type(map: &EExpr) -> Ty {
    match map.ty() {
        Ty::Map(_, value) => value.as_ref().clone(),
        Ty::Seq(element) => element.as_ref().clone(),
        _ => Ty::Error,
    }
}

/// Resolve names and constructors within an expression tree.
#[allow(clippy::too_many_lines)]
pub(super) fn resolve_expr(ctx: &Ctx, bound: &HashMap<String, Ty>, expr: &EExpr) -> EExpr {
    match expr {
        EExpr::Var(_, name, sp) => {
            if let Some(bound_ty) = bound.get(name) {
                // Bound variable: use the declared type from the binding scope.
                // Don't alias-rewrite or constructor-resolve.
                EExpr::Var(bound_ty.clone(), name.clone(), *sp)
            } else {
                let resolved_name = ctx.canonical_name(name).to_owned();
                let resolved_ty = resolve_var_type(ctx, &resolved_name);
                EExpr::Var(resolved_ty, resolved_name, *sp)
            }
        }
        EExpr::Field(_ty, e, f, sp) => {
            let resolved_base = resolve_expr(ctx, bound, e);
            let resolved_ty = infer_field_type(ctx, &resolved_base, f);
            EExpr::Field(resolved_ty, Box::new(resolved_base), f.clone(), *sp)
        }
        EExpr::Prime(_, e, sp) => {
            let resolved_expr = resolve_expr(ctx, bound, e);
            EExpr::Prime(resolved_expr.ty(), Box::new(resolved_expr), *sp)
        }
        EExpr::BinOp(ty, op, a, b, sp) => {
            let resolved_left = resolve_expr(ctx, bound, a);
            let resolved_right = resolve_expr(ctx, bound, b);
            let resolved_ty = infer_relation_set_op_type(*op, &resolved_left, &resolved_right)
                .or_else(|| {
                    infer_numeric_binop_type(*op, &resolved_left.ty(), &resolved_right.ty())
                })
                .unwrap_or_else(|| ty.clone());
            EExpr::BinOp(
                resolved_ty,
                *op,
                Box::new(resolved_left),
                Box::new(resolved_right),
                *sp,
            )
        }
        EExpr::UnOp(ty, op, e, sp) => {
            EExpr::UnOp(ty.clone(), *op, Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Call(ty, f, args, sp) => {
            let resolved_func = resolve_expr(ctx, bound, f);
            let resolved_args: Vec<EExpr> =
                args.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            EExpr::Call(ty.clone(), Box::new(resolved_func), resolved_args, *sp)
        }
        EExpr::QualCall(_ty, type_name, func_name, args, sp) => {
            let resolved_args: Vec<EExpr> =
                args.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            let resolved_ty = infer_qualcall_type(ctx, type_name, func_name, &resolved_args);
            EExpr::QualCall(
                resolved_ty,
                type_name.clone(),
                func_name.clone(),
                resolved_args,
                *sp,
            )
        }
        EExpr::CallR(ty, f, refs, args, sp) => EExpr::CallR(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, f)),
            refs.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            args.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            *sp,
        ),
        EExpr::Quant(ty, q, v, vty, body, sp) => {
            let resolved_vty = ctx.resolve_ty(vty);
            let mut inner_bound = bound.clone();
            inner_bound.insert(v.clone(), resolved_vty.clone());
            EExpr::Quant(
                ty.clone(),
                *q,
                v.clone(),
                resolved_vty,
                Box::new(resolve_expr(ctx, &inner_bound, body)),
                *sp,
            )
        }
        EExpr::Always(ty, e, sp) => {
            EExpr::Always(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Eventually(ty, e, sp) => {
            EExpr::Eventually(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Until(ty, l, r, sp) => EExpr::Until(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, l)),
            Box::new(resolve_expr(ctx, bound, r)),
            *sp,
        ),
        EExpr::Historically(ty, e, sp) => {
            EExpr::Historically(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Once(ty, e, sp) => {
            EExpr::Once(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Previously(ty, e, sp) => {
            EExpr::Previously(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Since(ty, l, r, sp) => EExpr::Since(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, l)),
            Box::new(resolve_expr(ctx, bound, r)),
            *sp,
        ),
        EExpr::Assert(ty, e, sp) => {
            EExpr::Assert(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::Assume(ty, e, sp) => {
            EExpr::Assume(ty.clone(), Box::new(resolve_expr(ctx, bound, e)), *sp)
        }
        EExpr::CtorRecord(ty, qual, name, fields, sp) => {
            // Resolve the type: find which enum contains this constructor
            let resolved_ty = if matches!(ty, Ty::Named(_)) {
                if let Some(q) = qual {
                    // Qualified: @Enum::Ctor — look up the enum directly
                    ctx.types
                        .get(q.as_str())
                        .cloned()
                        .unwrap_or_else(|| ty.clone())
                } else {
                    // Unqualified: @Ctor { field: val,... }
                    // Disambiguate by matching user-provided field names against
                    // each candidate enum's declared fields. This avoids HashMap
                    // iteration order nondeterminism when multiple enums share
                    // a constructor name.
                    let user_field_names: Vec<&str> =
                        fields.iter().map(|(n, _)| n.as_str()).collect();
                    let mut candidates: Vec<&Ty> = Vec::new();
                    for t in ctx.types.values() {
                        if let Ty::Enum(en, ctors) = t {
                            if ctors.contains(name) {
                                // Check if declared fields match user fields
                                if let Some(variants) = ctx.variant_fields.get(en.as_str()) {
                                    for (vname, vfields) in variants {
                                        if vname == name {
                                            let decl_names: Vec<&str> =
                                                vfields.iter().map(|(n, _)| n.as_str()).collect();
                                            if user_field_names
                                                .iter()
                                                .all(|f| decl_names.contains(f))
                                            {
                                                candidates.push(t);
                                            }
                                            break;
                                        }
                                    }
                                } else {
                                    // No field info — fieldless enum, include as candidate
                                    candidates.push(t);
                                }
                            }
                        }
                    }
                    if candidates.len() == 1 {
                        candidates[0].clone()
                    } else {
                        // Zero or multiple matches — leave unresolved so later validation handles it
                        ty.clone()
                    }
                }
            } else {
                ty.clone()
            };
            EExpr::CtorRecord(
                resolved_ty,
                qual.clone(),
                name.clone(),
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), resolve_expr(ctx, bound, e)))
                    .collect(),
                *sp,
            )
        }
        // struct constructor — resolve the struct type and recurse into fields
        EExpr::StructCtor(ty, name, fields, sp) => {
            let resolved_ty = if matches!(ty, Ty::Named(_)) {
                ctx.types
                    .get(name.as_str())
                    .cloned()
                    .unwrap_or_else(|| ty.clone())
            } else {
                ty.clone()
            };
            EExpr::StructCtor(
                resolved_ty,
                name.clone(),
                fields
                    .iter()
                    .map(|(n, e)| (n.clone(), resolve_expr(ctx, bound, e)))
                    .collect(),
                *sp,
            )
        }
        EExpr::Assign(ty, lhs, rhs, sp) => EExpr::Assign(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, lhs)),
            Box::new(resolve_expr(ctx, bound, rhs)),
            *sp,
        ),
        EExpr::NamedPair(ty, n, e, sp) => EExpr::NamedPair(
            ty.clone(),
            n.clone(),
            Box::new(resolve_expr(ctx, bound, e)),
            *sp,
        ),
        EExpr::Seq(ty, a, b, sp) => EExpr::Seq(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::SameStep(ty, a, b, sp) => EExpr::SameStep(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::Let(binds, body, sp) => {
            let mut inner_bound = bound.clone();
            let bs = binds
                .iter()
                .map(|(n, mt, e)| {
                    let resolved_mt = mt.as_ref().map(|t| ctx.resolve_ty(t));
                    let resolved = (
                        n.clone(),
                        resolved_mt.clone(),
                        resolve_expr(ctx, &inner_bound, e),
                    );
                    inner_bound.insert(n.clone(), resolved_mt.unwrap_or(Ty::Error));
                    resolved
                })
                .collect();
            EExpr::Let(bs, Box::new(resolve_expr(ctx, &inner_bound, body)), *sp)
        }
        EExpr::Lam(params, mret, body, sp) => {
            let mut inner_bound = bound.clone();
            for (n, t) in params {
                inner_bound.insert(n.clone(), ctx.resolve_ty(t));
            }
            EExpr::Lam(
                params
                    .iter()
                    .map(|(n, t)| (n.clone(), ctx.resolve_ty(t)))
                    .collect(),
                mret.as_ref().map(|t| ctx.resolve_ty(t)),
                Box::new(resolve_expr(ctx, &inner_bound, body)),
                *sp,
            )
        }
        EExpr::Match(scrut, arms, sp) => {
            let resolved_scrut = resolve_expr(ctx, bound, scrut);
            let resolved_arms = arms
                .iter()
                .map(|(pat, guard, body)| {
                    let mut arm_bound: HashMap<String, Ty> = bound.clone();
                    collect_epattern_vars(pat, &mut arm_bound);
                    let resolved_guard = guard.as_ref().map(|g| resolve_expr(ctx, &arm_bound, g));
                    let resolved_body = resolve_expr(ctx, &arm_bound, body);
                    (pat.clone(), resolved_guard, resolved_body)
                })
                .collect();
            EExpr::Match(Box::new(resolved_scrut), resolved_arms, *sp)
        }
        EExpr::SetComp(_ty, proj, var, vty, source, filter, sp) => {
            let resolved_source = source
                .as_ref()
                .map(|source| Box::new(resolve_expr(ctx, bound, source)));
            let explicit_vty = ctx.resolve_ty(vty);
            let resolved_vty = if matches!(explicit_vty, Ty::Error) {
                resolved_source
                    .as_deref()
                    .map(EExpr::ty)
                    .map(|ty| set_source_element_type(&ty))
                    .unwrap_or(Ty::Error)
            } else {
                explicit_vty
            };
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone(), resolved_vty.clone());
            let resolved_proj = proj
                .as_ref()
                .map(|p| Box::new(resolve_expr(ctx, &inner_bound, p)));
            let element_ty = resolved_proj
                .as_deref()
                .map(EExpr::ty)
                .unwrap_or_else(|| resolved_vty.clone());
            EExpr::SetComp(
                Ty::Set(Box::new(element_ty)),
                resolved_proj,
                var.clone(),
                resolved_vty,
                resolved_source,
                Box::new(resolve_expr(ctx, &inner_bound, filter)),
                *sp,
            )
        }
        EExpr::RelComp(_ty, projection, bindings, filter, sp) => {
            let mut inner_bound = bound.clone();
            let resolved_bindings = bindings
                .iter()
                .map(|binding| {
                    let resolved_domain = ctx.resolve_ty(&binding.domain);
                    inner_bound.insert(binding.var.clone(), resolved_domain.clone());
                    super::super::types::ERelCompBinding {
                        var: binding.var.clone(),
                        domain: resolved_domain,
                        source: binding
                            .source
                            .as_ref()
                            .map(|source| Box::new(resolve_expr(ctx, bound, source))),
                    }
                })
                .collect::<Vec<_>>();
            let resolved_projection = resolve_expr(ctx, &inner_bound, projection);
            let resolved_filter = resolve_expr(ctx, &inner_bound, filter);
            let resolved_ty = relation_type_from_projection(&resolved_projection);
            EExpr::RelComp(
                resolved_ty,
                Box::new(resolved_projection),
                resolved_bindings,
                Box::new(resolved_filter),
                *sp,
            )
        }
        EExpr::MapUpdate(_ty, m, k, v, sp) => {
            let resolved_map = resolve_expr(ctx, bound, m);
            let resolved_key = resolve_expr(ctx, bound, k);
            let resolved_value = resolve_expr(ctx, bound, v);
            EExpr::MapUpdate(
                resolved_map.ty().clone(),
                Box::new(resolved_map),
                Box::new(resolved_key),
                Box::new(resolved_value),
                *sp,
            )
        }
        EExpr::Index(_ty, m, k, sp) => {
            let resolved_map = resolve_expr(ctx, bound, m);
            let resolved_key = resolve_expr(ctx, bound, k);
            let resolved_ty = infer_index_type(&resolved_map);
            EExpr::Index(
                resolved_ty,
                Box::new(resolved_map),
                Box::new(resolved_key),
                *sp,
            )
        }
        EExpr::Qual(_, s, n, sp) => {
            let ty = ctx
                .types
                .get(s.as_str())
                .or_else(|| {
                    let last = last_segment(s);
                    ctx.types.get(last)
                })
                .cloned()
                .unwrap_or_else(|| Ty::Named(s.clone()));
            EExpr::Qual(ty, s.clone(), n.clone(), *sp)
        }
        EExpr::TupleLit(_ty, es, sp) => {
            let resolved_items: Vec<EExpr> =
                es.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            let item_tys = resolved_items
                .iter()
                .map(|item| item.ty().clone())
                .collect();
            EExpr::TupleLit(Ty::Tuple(item_tys), resolved_items, *sp)
        }
        EExpr::In(ty, a, b, sp) => EExpr::In(
            ty.clone(),
            Box::new(resolve_expr(ctx, bound, a)),
            Box::new(resolve_expr(ctx, bound, b)),
            *sp,
        ),
        EExpr::Card(_ty, e, sp) => EExpr::Card(
            Ty::Builtin(crate::elab::types::BuiltinTy::Int),
            Box::new(resolve_expr(ctx, bound, e)),
            *sp,
        ),
        EExpr::Pipe(ty, a, b, sp) => {
            let resolved_left = resolve_expr(ctx, bound, a);
            let resolved_right = resolve_expr(ctx, bound, b);
            if let EExpr::QualCall(_, namespace, name, args, _) = &resolved_right {
                if namespace == "Rel" {
                    let mut piped_args = Vec::with_capacity(args.len() + 1);
                    piped_args.push(resolved_left);
                    piped_args.extend(args.iter().cloned());
                    let resolved_ty = infer_qualcall_type(ctx, namespace, name, &piped_args);
                    return EExpr::QualCall(
                        resolved_ty,
                        namespace.clone(),
                        name.clone(),
                        piped_args,
                        *sp,
                    );
                }
            }
            EExpr::Pipe(
                ty.clone(),
                Box::new(resolved_left),
                Box::new(resolved_right),
                *sp,
            )
        }
        EExpr::Block(items, sp) => EExpr::Block(
            items.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
            *sp,
        ),
        EExpr::VarDecl(name, ty, init, rest, sp) => {
            let resolved_ty = ty.as_ref().map(|t| ctx.resolve_ty(t));
            let resolved_init = resolve_expr(ctx, bound, init);
            let mut inner_bound = bound.clone();
            inner_bound.insert(name.clone(), resolved_ty.clone().unwrap_or(Ty::Error));
            let resolved_rest = resolve_expr(ctx, &inner_bound, rest);
            EExpr::VarDecl(
                name.clone(),
                resolved_ty,
                Box::new(resolved_init),
                Box::new(resolved_rest),
                *sp,
            )
        }
        EExpr::While(cond, contracts, body, sp) => {
            let resolved_contracts = contracts
                .iter()
                .map(|c| super::resolve_contract(ctx, bound, bound, c))
                .collect();
            EExpr::While(
                Box::new(resolve_expr(ctx, bound, cond)),
                resolved_contracts,
                Box::new(resolve_expr(ctx, bound, body)),
                *sp,
            )
        }
        EExpr::IfElse(cond, then_body, else_body, sp) => EExpr::IfElse(
            Box::new(resolve_expr(ctx, bound, cond)),
            Box::new(resolve_expr(ctx, bound, then_body)),
            else_body
                .as_ref()
                .map(|e| Box::new(resolve_expr(ctx, bound, e))),
            *sp,
        ),
        // ── Collection literals: resolve elements and infer collection type ──
        EExpr::SetLit(ty, elems, sp) => {
            let resolved_elems: Vec<EExpr> =
                elems.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            // Infer element type from first element (or leave as unresolved)
            let elem_ty = resolved_elems.first().map_or(Ty::Error, |e| e.ty().clone());
            let collection_ty = if matches!(ty, Ty::Relation(_)) {
                match elem_ty {
                    Ty::Tuple(columns) => Ty::Relation(columns),
                    Ty::Error => Ty::Error,
                    single => Ty::Relation(vec![single]),
                }
            } else {
                Ty::Set(Box::new(elem_ty))
            };
            EExpr::SetLit(collection_ty, resolved_elems, *sp)
        }
        EExpr::SeqLit(_ty, elems, sp) => {
            let resolved_elems: Vec<EExpr> =
                elems.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
            let elem_ty = resolved_elems.first().map_or(Ty::Error, |e| e.ty().clone());
            EExpr::SeqLit(Ty::Seq(Box::new(elem_ty)), resolved_elems, *sp)
        }
        EExpr::MapLit(_ty, entries, sp) => {
            let resolved_entries: Vec<(EExpr, EExpr)> = entries
                .iter()
                .map(|(k, v)| (resolve_expr(ctx, bound, k), resolve_expr(ctx, bound, v)))
                .collect();
            let key_ty = resolved_entries
                .first()
                .map_or(Ty::Error, |(k, _)| k.ty().clone());
            let val_ty = resolved_entries
                .first()
                .map_or(Ty::Error, |(_, v)| v.ty().clone());
            EExpr::MapLit(
                Ty::Map(Box::new(key_ty), Box::new(val_ty)),
                resolved_entries,
                *sp,
            )
        }
        // resolve aggregate domain + body,
        // then infer the result type. count → Int; others → body type.
        EExpr::Aggregate(_ty, kind, var, domain, body, in_filter, sp) => {
            use crate::ast::AggKind;
            let resolved_domain = ctx.resolve_ty(domain);
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone(), resolved_domain.clone());
            let resolved_body = resolve_expr(ctx, &inner_bound, body);
            let resolved_filter = in_filter
                .as_ref()
                .map(|f| Box::new(resolve_expr(ctx, &inner_bound, f)));
            let result_ty = match kind {
                AggKind::Count => Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                AggKind::Sum | AggKind::Product | AggKind::Min | AggKind::Max => {
                    // Infer from body type; default to Int if unresolved.
                    match resolved_body.ty() {
                        Ty::Builtin(crate::elab::types::BuiltinTy::Real) => {
                            Ty::Builtin(crate::elab::types::BuiltinTy::Real)
                        }
                        Ty::Builtin(crate::elab::types::BuiltinTy::Float) => {
                            Ty::Builtin(crate::elab::types::BuiltinTy::Float)
                        }
                        _ => Ty::Builtin(crate::elab::types::BuiltinTy::Int),
                    }
                }
            };
            EExpr::Aggregate(
                result_ty,
                *kind,
                var.clone(),
                resolved_domain,
                Box::new(resolved_body),
                resolved_filter,
                *sp,
            )
        }
        // resolve `saw Extern::command(args)`.
        //
        // Only explicit two-segment type-qualified forms are intended for the
        // extern-boundary slice. We still preserve unqualified and 3+ segment
        // shapes here so `validate_saw_expressions` can reject them with the
        // dedicated boundary diagnostic after alias canonicalization.
        EExpr::Saw(ty, sys, evt, args, sp) => {
            let resolved_args: Vec<Option<Box<EExpr>>> = args
                .iter()
                .map(|a| a.as_ref().map(|e| Box::new(resolve_expr(ctx, bound, e))))
                .collect();

            let canonical_sys = if sys.is_empty() || sys.contains("::") {
                // Unqualified or 3+ segment: pass through unchanged for the
                // dedicated validation pass.
                sys.clone()
            } else {
                ctx.canonical_name(sys).to_owned()
            };

            EExpr::Saw(ty.clone(), canonical_sys, evt.clone(), resolved_args, *sp)
        }
        e => e.clone(),
    }
}

/// Collect variable names bound by a pattern into the given map.
pub(super) fn collect_epattern_vars(pat: &EPattern, vars: &mut HashMap<String, Ty>) {
    match pat {
        EPattern::Var(name) => {
            vars.insert(name.clone(), Ty::Error);
        }
        EPattern::Ctor(_, fields) => {
            for (_, fpat) in fields {
                collect_epattern_vars(fpat, vars);
            }
        }
        EPattern::Wild => {}
        EPattern::Or(left, right) => {
            collect_epattern_vars(left, vars);
            collect_epattern_vars(right, vars);
        }
    }
}

pub(super) fn resolve_var_type(ctx: &Ctx, name: &str) -> Ty {
    if let Some(parent_ty) = find_constructor_type(ctx, name) {
        return parent_ty;
    }
    if let Some(t) = ctx.types.get(name) {
        return t.clone();
    }
    Ty::Error
}

/// When a constructor expression has `Ty::Unresolved` (e.g. `@None` ambiguous across
/// multiple monomorphized generics), use the declared field type to resolve it.
/// If the field type is an enum and the constructor name is one of its variants,
/// patch the expression's type to the field's enum type.
pub(super) fn resolve_ctor_type_from_context(expr: &mut EExpr, field_ty: &Ty) {
    let Ty::Enum(_, ctors) = field_ty else { return };
    match expr {
        EExpr::Var(ref mut ty, name, _) if matches!(ty, Ty::Error) => {
            if ctors.iter().any(|c| c == name) {
                *ty = field_ty.clone();
            }
        }
        // Call wrapping a constructor: @Some(42) → Call(Var(@Some), [42])
        EExpr::Call(ref mut ty, ref mut callee, _, _) if matches!(ty, Ty::Error) => {
            if let EExpr::Var(ref mut inner_ty, name, _) = callee.as_mut() {
                if matches!(inner_ty, Ty::Error) && ctors.iter().any(|c| c == name) {
                    *inner_ty = field_ty.clone();
                    *ty = field_ty.clone();
                }
            }
        }
        EExpr::CtorRecord(ref mut ty, _, name, _, _) if matches!(ty, Ty::Error) => {
            if ctors.iter().any(|c| c == name) {
                *ty = field_ty.clone();
            }
        }
        _ => {}
    }
}

pub(super) fn find_constructor_type(ctx: &Ctx, name: &str) -> Option<Ty> {
    let mut matches: Vec<&Ty> = Vec::new();
    for ty in ctx.types.values() {
        if let Ty::Enum(_, ctors) = ty {
            if ctors.iter().any(|c| c == name) {
                matches.push(ty);
            }
        }
    }
    if matches.len() == 1 {
        return Some(matches[0].clone());
    }
    if matches.len() > 1 {
        // Prefer non-monomorphized (non-generic) types over monomorphized ones.
        // Monomorphized types have `<` in their name (e.g. "Option<Int>").
        let non_mono: Vec<&Ty> = matches
            .iter()
            .filter(|t| {
                if let Ty::Enum(n, _) = t {
                    !n.contains('<')
                } else {
                    true
                }
            })
            .copied()
            .collect();
        if non_mono.len() == 1 {
            return Some(non_mono[0].clone());
        }
        if non_mono.is_empty() {
            // All matches are monomorphized instances of generic(s).
            // Don't pick arbitrarily — leave unresolved for context-driven resolution.
            return None;
        }
        // Multiple non-monomorphized matches — pre-existing ambiguity, return first
        return Some(non_mono[0].clone());
    }
    None
}

pub(super) fn last_segment(s: &str) -> &str {
    s.rsplit("::").next().unwrap_or(s)
}
