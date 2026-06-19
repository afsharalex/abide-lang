//! Expression resolution — name and constructor resolution in expression trees.

use super::super::types::{BinOp, EExpr, EPattern, Literal, Ty};
use std::collections::HashMap;

use super::collection::{bind_set_comp_binder, set_source_element_type};
use super::constructor::{
    expected_constructor_call, resolve_comparison_ctor_from_context,
    resolve_ctor_type_from_context, resolve_var_type,
};
use super::Ctx;

fn infer_field_type(ctx: &Ctx, base: &EExpr, field_name: &str) -> Ty {
    let entity_name = match base.ty() {
        Ty::Entity(name) | Ty::Named(name) => name.clone(),
        other => other.name().to_owned(),
    };

    if let Some(entity) = ctx.entities.get(entity_name.as_str()) {
        if let Some(field) = entity.fields.iter().find(|f| f.name == field_name) {
            return ctx.resolve_ty(&field.ty);
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
        // `float` (IEEE-754 binary64) is a closed domain (DDR-059): it combines
        // only with `float`. Mixing `float` with `real` or `int` requires an
        // explicit conversion, so such an expression is a type error here rather
        // than being silently promoted (which would hide the loss of exactness).
        (Ty::Builtin(Float), Ty::Builtin(Float)) => Some(Ty::Builtin(Float)),
        // `int` promotes to `real` (exact, lossless).
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

fn resolve_if_else_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    cond: &EExpr,
    then_body: &EExpr,
    else_body: Option<&EExpr>,
    sp: Option<crate::span::Span>,
) -> EExpr {
    EExpr::IfElse(
        Box::new(resolve_expr(ctx, bound, cond)),
        Box::new(resolve_expr(ctx, bound, then_body)),
        else_body.map(|e| Box::new(resolve_expr(ctx, bound, e))),
        sp,
    )
}

fn resolve_if_else_with_expected_type(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    cond: &EExpr,
    then_body: &EExpr,
    else_body: Option<&EExpr>,
    sp: Option<crate::span::Span>,
    expected_ty: &Ty,
) -> EExpr {
    EExpr::IfElse(
        Box::new(resolve_expr(ctx, bound, cond)),
        Box::new(resolve_expr_with_expected_type(
            ctx,
            bound,
            then_body,
            expected_ty,
        )),
        else_body.map(|e| Box::new(resolve_expr_with_expected_type(ctx, bound, e, expected_ty))),
        sp,
    )
}

fn resolve_block_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    items: &[EExpr],
    sp: Option<crate::span::Span>,
) -> EExpr {
    EExpr::Block(
        items.iter().map(|e| resolve_expr(ctx, bound, e)).collect(),
        sp,
    )
}

fn resolve_var_decl_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    name: &str,
    ty: &Option<Ty>,
    init: &EExpr,
    rest: &EExpr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let resolved_ty = ty.as_ref().map(|t| ctx.resolve_ty(t));
    let resolved_init = if let Some(expected_ty) = ty {
        resolve_expr_with_expected_type(ctx, bound, init, expected_ty)
    } else {
        resolve_expr(ctx, bound, init)
    };
    let mut inner_bound = bound.clone();
    inner_bound.insert(name.to_owned(), resolved_ty.clone().unwrap_or(Ty::Error));
    EExpr::VarDecl(
        name.to_owned(),
        resolved_ty,
        Box::new(resolved_init),
        Box::new(resolve_expr(ctx, &inner_bound, rest)),
        sp,
    )
}

fn resolve_while_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    cond: &EExpr,
    contracts: &[super::super::types::EContract],
    body: &EExpr,
    sp: Option<crate::span::Span>,
) -> EExpr {
    let resolved_contracts = contracts
        .iter()
        .map(|c| super::resolve_contract(ctx, bound, bound, c))
        .collect();
    EExpr::While(
        Box::new(resolve_expr(ctx, bound, cond)),
        resolved_contracts,
        Box::new(resolve_expr(ctx, bound, body)),
        sp,
    )
}

fn resolve_set_literal_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    ty: &Ty,
    elems: &[EExpr],
    sp: Option<crate::span::Span>,
) -> EExpr {
    let resolved_elems: Vec<EExpr> = elems.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
    // abide-audit: allow-silent-fallback -- default branch is the documented absent or unresolved-type sentinel
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
    EExpr::SetLit(collection_ty, resolved_elems, sp)
}

fn resolve_seq_literal_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    elems: &[EExpr],
    sp: Option<crate::span::Span>,
) -> EExpr {
    let resolved_elems: Vec<EExpr> = elems.iter().map(|e| resolve_expr(ctx, bound, e)).collect();
    // abide-audit: allow-silent-fallback -- default branch is the documented absent or unresolved-type sentinel
    let elem_ty = resolved_elems.first().map_or(Ty::Error, |e| e.ty().clone());
    EExpr::SeqLit(Ty::Seq(Box::new(elem_ty)), resolved_elems, sp)
}

fn resolve_map_literal_expr(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    entries: &[(EExpr, EExpr)],
    sp: Option<crate::span::Span>,
) -> EExpr {
    let resolved_entries: Vec<(EExpr, EExpr)> = entries
        .iter()
        .map(|(k, v)| (resolve_expr(ctx, bound, k), resolve_expr(ctx, bound, v)))
        .collect();
    let key_ty = resolved_entries
        .first()
        // abide-audit: allow-silent-fallback -- default branch is the documented absent or unresolved-type sentinel
        .map_or(Ty::Error, |(k, _)| k.ty().clone());
    let val_ty = resolved_entries
        .first()
        // abide-audit: allow-silent-fallback -- default branch is the documented absent or unresolved-type sentinel
        .map_or(Ty::Error, |(_, v)| v.ty().clone());
    EExpr::MapLit(
        Ty::Map(Box::new(key_ty), Box::new(val_ty)),
        resolved_entries,
        sp,
    )
}

fn resolve_collection_literal_with_expected_type(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    expr: &EExpr,
    written_expected_ty: &Ty,
    expected_ty: &Ty,
) -> Option<EExpr> {
    match (expr, expected_ty) {
        (EExpr::SetLit(_, elements, sp), Ty::Set(element_ty)) => {
            let written_element_ty = match written_expected_ty {
                Ty::Set(element) => element.as_ref(),
                _ => element_ty.as_ref(),
            };
            let resolved_items = elements
                .iter()
                .map(|element| {
                    resolve_expr_with_expected_type(ctx, bound, element, written_element_ty)
                })
                .collect::<Vec<_>>();
            let item_ty = resolved_items
                .first()
                .map(EExpr::ty)
                .unwrap_or_else(|| element_ty.as_ref().clone());
            Some(EExpr::SetLit(
                Ty::Set(Box::new(item_ty)),
                resolved_items,
                *sp,
            ))
        }
        (EExpr::SetLit(_, elements, sp), Ty::Relation(columns)) => {
            let resolved_element_ty = match columns.as_slice() {
                [single] => single.clone(),
                _ => Ty::Tuple(columns.clone()),
            };
            let written_element_ty = match written_expected_ty {
                Ty::Relation(written_columns) => match written_columns.as_slice() {
                    [single] => single.clone(),
                    _ => Ty::Tuple(written_columns.clone()),
                },
                _ => resolved_element_ty,
            };
            let resolved_items = elements
                .iter()
                .map(|element| {
                    resolve_expr_with_expected_type(ctx, bound, element, &written_element_ty)
                })
                .collect::<Vec<_>>();
            Some(EExpr::SetLit(expected_ty.clone(), resolved_items, *sp))
        }
        (EExpr::SeqLit(_, elements, sp), Ty::Seq(element_ty)) => {
            let written_element_ty = match written_expected_ty {
                Ty::Seq(element) => element.as_ref(),
                _ => element_ty.as_ref(),
            };
            let resolved_items = elements
                .iter()
                .map(|element| {
                    resolve_expr_with_expected_type(ctx, bound, element, written_element_ty)
                })
                .collect::<Vec<_>>();
            let item_ty = resolved_items
                .first()
                .map(EExpr::ty)
                .unwrap_or_else(|| element_ty.as_ref().clone());
            Some(EExpr::SeqLit(
                Ty::Seq(Box::new(item_ty)),
                resolved_items,
                *sp,
            ))
        }
        (EExpr::MapLit(_, entries, sp), Ty::Map(key_ty, value_ty)) => {
            let (written_key_ty, written_value_ty) = match written_expected_ty {
                Ty::Map(key, value) => (key.as_ref(), value.as_ref()),
                _ => (key_ty.as_ref(), value_ty.as_ref()),
            };
            let resolved_entries = entries
                .iter()
                .map(|(key, value)| {
                    (
                        resolve_expr_with_expected_type(ctx, bound, key, written_key_ty),
                        resolve_expr_with_expected_type(ctx, bound, value, written_value_ty),
                    )
                })
                .collect::<Vec<_>>();
            let resolved_key_ty = resolved_entries
                .first()
                .map(|(key, _)| key.ty().clone())
                .unwrap_or_else(|| key_ty.as_ref().clone());
            let resolved_value_ty = resolved_entries
                .first()
                .map(|(_, value)| value.ty().clone())
                .unwrap_or_else(|| value_ty.as_ref().clone());
            Some(EExpr::MapLit(
                Ty::Map(Box::new(resolved_key_ty), Box::new(resolved_value_ty)),
                resolved_entries,
                *sp,
            ))
        }
        _ => None,
    }
}

/// Resolve names and constructors within an expression tree.
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
            let mut resolved_left = resolve_expr(ctx, bound, a);
            let mut resolved_right = resolve_expr(ctx, bound, b);
            if matches!(op, BinOp::Eq | BinOp::NEq) {
                resolved_left =
                    resolve_comparison_ctor_from_context(ctx, resolved_left, &resolved_right.ty());
                resolved_right =
                    resolve_comparison_ctor_from_context(ctx, resolved_right, &resolved_left.ty());
            }
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
                    let resolved_init = if let Some(expected_ty) = mt {
                        resolve_expr_with_expected_type(ctx, &inner_bound, e, expected_ty)
                    } else {
                        resolve_expr(ctx, &inner_bound, e)
                    };
                    let resolved = (n.clone(), resolved_mt.clone(), resolved_init);
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
            let scrut_ctors = enum_constructors_for_ty(ctx, &resolved_scrut.ty());
            let resolved_arms = arms
                .iter()
                .map(|(pat, guard, body)| {
                    let mut arm_bound: HashMap<String, Ty> = bound.clone();
                    collect_epattern_vars_for_scrutinee(
                        pat,
                        scrut_ctors.as_deref(),
                        &mut arm_bound,
                    );
                    let resolved_guard = guard.as_ref().map(|g| resolve_expr(ctx, &arm_bound, g));
                    let resolved_body = resolve_expr(ctx, &arm_bound, body);
                    (pat.clone(), resolved_guard, resolved_body)
                })
                .collect();
            EExpr::Match(Box::new(resolved_scrut), resolved_arms, *sp)
        }
        EExpr::Choose(_ty, binder, domain_ty, predicate, sp) => {
            let resolved_domain = ctx.resolve_ty(domain_ty);
            let mut inner_bound = bound.clone();
            inner_bound.insert(binder.clone(), resolved_domain.clone());
            EExpr::Choose(
                resolved_domain.clone(),
                binder.clone(),
                resolved_domain,
                predicate
                    .as_ref()
                    .map(|pred| Box::new(resolve_expr(ctx, &inner_bound, pred))),
                *sp,
            )
        }
        EExpr::SetComp(_ty, proj, binder, vty, source, filter, sp) => {
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
            bind_set_comp_binder(&mut inner_bound, binder, &resolved_vty);
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
                binder.clone(),
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
        EExpr::Block(items, sp) => resolve_block_expr(ctx, bound, items, *sp),
        EExpr::VarDecl(name, ty, init, rest, sp) => {
            resolve_var_decl_expr(ctx, bound, name, ty, init, rest, *sp)
        }
        EExpr::While(cond, contracts, body, sp) => {
            resolve_while_expr(ctx, bound, cond, contracts, body, *sp)
        }
        EExpr::IfElse(cond, then_body, else_body, sp) => {
            resolve_if_else_expr(ctx, bound, cond, then_body, else_body.as_deref(), *sp)
        }
        // ── Collection literals: resolve elements and infer collection type ──
        EExpr::SetLit(ty, elems, sp) => resolve_set_literal_expr(ctx, bound, ty, elems, *sp),
        EExpr::SeqLit(_ty, elems, sp) => resolve_seq_literal_expr(ctx, bound, elems, *sp),
        EExpr::MapLit(_ty, entries, sp) => resolve_map_literal_expr(ctx, bound, entries, *sp),
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

fn resolve_expr_with_expected_type(
    ctx: &Ctx,
    bound: &HashMap<String, Ty>,
    expr: &EExpr,
    expected_ty: &Ty,
) -> EExpr {
    let written_expected_ty = expected_ty;
    let expected_ty = ctx.resolve_ty(written_expected_ty);
    match (expr, &expected_ty) {
        (EExpr::TupleLit(_, elements, sp), Ty::Tuple(expected_items))
            if elements.len() == expected_items.len() =>
        {
            let written_items = match written_expected_ty {
                Ty::Tuple(items) => Some(items.as_slice()),
                _ => None,
            };
            let resolved_items = elements
                .iter()
                .enumerate()
                .zip(expected_items.iter())
                .map(|((idx, element), expected)| {
                    let recursive_expected = written_items
                        .and_then(|items| items.get(idx))
                        .unwrap_or(expected);
                    resolve_expr_with_expected_type(ctx, bound, element, recursive_expected)
                })
                .collect::<Vec<_>>();
            let item_tys = resolved_items
                .iter()
                .map(|item| item.ty().clone())
                .collect();
            return EExpr::TupleLit(Ty::Tuple(item_tys), resolved_items, *sp);
        }
        (EExpr::IfElse(cond, then_body, else_body, sp), _) => {
            return resolve_if_else_with_expected_type(
                ctx,
                bound,
                cond,
                then_body,
                else_body.as_deref(),
                *sp,
                written_expected_ty,
            );
        }
        (EExpr::SetLit(..) | EExpr::SeqLit(..) | EExpr::MapLit(..), _) => {
            if let Some(resolved) = resolve_collection_literal_with_expected_type(
                ctx,
                bound,
                expr,
                written_expected_ty,
                &expected_ty,
            ) {
                return resolved;
            }
        }
        (EExpr::Call(_, callee, args, sp), Ty::Enum(_, _)) => {
            if let Some(constructor) = expected_constructor_call(ctx, written_expected_ty, callee) {
                let resolved_callee = constructor.resolve_callee(callee);
                let resolved_args = args
                    .iter()
                    .enumerate()
                    .map(|(idx, arg)| {
                        if let Some(expected_arg_ty) = constructor.payload_tys.get(idx) {
                            resolve_expr_with_expected_type(ctx, bound, arg, expected_arg_ty)
                        } else {
                            resolve_expr(ctx, bound, arg)
                        }
                    })
                    .collect::<Vec<_>>();
                return EExpr::Call(
                    constructor.expected_ty,
                    Box::new(resolved_callee),
                    resolved_args,
                    *sp,
                );
            }
        }
        _ => {}
    }

    let mut resolved = resolve_expr(ctx, bound, expr);
    resolve_ctor_type_from_context(&mut resolved, &expected_ty);
    resolved
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

fn collect_epattern_vars_for_scrutinee(
    pat: &EPattern,
    constructors: Option<&[String]>,
    vars: &mut HashMap<String, Ty>,
) {
    match pat {
        EPattern::Var(name) => {
            if !constructors.is_some_and(|ctors| ctors.iter().any(|ctor| ctor == name)) {
                vars.insert(name.clone(), Ty::Error);
            }
        }
        EPattern::Ctor(_, fields) => {
            for (_, fpat) in fields {
                collect_epattern_vars(fpat, vars);
            }
        }
        EPattern::Wild => {}
        EPattern::Or(left, right) => {
            collect_epattern_vars_for_scrutinee(left, constructors, vars);
            collect_epattern_vars_for_scrutinee(right, constructors, vars);
        }
    }
}

fn enum_constructors_for_ty(ctx: &Ctx, ty: &Ty) -> Option<Vec<String>> {
    match ctx.resolve_ty(ty) {
        Ty::Enum(_, ctors) => Some(ctors),
        _ => None,
    }
}

pub(super) fn last_segment(s: &str) -> &str {
    s.rsplit("::").next().unwrap_or(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Visibility;
    use crate::elab::env::Env;
    use crate::elab::types::{BuiltinTy, EEntity, EField, GenericTypeDef};

    fn int_ty() -> Ty {
        Ty::Builtin(BuiltinTy::Int)
    }

    fn bool_ty() -> Ty {
        Ty::Builtin(BuiltinTy::Bool)
    }

    fn string_ty() -> Ty {
        Ty::Builtin(BuiltinTy::String)
    }

    fn var(name: &str, ty: Ty) -> EExpr {
        EExpr::Var(ty, name.to_owned(), None)
    }

    fn lit_int(value: i64) -> EExpr {
        EExpr::Lit(int_ty(), Literal::Int(value), None)
    }

    fn ctx_with_order_entity() -> Ctx {
        let mut env = Env::new();
        env.entities.insert(
            "Order".to_owned(),
            EEntity {
                name: "Order".to_owned(),
                fields: vec![EField {
                    name: "status".to_owned(),
                    ty: Ty::Named("Status".to_owned()),
                    default: None,
                    span: None,
                }],
                actions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
                span: None,
            },
        );
        env.types.insert(
            "Status".to_owned(),
            Ty::Enum(
                "Status".to_owned(),
                vec!["Open".to_owned(), "Closed".to_owned()],
            ),
        );
        Ctx::from_env(&env)
    }

    fn ctx_with_status_types() -> Ctx {
        let mut env = Env::new();
        env.types.insert(
            "Status".to_owned(),
            Ty::Enum(
                "Status".to_owned(),
                vec!["Open".to_owned(), "Closed".to_owned()],
            ),
        );
        env.types.insert(
            "Outcome".to_owned(),
            Ty::Enum(
                "Outcome".to_owned(),
                vec!["Open".to_owned(), "Failed".to_owned()],
            ),
        );
        Ctx::from_env(&env)
    }

    #[test]
    fn infer_field_type_resolves_named_and_entity_base_types() {
        let ctx = ctx_with_order_entity();

        for base_ty in [
            Ty::Entity("Order".to_owned()),
            Ty::Named("Order".to_owned()),
        ] {
            let field_ty = infer_field_type(&ctx, &var("order", base_ty), "status");
            assert!(
                matches!(&field_ty, Ty::Enum(name, variants) if name == "Status" && variants == &vec!["Open".to_owned(), "Closed".to_owned()]),
                "status field should resolve through ctx types, got {field_ty:?}"
            );
        }

        assert!(
            matches!(
                infer_field_type(
                    &ctx,
                    &var("order", Ty::Entity("Order".to_owned())),
                    "missing"
                ),
                Ty::Error
            ),
            "unknown fields should remain poison"
        );
    }

    #[test]
    fn infer_qualcall_type_covers_common_collection_helpers() {
        let ctx = ctx_with_order_entity();
        let int_set = Ty::Set(Box::new(int_ty()));
        let int_seq = Ty::Seq(Box::new(int_ty()));
        let int_string_map = Ty::Map(Box::new(int_ty()), Box::new(string_ty()));
        let relation = Ty::Relation(vec![int_ty(), int_ty()]);

        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Rel", "closure", &[var("r", relation)]),
                Ty::Relation(columns) if matches!(columns.as_slice(), [Ty::Builtin(BuiltinTy::Int), Ty::Builtin(BuiltinTy::Int)])
            ),
            "Rel::closure should keep homogeneous binary relation type"
        );
        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Set", "union", &[var("s", int_set.clone())]),
                Ty::Set(inner) if matches!(inner.as_ref(), Ty::Builtin(BuiltinTy::Int))
            ),
            "Set::union should keep set type"
        );
        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Set", "member", &[lit_int(1), var("s", int_set)]),
                Ty::Builtin(BuiltinTy::Bool)
            ),
            "Set::member should return bool"
        );
        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Seq", "head", &[var("xs", int_seq.clone())]),
                Ty::Builtin(BuiltinTy::Int)
            ),
            "Seq::head should return element type"
        );
        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Seq", "tail", &[var("xs", int_seq)]),
                Ty::Seq(inner) if matches!(inner.as_ref(), Ty::Builtin(BuiltinTy::Int))
            ),
            "Seq::tail should keep sequence type"
        );
        assert!(
            matches!(
                infer_qualcall_type(
                    &ctx,
                    "Seq",
                    "length",
                    &[var("xs", Ty::Seq(Box::new(string_ty())))]
                ),
                Ty::Builtin(BuiltinTy::Int)
            ),
            "Seq::length should return int"
        );
        assert!(
            matches!(
                infer_qualcall_type(
                    &ctx,
                    "Seq",
                    "empty",
                    &[var("xs", Ty::Seq(Box::new(string_ty())))]
                ),
                Ty::Builtin(BuiltinTy::Bool)
            ),
            "Seq::empty should return bool"
        );
        assert!(
            matches!(
                infer_qualcall_type(
                    &ctx,
                    "Map",
                    "has",
                    &[var("m", int_string_map.clone()), lit_int(1)]
                ),
                Ty::Builtin(BuiltinTy::Bool)
            ),
            "Map::has should return bool"
        );
        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Map", "domain", &[var("m", int_string_map.clone())]),
                Ty::Set(inner) if matches!(inner.as_ref(), Ty::Builtin(BuiltinTy::Int))
            ),
            "Map::domain should return key set"
        );
        assert!(
            matches!(
                infer_qualcall_type(&ctx, "Map", "range", &[var("m", int_string_map)]),
                Ty::Set(inner) if matches!(inner.as_ref(), Ty::Builtin(BuiltinTy::String))
            ),
            "Map::range should return value set"
        );
        assert!(
            matches!(
                infer_qualcall_type(
                    &ctx,
                    "Map",
                    "merge",
                    &[var("m", Ty::Map(Box::new(int_ty()), Box::new(string_ty())))]
                ),
                Ty::Map(key, value)
                    if matches!(key.as_ref(), Ty::Builtin(BuiltinTy::Int))
                        && matches!(value.as_ref(), Ty::Builtin(BuiltinTy::String))
            ),
            "Map::merge should keep map type"
        );
    }

    #[test]
    fn set_source_element_type_covers_maps_and_stores() {
        assert!(
            matches!(
                set_source_element_type(&Ty::Map(Box::new(int_ty()), Box::new(string_ty()))),
                Ty::Tuple(columns)
                    if matches!(columns.as_slice(), [
                        Ty::Builtin(BuiltinTy::Int),
                        Ty::Builtin(BuiltinTy::String)
                    ])
            ),
            "map sources should bind key/value tuples"
        );
        assert!(
            matches!(
                set_source_element_type(&Ty::Store("Order".to_owned())),
                Ty::Entity(name) if name == "Order"
            ),
            "store sources should bind entity instances"
        );
    }

    #[test]
    fn relation_helpers_preserve_columns_and_reject_empty_relations() {
        assert!(
            matches!(
                relation_columns(&Ty::Relation(vec![int_ty(), string_ty()])),
                Some(columns)
                    if matches!(columns.as_slice(), [
                        Ty::Builtin(BuiltinTy::Int),
                        Ty::Builtin(BuiltinTy::String)
                    ])
            ),
            "relation columns should be returned directly"
        );
        assert!(
            matches!(relation_type_from_columns(vec![]), Ty::Error),
            "empty relation column list should be poison"
        );
    }

    #[test]
    fn relation_set_op_type_accepts_only_matching_relation_shapes() {
        let left = var("left", Ty::Relation(vec![int_ty(), string_ty()]));
        let right = var("right", Ty::Relation(vec![int_ty(), string_ty()]));
        let wrong_len = var("wrong_len", Ty::Relation(vec![int_ty()]));
        let wrong_type = var("wrong_type", Ty::Relation(vec![string_ty(), string_ty()]));

        assert!(
            matches!(
                infer_relation_set_op_type(BinOp::Add, &left, &right),
                Some(Ty::Relation(columns))
                    if matches!(columns.as_slice(), [
                        Ty::Builtin(BuiltinTy::Int),
                        Ty::Builtin(BuiltinTy::String)
                    ])
            ),
            "relation union-style ops should preserve matching relation shape"
        );
        assert!(
            infer_relation_set_op_type(BinOp::Eq, &left, &right).is_none(),
            "non relation-set operators should not infer a relation set op type"
        );
        assert!(
            matches!(
                infer_relation_set_op_type(BinOp::Add, &left, &wrong_len),
                Some(Ty::Error)
            ),
            "different relation arity should be poison"
        );
        assert!(
            matches!(
                infer_relation_set_op_type(BinOp::Add, &left, &wrong_type),
                Some(Ty::Error)
            ),
            "different relation column types should be poison"
        );
    }

    #[test]
    fn relation_project_indices_reject_negative_indices() {
        assert_eq!(
            relation_project_indices(&[lit_int(0), lit_int(2)]),
            Some(vec![0, 2])
        );
        assert_eq!(
            relation_project_indices(&[lit_int(-1)]),
            None,
            "negative projection indices should be rejected"
        );
    }

    #[test]
    fn relation_ty_same_compares_nominal_and_container_types_structurally() {
        assert!(ty_same(
            &Ty::Enum("Status".to_owned(), vec![]),
            &Ty::Named("Status".to_owned())
        ));
        assert!(!ty_same(
            &Ty::Enum("Status".to_owned(), vec![]),
            &Ty::Named("Outcome".to_owned())
        ));
        assert!(ty_same(
            &Ty::Entity("Order".to_owned()),
            &Ty::Named("Order".to_owned())
        ));
        assert!(!ty_same(
            &Ty::Entity("Order".to_owned()),
            &Ty::Named("Customer".to_owned())
        ));
        assert!(ty_same(
            &Ty::Set(Box::new(int_ty())),
            &Ty::Set(Box::new(int_ty()))
        ));
        assert!(!ty_same(
            &Ty::Set(Box::new(int_ty())),
            &Ty::Set(Box::new(string_ty()))
        ));
        assert!(ty_same(
            &Ty::Seq(Box::new(int_ty())),
            &Ty::Seq(Box::new(int_ty()))
        ));
        assert!(!ty_same(
            &Ty::Seq(Box::new(int_ty())),
            &Ty::Seq(Box::new(string_ty()))
        ));
        assert!(ty_same(
            &Ty::Map(Box::new(int_ty()), Box::new(string_ty())),
            &Ty::Map(Box::new(int_ty()), Box::new(string_ty()))
        ));
        assert!(!ty_same(
            &Ty::Map(Box::new(int_ty()), Box::new(string_ty())),
            &Ty::Map(Box::new(string_ty()), Box::new(string_ty()))
        ));
        assert!(!ty_same(
            &Ty::Map(Box::new(int_ty()), Box::new(string_ty())),
            &Ty::Map(Box::new(int_ty()), Box::new(int_ty()))
        ));
        assert!(ty_same(
            &Ty::Store("Order".to_owned()),
            &Ty::Store("Order".to_owned())
        ));
        assert!(!ty_same(
            &Ty::Store("Order".to_owned()),
            &Ty::Store("Customer".to_owned())
        ));
        assert!(ty_same(
            &Ty::Relation(vec![int_ty(), string_ty()]),
            &Ty::Relation(vec![int_ty(), string_ty()])
        ));
        assert!(!ty_same(
            &Ty::Relation(vec![int_ty(), string_ty()]),
            &Ty::Relation(vec![int_ty(), int_ty()])
        ));
        assert!(!ty_same(
            &Ty::Relation(vec![int_ty(), string_ty()]),
            &Ty::Relation(vec![int_ty()])
        ));
        assert!(ty_same(
            &Ty::Tuple(vec![int_ty(), string_ty()]),
            &Ty::Tuple(vec![int_ty(), string_ty()])
        ));
        assert!(!ty_same(
            &Ty::Tuple(vec![int_ty(), string_ty()]),
            &Ty::Tuple(vec![int_ty()])
        ));
        assert!(ty_same(
            &Ty::Alias("Alias".to_owned(), Box::new(int_ty())),
            &int_ty()
        ));
        assert!(ty_same(
            &Ty::Refinement(Box::new(int_ty()), Box::new(lit_int(1))),
            &int_ty()
        ));
        assert!(ty_same(&Ty::Error, &Ty::Store("Order".to_owned())));
    }

    #[test]
    fn infer_numeric_binop_type_keeps_real_and_float_domains_distinct() {
        // DDR-059: `float` is a closed domain — only float+float yields float.
        assert!(
            matches!(
                infer_numeric_binop_type(
                    BinOp::Add,
                    &Ty::Builtin(BuiltinTy::Float),
                    &Ty::Builtin(BuiltinTy::Float)
                ),
                Some(Ty::Builtin(BuiltinTy::Float))
            ),
            "float + float should be float"
        );
        // Mixing float with int or real is NOT implicit — it is a type error.
        assert!(
            infer_numeric_binop_type(BinOp::Add, &Ty::Builtin(BuiltinTy::Float), &int_ty())
                .is_none(),
            "float + int must not implicitly promote"
        );
        assert!(
            infer_numeric_binop_type(
                BinOp::Add,
                &Ty::Builtin(BuiltinTy::Float),
                &Ty::Builtin(BuiltinTy::Real)
            )
            .is_none(),
            "float + real must not implicitly mix"
        );
        // `int` still promotes to `real` (exact, lossless).
        assert!(
            matches!(
                infer_numeric_binop_type(BinOp::Sub, &int_ty(), &Ty::Builtin(BuiltinTy::Real)),
                Some(Ty::Builtin(BuiltinTy::Real))
            ),
            "real arithmetic should promote int/real to real"
        );
    }

    #[test]
    fn infer_index_type_returns_map_value_type() {
        assert!(
            matches!(
                infer_index_type(&var(
                    "m",
                    Ty::Map(Box::new(int_ty()), Box::new(string_ty()))
                )),
                Ty::Builtin(BuiltinTy::String)
            ),
            "map indexing should return the value type"
        );
        assert!(
            matches!(
                infer_index_type(&var("xs", Ty::Seq(Box::new(int_ty())))),
                Ty::Builtin(BuiltinTy::Int)
            ),
            "sequence indexing should return the element type"
        );
    }

    #[test]
    fn resolve_expr_infers_real_and_float_aggregate_result_types() {
        let ctx = ctx_with_status_types();
        let bound = HashMap::new();

        for (body_ty, expected) in [
            (Ty::Builtin(BuiltinTy::Real), Ty::Builtin(BuiltinTy::Real)),
            (Ty::Builtin(BuiltinTy::Float), Ty::Builtin(BuiltinTy::Float)),
        ] {
            let resolved = resolve_expr(
                &ctx,
                &bound,
                &EExpr::Aggregate(
                    Ty::Error,
                    crate::ast::AggKind::Sum,
                    "x".to_owned(),
                    body_ty.clone(),
                    Box::new(var("x", body_ty)),
                    None,
                    None,
                ),
            );
            assert!(
                matches!(
                    (resolved.ty(), expected),
                    (Ty::Builtin(actual), Ty::Builtin(expected)) if actual == expected
                ),
                "aggregate result type should follow numeric body type, got {resolved:?}"
            );
        }
    }

    fn ctx_with_monomorphized_options() -> Ctx {
        let mut env = Env::new();
        env.generic_types.insert(
            "Option".to_owned(),
            GenericTypeDef {
                name: "Option".to_owned(),
                type_params: vec!["T".to_owned()],
                variant_names: vec!["Some".to_owned(), "None".to_owned()],
                variant_fields: vec![
                    (
                        "Some".to_owned(),
                        vec![("_0".to_owned(), Ty::Named("T".to_owned()))],
                    ),
                    ("None".to_owned(), vec![]),
                ],
                visibility: Visibility::Private,
                span: crate::span::Span { start: 0, end: 0 },
            },
        );
        env.types.insert(
            "Option<int>".to_owned(),
            Ty::Enum(
                "Option<int>".to_owned(),
                vec!["Some".to_owned(), "None".to_owned()],
            ),
        );
        env.types.insert(
            "Option<bool>".to_owned(),
            Ty::Enum(
                "Option<bool>".to_owned(),
                vec!["Some".to_owned(), "None".to_owned()],
            ),
        );
        env.variant_fields.insert(
            "Option<int>".to_owned(),
            vec![("Some".to_owned(), vec![("_0".to_owned(), int_ty())])],
        );
        env.variant_fields.insert(
            "Option<bool>".to_owned(),
            vec![("Some".to_owned(), vec![("_0".to_owned(), bool_ty())])],
        );
        env.types.insert(
            "MaybeIntRel".to_owned(),
            Ty::Relation(vec![Ty::Named("Option<int>".to_owned())]),
        );
        env.types.insert(
            "MaybePairRel".to_owned(),
            Ty::Relation(vec![
                Ty::Named("Option<int>".to_owned()),
                Ty::Named("Option<bool>".to_owned()),
            ]),
        );
        Ctx::from_env(&env)
    }

    #[test]
    fn resolve_expr_infers_let_initializer_constructor_from_annotation() {
        let ctx = ctx_with_monomorphized_options();
        let resolved = resolve_expr(
            &ctx,
            &HashMap::new(),
            &EExpr::Let(
                vec![(
                    "x".to_owned(),
                    Some(Ty::Named("Option<int>".to_owned())),
                    var("None", Ty::Error),
                )],
                Box::new(EExpr::Lit(bool_ty(), Literal::Bool(true), None)),
                None,
            ),
        );

        let EExpr::Let(bindings, _, _) = resolved else {
            panic!("expected let expression");
        };
        let (_, annotation, init) = bindings.first().expect("let binding");
        assert!(
            matches!(annotation, Some(Ty::Enum(name, _)) if name == "Option<int>"),
            "let annotation should resolve to Option<int>, got {annotation:?}"
        );
        assert!(
            matches!(init.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "constructor initializer should infer Option<int>, got {init:?}"
        );
    }

    #[test]
    fn resolve_expr_infers_var_initializer_constructor_from_annotation() {
        let ctx = ctx_with_monomorphized_options();
        let resolved = resolve_expr(
            &ctx,
            &HashMap::new(),
            &EExpr::VarDecl(
                "x".to_owned(),
                Some(Ty::Named("Option<int>".to_owned())),
                Box::new(var("None", Ty::Error)),
                Box::new(EExpr::Lit(bool_ty(), Literal::Bool(true), None)),
                None,
            ),
        );

        let EExpr::VarDecl(_, ref annotation, ref init, _, _) = resolved else {
            panic!("expected var declaration");
        };
        assert!(
            matches!(annotation, Some(Ty::Enum(name, _)) if name == "Option<int>"),
            "var annotation should resolve to Option<int>, got {annotation:?}"
        );
        assert!(
            matches!(init.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "constructor initializer should infer Option<int>, got {init:?}"
        );
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_tuple_initializer_items() {
        let ctx = ctx_with_monomorphized_options();
        let resolved = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::TupleLit(
                Ty::Error,
                vec![var("None", Ty::Error), var("None", Ty::Error)],
                None,
            ),
            &Ty::Tuple(vec![
                Ty::Named("Option<int>".to_owned()),
                Ty::Named("Option<bool>".to_owned()),
            ]),
        );

        let EExpr::TupleLit(_, elements, _) = resolved else {
            panic!("expected tuple literal");
        };
        assert!(
            matches!(elements[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "first tuple element should infer Option<int>, got {:?}",
            elements[0]
        );
        assert!(
            matches!(elements[1].ty(), Ty::Enum(name, _) if name == "Option<bool>"),
            "second tuple element should infer Option<bool>, got {:?}",
            elements[1]
        );
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_collection_literals() {
        let ctx = ctx_with_monomorphized_options();

        let resolved_set = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(Ty::Error, vec![var("None", Ty::Error)], None),
            &Ty::Set(Box::new(Ty::Named("Option<int>".to_owned()))),
        );
        let EExpr::SetLit(_, set_items, _) = resolved_set else {
            panic!("expected set literal");
        };
        assert!(
            matches!(set_items[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "set element should infer Option<int>, got {:?}",
            set_items[0]
        );

        let resolved_seq = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SeqLit(Ty::Error, vec![var("None", Ty::Error)], None),
            &Ty::Seq(Box::new(Ty::Named("Option<bool>".to_owned()))),
        );
        let EExpr::SeqLit(_, seq_items, _) = resolved_seq else {
            panic!("expected seq literal");
        };
        assert!(
            matches!(seq_items[0].ty(), Ty::Enum(name, _) if name == "Option<bool>"),
            "seq element should infer Option<bool>, got {:?}",
            seq_items[0]
        );

        let resolved_map = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::MapLit(
                Ty::Error,
                vec![(var("None", Ty::Error), var("None", Ty::Error))],
                None,
            ),
            &Ty::Map(
                Box::new(Ty::Named("Option<int>".to_owned())),
                Box::new(Ty::Named("Option<bool>".to_owned())),
            ),
        );
        let EExpr::MapLit(_, entries, _) = resolved_map else {
            panic!("expected map literal");
        };
        let (key, value) = entries.first().expect("map entry");
        assert!(
            matches!(key.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "map key should infer Option<int>, got {key:?}"
        );
        assert!(
            matches!(value.ty(), Ty::Enum(name, _) if name == "Option<bool>"),
            "map value should infer Option<bool>, got {value:?}"
        );
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_empty_collection_literals() {
        let ctx = ctx_with_monomorphized_options();

        let resolved_set = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(Ty::Error, vec![], None),
            &Ty::Set(Box::new(Ty::Named("Option<int>".to_owned()))),
        );
        assert!(
            matches!(resolved_set.ty(), Ty::Set(inner) if matches!(inner.as_ref(), Ty::Enum(name, _) if name == "Option<int>")),
            "empty set should retain expected element type, got {resolved_set:?}"
        );

        let resolved_seq = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SeqLit(Ty::Error, vec![], None),
            &Ty::Seq(Box::new(Ty::Named("Option<bool>".to_owned()))),
        );
        assert!(
            matches!(resolved_seq.ty(), Ty::Seq(inner) if matches!(inner.as_ref(), Ty::Enum(name, _) if name == "Option<bool>")),
            "empty seq should retain expected element type, got {resolved_seq:?}"
        );

        let resolved_map = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::MapLit(Ty::Error, vec![], None),
            &Ty::Map(
                Box::new(Ty::Named("Option<int>".to_owned())),
                Box::new(Ty::Named("Option<bool>".to_owned())),
            ),
        );
        assert!(
            matches!(resolved_map.ty(), Ty::Map(key, value)
                if matches!(key.as_ref(), Ty::Enum(name, _) if name == "Option<int>")
                    && matches!(value.as_ref(), Ty::Enum(name, _) if name == "Option<bool>")),
            "empty map should retain expected key/value types, got {resolved_map:?}"
        );
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_relation_literals() {
        let ctx = ctx_with_monomorphized_options();

        let resolved_single = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(Ty::Error, vec![var("None", Ty::Error)], None),
            &Ty::Relation(vec![Ty::Named("Option<int>".to_owned())]),
        );
        let EExpr::SetLit(single_ty, single_items, _) = resolved_single else {
            panic!("expected single-column relation literal");
        };
        assert!(
            matches!(&single_ty, Ty::Relation(columns)
                if matches!(columns.as_slice(), [Ty::Enum(name, _)] if name == "Option<int>")),
            "single-column relation should retain relation type, got {single_ty:?}"
        );
        assert!(
            matches!(single_items[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "single-column relation row should infer Option<int>, got {:?}",
            single_items[0]
        );

        let resolved_multi = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(
                Ty::Error,
                vec![EExpr::TupleLit(
                    Ty::Error,
                    vec![var("None", Ty::Error), var("None", Ty::Error)],
                    None,
                )],
                None,
            ),
            &Ty::Relation(vec![
                Ty::Named("Option<int>".to_owned()),
                Ty::Named("Option<bool>".to_owned()),
            ]),
        );
        let EExpr::SetLit(multi_ty, multi_items, _) = resolved_multi else {
            panic!("expected multi-column relation literal");
        };
        assert!(
            matches!(&multi_ty, Ty::Relation(columns)
                if matches!(columns.as_slice(), [Ty::Enum(int_name, _), Ty::Enum(bool_name, _)] if int_name == "Option<int>" && bool_name == "Option<bool>")),
            "multi-column relation should retain relation type, got {multi_ty:?}"
        );
        let EExpr::TupleLit(_, row_items, _) = &multi_items[0] else {
            panic!(
                "expected multi-column relation row tuple, got {:?}",
                multi_items[0]
            );
        };
        assert!(
            matches!(row_items[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "first relation column should infer Option<int>, got {:?}",
            row_items[0]
        );
        assert!(
            matches!(row_items[1].ty(), Ty::Enum(name, _) if name == "Option<bool>"),
            "second relation column should infer Option<bool>, got {:?}",
            row_items[1]
        );

        let resolved_alias = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(Ty::Error, vec![var("None", Ty::Error)], None),
            &Ty::Named("MaybeIntRel".to_owned()),
        );
        let EExpr::SetLit(_, alias_items, _) = resolved_alias else {
            panic!("expected aliased relation literal");
        };
        assert!(
            matches!(alias_items[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "aliased single-column relation row should infer Option<int>, got {:?}",
            alias_items[0]
        );
    }

    #[test]
    fn resolve_expr_uses_written_expected_type_for_nested_collection_payloads() {
        let ctx = ctx_with_monomorphized_options();
        let nested_option = Ty::Param(
            "Option".to_owned(),
            vec![Ty::Param("Option".to_owned(), vec![int_ty()])],
        );
        let nested_bool_option = Ty::Param(
            "Option".to_owned(),
            vec![Ty::Param("Option".to_owned(), vec![bool_ty()])],
        );
        let nested_some = EExpr::Call(
            Ty::Error,
            Box::new(var("Some", Ty::Error)),
            vec![var("None", Ty::Error)],
            None,
        );
        let nested_bool_some = EExpr::Call(
            Ty::Error,
            Box::new(var("Some", Ty::Error)),
            vec![var("None", Ty::Error)],
            None,
        );

        let resolved_set = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(Ty::Error, vec![nested_some.clone()], None),
            &Ty::Set(Box::new(nested_option.clone())),
        );
        let EExpr::SetLit(_, set_items, _) = resolved_set else {
            panic!("expected set literal");
        };
        let EExpr::Call(_, _, set_args, _) = &set_items[0] else {
            panic!("expected nested constructor in set, got {:?}", set_items[0]);
        };
        assert!(
            matches!(set_args[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "set element constructor payload should infer Option<int> from written generic type, got {:?}",
            set_args[0]
        );

        let resolved_seq = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SeqLit(Ty::Error, vec![nested_some.clone()], None),
            &Ty::Seq(Box::new(nested_option.clone())),
        );
        let EExpr::SeqLit(_, seq_items, _) = resolved_seq else {
            panic!("expected seq literal");
        };
        let EExpr::Call(_, _, seq_args, _) = &seq_items[0] else {
            panic!("expected nested constructor in seq, got {:?}", seq_items[0]);
        };
        assert!(
            matches!(seq_args[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "seq element constructor payload should infer Option<int> from written generic type, got {:?}",
            seq_args[0]
        );

        let resolved_map = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::MapLit(
                Ty::Error,
                vec![(nested_some.clone(), nested_bool_some)],
                None,
            ),
            &Ty::Map(
                Box::new(nested_option.clone()),
                Box::new(nested_bool_option),
            ),
        );
        let EExpr::MapLit(_, map_entries, _) = resolved_map else {
            panic!("expected map literal");
        };
        let (map_key, map_value) = map_entries.first().expect("map entry");
        let EExpr::Call(_, _, key_args, _) = map_key else {
            panic!("expected nested constructor in map key, got {map_key:?}");
        };
        assert!(
            matches!(key_args[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "map key constructor payload should infer Option<int> from written generic type, got {:?}",
            key_args[0]
        );
        let EExpr::Call(_, _, value_args, _) = map_value else {
            panic!("expected nested constructor in map value, got {map_value:?}");
        };
        assert!(
            matches!(value_args[0].ty(), Ty::Enum(name, _) if name == "Option<bool>"),
            "map value constructor payload should infer Option<bool> from written generic type, got {:?}",
            value_args[0]
        );

        let resolved_relation = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::SetLit(Ty::Error, vec![nested_some], None),
            &Ty::Relation(vec![nested_option]),
        );
        let EExpr::SetLit(_, relation_items, _) = resolved_relation else {
            panic!("expected relation literal");
        };
        let EExpr::Call(_, _, relation_args, _) = &relation_items[0] else {
            panic!(
                "expected nested constructor in relation, got {:?}",
                relation_items[0]
            );
        };
        assert!(
            matches!(relation_args[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "relation row constructor payload should infer Option<int> from written generic type, got {:?}",
            relation_args[0]
        );
    }

    #[test]
    fn resolve_expr_falls_back_when_tuple_expected_arity_does_not_match() {
        let ctx = ctx_with_monomorphized_options();
        let resolved = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::TupleLit(
                Ty::Error,
                vec![
                    EExpr::Lit(int_ty(), Literal::Int(1), None),
                    EExpr::Lit(bool_ty(), Literal::Bool(true), None),
                ],
                None,
            ),
            &Ty::Tuple(vec![Ty::Named("Option<int>".to_owned())]),
        );

        let EExpr::TupleLit(_, elements, _) = resolved else {
            panic!("expected tuple literal");
        };
        assert_eq!(
            elements.len(),
            2,
            "mismatched expected tuple arity should not truncate resolved tuple elements"
        );
        assert!(
            matches!(elements[0].ty(), Ty::Builtin(BuiltinTy::Int)),
            "fallback resolution should preserve first literal type, got {:?}",
            elements[0]
        );
        assert!(
            matches!(elements[1].ty(), Ty::Builtin(BuiltinTy::Bool)),
            "fallback resolution should preserve second literal type, got {:?}",
            elements[1]
        );
    }

    #[test]
    fn resolve_expr_uses_written_expected_type_for_tuple_constructor_payloads() {
        let ctx = ctx_with_monomorphized_options();
        let nested_option = Ty::Param(
            "Option".to_owned(),
            vec![Ty::Param("Option".to_owned(), vec![int_ty()])],
        );

        let resolved = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::TupleLit(
                Ty::Error,
                vec![EExpr::Call(
                    Ty::Error,
                    Box::new(var("Some", Ty::Error)),
                    vec![var("None", Ty::Error)],
                    None,
                )],
                None,
            ),
            &Ty::Tuple(vec![nested_option]),
        );

        let EExpr::TupleLit(_, elements, _) = resolved else {
            panic!("expected tuple literal");
        };
        let EExpr::Call(_, _, args, _) = &elements[0] else {
            panic!(
                "expected nested constructor in tuple, got {:?}",
                elements[0]
            );
        };
        assert!(
            matches!(args[0].ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "tuple element constructor payload should infer Option<int> from written generic type, got {:?}",
            args[0]
        );
    }

    #[test]
    fn resolve_expr_rejects_expected_constructor_non_members_and_wrong_scopes() {
        let ctx = ctx_with_status_types();
        let expected = Ty::Named("Status".to_owned());

        assert!(
            expected_constructor_call(&ctx, &expected, &var("Missing", Ty::Error)).is_none(),
            "unqualified constructors must belong to the expected enum"
        );
        assert!(
            expected_constructor_call(
                &ctx,
                &expected,
                &EExpr::Qual(Ty::Error, "Outcome".to_owned(), "Open".to_owned(), None),
            )
            .is_none(),
            "qualified constructors must use the expected enum scope"
        );
        assert!(
            expected_constructor_call(
                &ctx,
                &expected,
                &EExpr::Qual(Ty::Error, "Status".to_owned(), "Missing".to_owned(), None),
            )
            .is_none(),
            "qualified constructors must belong to the expected enum"
        );

        let mut env = Env::new();
        env.types.insert(
            "Commerce::Status".to_owned(),
            Ty::Enum(
                "Commerce::Status".to_owned(),
                vec!["Open".to_owned(), "Closed".to_owned()],
            ),
        );
        let module_ctx = Ctx::from_env(&env);
        assert!(
            expected_constructor_call(
                &module_ctx,
                &Ty::Named("Commerce::Status".to_owned()),
                &EExpr::Qual(Ty::Error, "Status".to_owned(), "Open".to_owned(), None),
            )
            .is_some(),
            "bare qualified scope should match a module-qualified enum name"
        );
    }

    #[test]
    fn resolve_expr_selects_expected_constructor_payloads_by_variant_name() {
        let mut env = Env::new();
        env.types.insert(
            "Result".to_owned(),
            Ty::Enum(
                "Result".to_owned(),
                vec!["Done".to_owned(), "Failed".to_owned()],
            ),
        );
        env.variant_fields.insert(
            "Result".to_owned(),
            vec![
                ("Done".to_owned(), vec![("value".to_owned(), int_ty())]),
                ("Failed".to_owned(), vec![("reason".to_owned(), bool_ty())]),
            ],
        );
        let ctx = Ctx::from_env(&env);

        let constructor = expected_constructor_call(
            &ctx,
            &Ty::Named("Result".to_owned()),
            &var("Done", Ty::Error),
        )
        .expect("Done should be a Result constructor");

        assert!(
            matches!(
                constructor.payload_tys.as_slice(),
                [Ty::Builtin(BuiltinTy::Int)]
            ),
            "Done payload should be selected by variant name, got {:?}",
            constructor.payload_tys
        );
    }

    #[test]
    fn resolve_expr_uses_wrapped_generic_expected_constructor_payloads() {
        let ctx = ctx_with_monomorphized_options();
        let nested_option = Ty::Param(
            "Option".to_owned(),
            vec![Ty::Param("Option".to_owned(), vec![int_ty()])],
        );

        for written_expected in [
            Ty::Alias("AliasOption".to_owned(), Box::new(nested_option.clone())),
            Ty::Newtype("NewOption".to_owned(), Box::new(nested_option.clone())),
            Ty::Refinement(
                Box::new(nested_option.clone()),
                Box::new(EExpr::Lit(bool_ty(), Literal::Bool(true), None)),
            ),
        ] {
            let constructor =
                expected_constructor_call(&ctx, &written_expected, &var("Some", Ty::Error))
                    .expect("wrapped generic option should resolve constructor payloads");

            assert!(
                matches!(constructor.payload_tys.as_slice(), [Ty::Enum(name, _)] if name == "Option<int>"),
                "wrapped generic constructor payload should resolve to Option<int>, got {:?}",
                constructor.payload_tys
            );
        }
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_constructor_call_payloads() {
        let ctx = ctx_with_monomorphized_options();
        let resolved = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::Call(
                Ty::Error,
                Box::new(var("Some", Ty::Error)),
                vec![var("None", Ty::Error)],
                None,
            ),
            &Ty::Param(
                "Option".to_owned(),
                vec![Ty::Param("Option".to_owned(), vec![int_ty()])],
            ),
        );

        let EExpr::Call(ref call_ty, callee, args, _) = resolved else {
            panic!("expected constructor call");
        };
        assert!(
            matches!(call_ty, Ty::Enum(name, _) if name == "Option<Option<int>>"),
            "constructor call should infer Option<Option<int>>, got {call_ty:?}"
        );
        assert!(
            matches!(callee.as_ref(), EExpr::Var(Ty::Enum(name, _), ctor, _) if name == "Option<Option<int>>" && ctor == "Some"),
            "constructor callee should infer Option<Option<int>>::Some, got {callee:?}"
        );
        let payload = args.first().expect("constructor payload");
        assert!(
            matches!(payload.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "constructor payload should infer Option<int>, got {payload:?}"
        );
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_qualified_constructor_call_payloads() {
        let ctx = ctx_with_monomorphized_options();
        let resolved = resolve_expr_with_expected_type(
            &ctx,
            &HashMap::new(),
            &EExpr::Call(
                Ty::Error,
                Box::new(EExpr::Qual(
                    Ty::Error,
                    "Option".to_owned(),
                    "Some".to_owned(),
                    None,
                )),
                vec![EExpr::Qual(
                    Ty::Error,
                    "Option".to_owned(),
                    "None".to_owned(),
                    None,
                )],
                None,
            ),
            &Ty::Param(
                "Option".to_owned(),
                vec![Ty::Param("Option".to_owned(), vec![int_ty()])],
            ),
        );

        let EExpr::Call(ref call_ty, callee, args, _) = resolved else {
            panic!("expected constructor call");
        };
        assert!(
            matches!(call_ty, Ty::Enum(name, _) if name == "Option<Option<int>>"),
            "constructor call should infer Option<Option<int>>, got {call_ty:?}"
        );
        assert!(
            matches!(callee.as_ref(), EExpr::Qual(Ty::Enum(name, _), scope, ctor, _) if name == "Option<Option<int>>" && scope == "Option" && ctor == "Some"),
            "qualified constructor callee should infer Option<Option<int>>::Some, got {callee:?}"
        );
        let payload = args.first().expect("constructor payload");
        assert!(
            matches!(payload.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "qualified constructor payload should infer Option<int>, got {payload:?}"
        );
    }

    #[test]
    fn resolve_expr_propagates_expected_type_into_if_branches() {
        let ctx = ctx_with_monomorphized_options();
        let mut bound = HashMap::new();
        bound.insert("flag".to_owned(), bool_ty());
        let resolved = resolve_expr_with_expected_type(
            &ctx,
            &bound,
            &EExpr::IfElse(
                Box::new(var("flag", Ty::Error)),
                Box::new(var("None", Ty::Error)),
                Some(Box::new(EExpr::Call(
                    Ty::Error,
                    Box::new(var("Some", Ty::Error)),
                    vec![EExpr::Lit(int_ty(), Literal::Int(1), None)],
                    None,
                ))),
                None,
            ),
            &Ty::Named("Option<int>".to_owned()),
        );

        let EExpr::IfElse(cond, then_branch, Some(else_branch), _) = resolved else {
            panic!("expected if expression");
        };
        assert!(
            matches!(cond.ty(), Ty::Builtin(BuiltinTy::Bool)),
            "condition should resolve from bound variables, got {cond:?}"
        );
        assert!(
            matches!(then_branch.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "then branch should infer Option<int>, got {then_branch:?}"
        );
        assert!(
            matches!(else_branch.ty(), Ty::Enum(name, _) if name == "Option<int>"),
            "else branch should infer Option<int>, got {else_branch:?}"
        );
    }

    #[test]
    fn resolve_expr_disambiguates_ctor_records_by_variant_field_names() {
        let mut env = Env::new();
        env.types.insert(
            "PaymentResult".to_owned(),
            Ty::Enum("PaymentResult".to_owned(), vec!["Done".to_owned()]),
        );
        env.types.insert(
            "ShippingResult".to_owned(),
            Ty::Enum("ShippingResult".to_owned(), vec!["Done".to_owned()]),
        );
        env.variant_fields.insert(
            "PaymentResult".to_owned(),
            vec![(
                "Done".to_owned(),
                vec![("receipt".to_owned(), Ty::Builtin(BuiltinTy::String))],
            )],
        );
        env.variant_fields.insert(
            "ShippingResult".to_owned(),
            vec![(
                "Done".to_owned(),
                vec![("tracking".to_owned(), Ty::Builtin(BuiltinTy::String))],
            )],
        );
        let ctx = Ctx::from_env(&env);

        let resolved = resolve_expr(
            &ctx,
            &HashMap::new(),
            &EExpr::CtorRecord(
                Ty::Named("Done".to_owned()),
                None,
                "Done".to_owned(),
                vec![(
                    "receipt".to_owned(),
                    EExpr::Lit(
                        Ty::Builtin(BuiltinTy::String),
                        Literal::Str("r-1".to_owned()),
                        None,
                    ),
                )],
                None,
            ),
        );

        assert!(
            matches!(resolved.ty(), Ty::Enum(name, _) if name == "PaymentResult"),
            "constructor record should resolve by matching field names, got {resolved:?}"
        );
    }

    #[test]
    fn resolve_expr_preserves_noncanonical_saw_paths_with_scope_segments() {
        let mut env = Env::new();
        env.aliases.insert(
            "Gateway::authorize".to_owned(),
            "Canonical::authorize".to_owned(),
        );
        let ctx = Ctx::from_env(&env);

        let resolved = resolve_expr(
            &ctx,
            &HashMap::new(),
            &EExpr::Saw(
                bool_ty(),
                "Gateway::authorize".to_owned(),
                "called".to_owned(),
                vec![],
                None,
            ),
        );

        assert!(
            matches!(&resolved, EExpr::Saw(_, sys, _, _, _) if sys == "Gateway::authorize"),
            "multi-segment saw paths should be preserved for validation, got {resolved:?}"
        );
    }

    #[test]
    fn resolve_comparison_ctor_from_context_respects_scope_and_constructor_membership() {
        let ctx = ctx_with_status_types();
        let expected = Ty::Enum(
            "Status".to_owned(),
            vec!["Open".to_owned(), "Closed".to_owned()],
        );

        let resolved =
            resolve_comparison_ctor_from_context(&ctx, var("Open", Ty::Error), &expected);
        assert!(
            matches!(resolved, EExpr::Var(Ty::Enum(name, _), ctor, _) if name == "Status" && ctor == "Open"),
            "unqualified constructor should resolve when it belongs to expected enum"
        );

        let resolved = resolve_comparison_ctor_from_context(
            &ctx,
            EExpr::Qual(Ty::Error, "Status".to_owned(), "Open".to_owned(), None),
            &expected,
        );
        assert!(
            matches!(resolved, EExpr::Qual(Ty::Enum(name, _), scope, ctor, _) if name == "Status" && scope == "Status" && ctor == "Open"),
            "qualified constructor should resolve when scope and constructor match"
        );

        let wrong_scope = resolve_comparison_ctor_from_context(
            &ctx,
            EExpr::Qual(Ty::Error, "Outcome".to_owned(), "Open".to_owned(), None),
            &expected,
        );
        assert!(
            matches!(wrong_scope, EExpr::Qual(Ty::Error, scope, ctor, _) if scope == "Outcome" && ctor == "Open"),
            "wrong enum scope must not be coerced to expected enum"
        );

        let wrong_qualified_ctor = resolve_comparison_ctor_from_context(
            &ctx,
            EExpr::Qual(Ty::Error, "Status".to_owned(), "Missing".to_owned(), None),
            &expected,
        );
        assert!(
            matches!(wrong_qualified_ctor, EExpr::Qual(Ty::Error, scope, ctor, _) if scope == "Status" && ctor == "Missing"),
            "qualified constructors outside the expected enum must not be coerced"
        );

        let wrong_ctor =
            resolve_comparison_ctor_from_context(&ctx, var("Missing", Ty::Error), &expected);
        assert!(
            matches!(wrong_ctor, EExpr::Var(Ty::Error, ctor, _) if ctor == "Missing"),
            "unknown constructor must not be coerced to expected enum"
        );
    }

    #[test]
    fn resolve_ctor_type_from_context_patches_only_matching_error_typed_constructors() {
        let status_ty = Ty::Enum(
            "Status".to_owned(),
            vec!["Open".to_owned(), "Closed".to_owned()],
        );

        let mut ctor_var = var("Open", Ty::Error);
        resolve_ctor_type_from_context(&mut ctor_var, &status_ty);
        assert!(
            matches!(ctor_var, EExpr::Var(Ty::Enum(name, _), ctor, _) if name == "Status" && ctor == "Open"),
            "matching error-typed constructor var should be patched"
        );

        let mut wrong_var = var("Missing", Ty::Error);
        resolve_ctor_type_from_context(&mut wrong_var, &status_ty);
        assert!(
            matches!(wrong_var, EExpr::Var(Ty::Error, ctor, _) if ctor == "Missing"),
            "non-member constructor var should not be patched"
        );

        let mut already_typed = var("Open", Ty::Builtin(BuiltinTy::String));
        resolve_ctor_type_from_context(&mut already_typed, &status_ty);
        assert!(
            matches!(already_typed, EExpr::Var(Ty::Builtin(BuiltinTy::String), ctor, _) if ctor == "Open"),
            "already typed constructor vars should not be overwritten"
        );

        let mut ctor_qual = EExpr::Qual(Ty::Error, "Status".to_owned(), "Open".to_owned(), None);
        resolve_ctor_type_from_context(&mut ctor_qual, &status_ty);
        assert!(
            matches!(ctor_qual, EExpr::Qual(Ty::Enum(name, _), scope, ctor, _) if name == "Status" && scope == "Status" && ctor == "Open"),
            "matching qualified constructors should be patched"
        );

        let mut wrong_scope_qual =
            EExpr::Qual(Ty::Error, "Outcome".to_owned(), "Open".to_owned(), None);
        resolve_ctor_type_from_context(&mut wrong_scope_qual, &status_ty);
        assert!(
            matches!(wrong_scope_qual, EExpr::Qual(Ty::Error, scope, ctor, _) if scope == "Outcome" && ctor == "Open"),
            "qualified constructors with the wrong scope should remain unresolved"
        );

        let mut wrong_member_qual =
            EExpr::Qual(Ty::Error, "Status".to_owned(), "Missing".to_owned(), None);
        resolve_ctor_type_from_context(&mut wrong_member_qual, &status_ty);
        assert!(
            matches!(wrong_member_qual, EExpr::Qual(Ty::Error, scope, ctor, _) if scope == "Status" && ctor == "Missing"),
            "qualified constructors outside the expected enum should remain unresolved"
        );

        let mut ctor_call =
            EExpr::Call(Ty::Error, Box::new(var("Closed", Ty::Error)), vec![], None);
        resolve_ctor_type_from_context(&mut ctor_call, &status_ty);
        assert!(
            matches!(
                ctor_call,
                EExpr::Call(Ty::Enum(ref call_ty, _), ref callee, _, _)
                    if call_ty == "Status"
                        && matches!(callee.as_ref(), EExpr::Var(Ty::Enum(name, _), ctor, _) if name == "Status" && ctor == "Closed")
            ),
            "matching constructor calls should patch both call and callee types"
        );

        let mut wrong_call =
            EExpr::Call(Ty::Error, Box::new(var("Missing", Ty::Error)), vec![], None);
        resolve_ctor_type_from_context(&mut wrong_call, &status_ty);
        assert!(
            matches!(
                wrong_call,
                EExpr::Call(Ty::Error, ref callee, _, _)
                    if matches!(callee.as_ref(), EExpr::Var(Ty::Error, ctor, _) if ctor == "Missing")
            ),
            "non-member constructor calls should remain unresolved"
        );

        let mut wrong_qualified_call = EExpr::Call(
            Ty::Error,
            Box::new(EExpr::Qual(
                Ty::Error,
                "Outcome".to_owned(),
                "Open".to_owned(),
                None,
            )),
            vec![],
            None,
        );
        resolve_ctor_type_from_context(&mut wrong_qualified_call, &status_ty);
        assert!(
            matches!(
                wrong_qualified_call,
                EExpr::Call(Ty::Error, ref callee, _, _)
                    if matches!(callee.as_ref(), EExpr::Qual(Ty::Error, scope, ctor, _) if scope == "Outcome" && ctor == "Open")
            ),
            "constructor calls with wrong qualified callee scope should remain unresolved"
        );

        let mut wrong_qualified_member_call = EExpr::Call(
            Ty::Error,
            Box::new(EExpr::Qual(
                Ty::Error,
                "Status".to_owned(),
                "Missing".to_owned(),
                None,
            )),
            vec![],
            None,
        );
        resolve_ctor_type_from_context(&mut wrong_qualified_member_call, &status_ty);
        assert!(
            matches!(
                wrong_qualified_member_call,
                EExpr::Call(Ty::Error, ref callee, _, _)
                    if matches!(callee.as_ref(), EExpr::Qual(Ty::Error, scope, ctor, _) if scope == "Status" && ctor == "Missing")
            ),
            "constructor calls with wrong qualified callee member should remain unresolved"
        );

        let mut qualified_call = EExpr::Call(
            Ty::Error,
            Box::new(EExpr::Qual(
                Ty::Error,
                "Status".to_owned(),
                "Closed".to_owned(),
                None,
            )),
            vec![],
            None,
        );
        resolve_ctor_type_from_context(&mut qualified_call, &status_ty);
        assert!(
            matches!(
                qualified_call,
                EExpr::Call(Ty::Enum(ref call_ty, _), ref callee, _, _)
                    if call_ty == "Status"
                        && matches!(callee.as_ref(), EExpr::Qual(Ty::Enum(name, _), scope, ctor, _) if name == "Status" && scope == "Status" && ctor == "Closed")
            ),
            "matching qualified constructor calls should patch both call and callee types"
        );

        let mut already_typed_call = EExpr::Call(
            Ty::Builtin(BuiltinTy::String),
            Box::new(var("Closed", Ty::Error)),
            vec![],
            None,
        );
        resolve_ctor_type_from_context(&mut already_typed_call, &status_ty);
        assert!(
            matches!(
                already_typed_call,
                EExpr::Call(Ty::Builtin(BuiltinTy::String), ref callee, _, _)
                    if matches!(callee.as_ref(), EExpr::Var(Ty::Error, ctor, _) if ctor == "Closed")
            ),
            "already typed constructor calls should not be overwritten"
        );

        let mut ctor_record = EExpr::CtorRecord(Ty::Error, None, "Open".to_owned(), vec![], None);
        resolve_ctor_type_from_context(&mut ctor_record, &status_ty);
        assert!(
            matches!(ctor_record, EExpr::CtorRecord(Ty::Enum(name, _), _, ctor, _, _) if name == "Status" && ctor == "Open"),
            "matching record constructors should be patched"
        );

        let mut wrong_record =
            EExpr::CtorRecord(Ty::Error, None, "Missing".to_owned(), vec![], None);
        resolve_ctor_type_from_context(&mut wrong_record, &status_ty);
        assert!(
            matches!(wrong_record, EExpr::CtorRecord(Ty::Error, _, ctor, _, _) if ctor == "Missing"),
            "non-member record constructors should remain unresolved"
        );
    }

    #[test]
    fn resolve_constructor_var_type_finds_unique_and_prefers_non_monomorphized() {
        let mut env = Env::new();
        env.types.insert(
            "Unique".to_owned(),
            Ty::Enum("Unique".to_owned(), vec!["Only".to_owned()]),
        );
        let unique_ctx = Ctx::from_env(&env);
        assert!(
            matches!(resolve_var_type(&unique_ctx, "Only"), Ty::Enum(name, _) if name == "Unique"),
            "unique constructor should resolve to its enum"
        );
        assert!(
            matches!(resolve_var_type(&unique_ctx, "Missing"), Ty::Error),
            "missing constructor should not resolve to an enum"
        );

        let mut env = Env::new();
        env.types.insert(
            "Option".to_owned(),
            Ty::Enum("Option".to_owned(), vec!["Some".to_owned()]),
        );
        env.types.insert(
            "Option<int>".to_owned(),
            Ty::Enum("Option<int>".to_owned(), vec!["Some".to_owned()]),
        );
        let generic_ctx = Ctx::from_env(&env);
        assert!(
            matches!(resolve_var_type(&generic_ctx, "Some"), Ty::Enum(name, _) if name == "Option"),
            "shared constructor should prefer the non-monomorphized enum"
        );

        let mut env = Env::new();
        env.types.insert(
            "Option<int>".to_owned(),
            Ty::Enum("Option<int>".to_owned(), vec!["Some".to_owned()]),
        );
        let monomorphized_ctx = Ctx::from_env(&env);
        assert!(
            matches!(resolve_var_type(&monomorphized_ctx, "Some"), Ty::Enum(name, _) if name == "Option<int>"),
            "single monomorphized constructor match should still resolve"
        );
    }
}
