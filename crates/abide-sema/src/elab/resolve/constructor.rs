//! Constructor and scoped enum-path resolution helpers.

use std::collections::HashMap;

use super::monomorphize::substitute_ty;
use super::Ctx;
use crate::elab::types::{EExpr, Ty};

pub(super) struct ExpectedConstructorCall {
    pub(super) expected_ty: Ty,
    pub(super) payload_tys: Vec<Ty>,
}

impl ExpectedConstructorCall {
    pub(super) fn resolve_callee(&self, callee: &EExpr) -> EExpr {
        match callee {
            EExpr::Var(_, ctor, sp) => EExpr::Var(self.expected_ty.clone(), ctor.clone(), *sp),
            EExpr::Qual(_, scope, ctor, sp) => {
                EExpr::Qual(self.expected_ty.clone(), scope.clone(), ctor.clone(), *sp)
            }
            other => other.clone(),
        }
    }
}

pub(super) fn expected_constructor_call(
    ctx: &Ctx,
    written_expected_ty: &Ty,
    callee: &EExpr,
) -> Option<ExpectedConstructorCall> {
    let expected_ty = expected_constructor_ty(ctx, written_expected_ty);
    let ctor_name = expected_enum_constructor_name(&expected_ty, callee)?;
    let Ty::Enum(enum_name, _) = &expected_ty else {
        return None;
    };
    let payload_tys =
        expected_constructor_payload_types(ctx, written_expected_ty, enum_name, &ctor_name);
    Some(ExpectedConstructorCall {
        expected_ty,
        payload_tys,
    })
}

fn expected_constructor_ty(ctx: &Ctx, written_expected_ty: &Ty) -> Ty {
    match ctx.resolve_ty(written_expected_ty) {
        Ty::Alias(_, inner) | Ty::Newtype(_, inner) | Ty::Refinement(inner, _) => {
            expected_constructor_ty(ctx, &inner)
        }
        ty => ty,
    }
}

fn expected_enum_constructor_name(expected_ty: &Ty, callee: &EExpr) -> Option<String> {
    let Ty::Enum(enum_name, constructors) = expected_ty else {
        return None;
    };
    match callee {
        EExpr::Var(_, ctor, _) if constructors.iter().any(|candidate| candidate == ctor) => {
            Some(ctor.clone())
        }
        EExpr::Qual(_, scope, ctor, _)
            if enum_scope_matches(enum_name, scope)
                && constructors.iter().any(|candidate| candidate == ctor) =>
        {
            Some(ctor.clone())
        }
        _ => None,
    }
}

fn expected_constructor_payload_types(
    ctx: &Ctx,
    written_expected_ty: &Ty,
    enum_name: &str,
    ctor_name: &str,
) -> Vec<Ty> {
    if let Some(payload_tys) = ctx.variant_fields.get(enum_name).and_then(|variants| {
        variants
            .iter()
            .find(|(variant, _)| variant == ctor_name)
            .map(|(_, fields)| {
                fields
                    .iter()
                    .map(|(_, ty)| ctx.resolve_ty(ty))
                    .collect::<Vec<_>>()
            })
    }) {
        return payload_tys;
    }

    expected_generic_constructor_payload_types(ctx, written_expected_ty, ctor_name)
        .unwrap_or_default()
}

fn expected_generic_constructor_payload_types(
    ctx: &Ctx,
    written_expected_ty: &Ty,
    ctor_name: &str,
) -> Option<Vec<Ty>> {
    match written_expected_ty {
        Ty::Param(generic_name, args) => {
            let generic = ctx.generic_types.get(generic_name.as_str())?;
            if args.len() != generic.type_params.len() {
                return None;
            }
            let subst: HashMap<String, Ty> = generic
                .type_params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| (param.clone(), ctx.resolve_ty(arg)))
                .collect();
            generic
                .variant_fields
                .iter()
                .find(|(variant, _)| variant == ctor_name)
                .map(|(_, fields)| {
                    fields
                        .iter()
                        .map(|(_, ty)| ctx.resolve_ty(&substitute_ty(ty, &subst)))
                        .collect()
                })
        }
        Ty::Alias(_, inner) | Ty::Newtype(_, inner) | Ty::Refinement(inner, _) => {
            expected_generic_constructor_payload_types(ctx, inner, ctor_name)
        }
        _ => None,
    }
}

pub(super) fn resolve_comparison_ctor_from_context(
    ctx: &Ctx,
    expr: EExpr,
    expected_ty: &Ty,
) -> EExpr {
    let expected_ty = ctx.resolve_ty(expected_ty);
    let Ty::Enum(enum_name, ctors) = &expected_ty else {
        return expr;
    };
    match expr {
        EExpr::Qual(_, scope, ctor, sp)
            if enum_scope_matches(enum_name, &scope) && ctors.iter().any(|c| c == &ctor) =>
        {
            EExpr::Qual(expected_ty, scope, ctor, sp)
        }
        EExpr::Var(ty, ctor, sp) if matches!(ty, Ty::Error) && ctors.iter().any(|c| c == &ctor) => {
            EExpr::Var(expected_ty, ctor, sp)
        }
        other => other,
    }
}

fn enum_scope_matches(concrete_enum: &str, written_scope: &str) -> bool {
    let concrete_base = enum_name_without_args(concrete_enum);
    concrete_base == written_scope
        || concrete_base
            .rsplit_once("::")
            .is_some_and(|(_, bare)| bare == written_scope)
}

fn enum_name_without_args(name: &str) -> &str {
    name.split_once('<').map_or(name, |(base, _)| base)
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

/// When a constructor expression has an unresolved or generic-base type
/// (e.g. `@None`, `@Option::None`), use the expected enum type to resolve it.
pub(super) fn resolve_ctor_type_from_context(expr: &mut EExpr, field_ty: &Ty) {
    let Ty::Enum(enum_name, ctors) = field_ty else {
        return;
    };
    match expr {
        EExpr::Var(ref mut ty, name, _)
            if can_patch_constructor_ty(ty) && ctors.iter().any(|ctor| ctor == name) =>
        {
            *ty = field_ty.clone();
        }
        EExpr::Qual(ref mut ty, scope, name, _)
            if can_patch_constructor_ty(ty)
                && enum_scope_matches(enum_name, scope)
                && ctors.iter().any(|ctor| ctor == name) =>
        {
            *ty = field_ty.clone();
        }
        EExpr::Call(ref mut ty, ref mut callee, _, _) if matches!(ty, Ty::Error) => {
            if patch_constructor_callee(callee, enum_name, ctors, field_ty) {
                *ty = field_ty.clone();
            }
        }
        EExpr::CtorRecord(ref mut ty, _, name, _, _)
            if can_patch_constructor_ty(ty) && ctors.iter().any(|ctor| ctor == name) =>
        {
            *ty = field_ty.clone();
        }
        _ => {}
    }
}

fn patch_constructor_callee(
    callee: &mut EExpr,
    enum_name: &str,
    ctors: &[String],
    field_ty: &Ty,
) -> bool {
    match callee {
        EExpr::Var(ref mut ty, name, _)
            if can_patch_constructor_ty(ty) && ctors.iter().any(|ctor| ctor == name) =>
        {
            *ty = field_ty.clone();
            true
        }
        EExpr::Qual(ref mut ty, scope, name, _)
            if can_patch_constructor_ty(ty)
                && enum_scope_matches(enum_name, scope)
                && ctors.iter().any(|ctor| ctor == name) =>
        {
            *ty = field_ty.clone();
            true
        }
        _ => false,
    }
}

fn can_patch_constructor_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Error | Ty::Named(_))
}

fn find_constructor_type(ctx: &Ctx, name: &str) -> Option<Ty> {
    let mut matches: Vec<&Ty> = Vec::new();
    for ty in ctx.types.values() {
        if let Ty::Enum(_, ctors) = ty {
            if ctors.iter().any(|c| c == name) {
                matches.push(ty);
            }
        }
    }
    if matches.is_empty() {
        return None;
    }
    if matches.len() == 1 {
        return Some(matches[0].clone());
    }

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
    match non_mono.as_slice() {
        [only] => Some((*only).clone()),
        [] => {
            // All matches are monomorphized instances of generic(s).
            // Don't pick arbitrarily — leave unresolved for context-driven resolution.
            None
        }
        [first, ..] => {
            // Multiple non-monomorphized matches — pre-existing ambiguity, return first.
            Some((*first).clone())
        }
    }
}
