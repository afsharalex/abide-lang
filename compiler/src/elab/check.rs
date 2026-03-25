//! Pass 3: Type-check expressions and validate well-formedness.
//!
//! Validates: field defaults match types, requires is Bool,
//! primed assignments target known fields, system uses reference known entities.

use super::env::Env;
use super::error::{ElabError, ErrorKind};
use super::types::{
    BuiltinTy, EAction, EEntity, EExpr, EField, ESystem, EType, EVariant, ElabResult, Ty,
};

/// Type-check the resolved environment.
/// Returns an `ElabResult` with all elaborated declarations + any errors.
pub fn check(env: &Env) -> (ElabResult, Vec<ElabError>) {
    let mut errors = Vec::new();

    for ty in env.types.values() {
        errors.extend(check_type(ty));
    }
    for entity in env.entities.values() {
        errors.extend(check_entity(entity));
    }
    for system in env.systems.values() {
        errors.extend(check_system(env, system));
    }

    let result = ElabResult {
        types: env
            .types
            .iter()
            .map(|(name, ty)| mk_etype(name, ty))
            .collect(),
        entities: env.entities.values().cloned().collect(),
        systems: env.systems.values().cloned().collect(),
        preds: env.preds.values().cloned().collect(),
        props: env.props.values().cloned().collect(),
        verifies: env.verifies.clone(),
        scenes: env.scenes.clone(),
        proofs: env.proofs.clone(),
        lemmas: env.lemmas.clone(),
        consts: env.consts.clone(),
        fns: env.fns.clone(),
    };

    (result, errors)
}

fn mk_etype(name: &str, ty: &Ty) -> EType {
    match ty {
        Ty::Enum(_, vs) => EType {
            name: name.to_owned(),
            variants: vs.iter().map(|v| EVariant::Simple(v.clone())).collect(),
            ty: ty.clone(),
        },
        Ty::Record(_, fs) => EType {
            name: name.to_owned(),
            variants: vec![EVariant::Record(name.to_owned(), fs.clone())],
            ty: ty.clone(),
        },
        _ => EType {
            name: name.to_owned(),
            variants: Vec::new(),
            ty: ty.clone(),
        },
    }
}

// ── Type well-formedness ─────────────────────────────────────────────

fn check_type(ty: &Ty) -> Vec<ElabError> {
    match ty {
        Ty::Enum(name, ctors) => {
            let dups = find_duplicates(ctors);
            dups.iter()
                .map(|d| {
                    ElabError::new(
                        ErrorKind::DuplicateDecl,
                        format!("duplicate constructor {d} in type {name}"),
                        format!("type {name}"),
                    )
                })
                .collect()
        }
        Ty::Record(name, fields) => {
            let field_names: Vec<&String> = fields.iter().map(|(n, _)| n).collect();
            let dups = find_duplicates(&field_names);
            dups.iter()
                .map(|d| {
                    ElabError::new(
                        ErrorKind::DuplicateDecl,
                        format!("duplicate field {d} in record {name}"),
                        format!("type {name}"),
                    )
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

// ── Entity well-formedness ───────────────────────────────────────────

fn check_entity(entity: &EEntity) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for field in &entity.fields {
        errors.extend(check_field(&entity.name, field));
    }
    for action in &entity.actions {
        errors.extend(check_action(entity, action));
    }

    errors
}

fn check_field(entity_name: &str, field: &EField) -> Vec<ElabError> {
    let Some(ref def_expr) = field.default else {
        return Vec::new();
    };

    match (&field.ty, def_expr) {
        (Ty::Enum(_, ctors), EExpr::Var(_, v)) if !ctors.iter().any(|c| c == v) => {
            vec![ElabError::new(
                ErrorKind::InvalidDefault,
                format!("{v} is not a constructor of {}", field.ty.name()),
                format!("entity {entity_name}, field {}", field.name),
            )]
        }
        _ => Vec::new(),
    }
}

fn check_action(entity: &EEntity, action: &EAction) -> Vec<ElabError> {
    let ctx = format!("entity {}, action {}", entity.name, action.name);
    let mut errors = Vec::new();

    // Check requires are boolean-typed
    for req in &action.requires {
        if !is_bool_expr(req) {
            errors.push(ElabError::new(
                ErrorKind::TypeMismatch,
                "requires expression should be Bool",
                &ctx,
            ));
        }
    }

    // Check primed assignments target known fields
    for expr in &action.body {
        errors.extend(check_assignment(entity, &ctx, expr));
    }

    errors
}

fn check_assignment(entity: &EEntity, ctx: &str, expr: &EExpr) -> Vec<ElabError> {
    if let EExpr::Assign(_, lhs, _) = expr {
        if let EExpr::Prime(_, inner) = lhs.as_ref() {
            if let EExpr::Var(_, field_name) = inner.as_ref() {
                let field_names: Vec<&str> =
                    entity.fields.iter().map(|f| f.name.as_str()).collect();
                if !field_names.contains(&field_name.as_str()) {
                    return vec![ElabError::new(
                        ErrorKind::InvalidPrime,
                        format!("{field_name} is not a field of {}", entity.name),
                        ctx,
                    )];
                }
            }
        }
    }
    Vec::new()
}

// ── System well-formedness ───────────────────────────────────────────

fn check_system(env: &Env, system: &ESystem) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for entity_name in &system.uses {
        if env.lookup_entity(entity_name).is_none() {
            errors.push(ElabError::new(
                ErrorKind::UndefinedRef,
                format!("system {} uses unknown entity {entity_name}", system.name),
                format!("system {}", system.name),
            ));
        }
    }

    for scope in &system.scopes {
        if scope.lo < 0 || scope.hi < scope.lo {
            errors.push(ElabError::new(
                ErrorKind::InvalidScope,
                format!(
                    "scope {} has invalid range {}..{}",
                    scope.entity, scope.lo, scope.hi
                ),
                format!("system {}", system.name),
            ));
        }
    }

    errors
}

// ── Helpers ──────────────────────────────────────────────────────────

fn is_bool_expr(e: &EExpr) -> bool {
    match e.ty() {
        Ty::Builtin(BuiltinTy::Bool) | Ty::Unresolved(_) => true, // might be Bool; don't error
        _ => false,
    }
}

fn find_duplicates<T: PartialEq>(items: &[T]) -> Vec<&T> {
    let mut dups = Vec::new();
    for (i, item) in items.iter().enumerate() {
        if items[..i].contains(item) && !dups.contains(&item) {
            dups.push(item);
        }
    }
    dups
}
