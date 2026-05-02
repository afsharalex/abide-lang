//! Entity well-formedness checking.

use super::super::error::{ElabError, ErrorKind};
use super::super::types::{BuiltinTy, EAction, EEntity, EExpr, EField, Ty};

pub(super) fn check_entity(entity: &EEntity, all_known_names: &[String]) -> Vec<ElabError> {
    let mut errors = Vec::new();

    for field in &entity.fields {
        errors.extend(check_field(&entity.name, field));
    }
    for action in &entity.actions {
        errors.extend(check_action(entity, action, all_known_names));
    }
    // invariants are safety-only — liveness
    // temporal operators (`eventually`, `until`, `previously`, `since`)
    // are not allowed in invariant bodies.
    for inv in &entity.invariants {
        check_invariant_body_no_liveness(&inv.body, &mut errors);
    }

    errors
}

/// walk an invariant body and emit
/// `INVARIANT_LIVENESS_NOT_ALLOWED` for any liveness temporal
/// operator. The forbidden set is the full list:
///
/// - **Future-time liveness:** `eventually`, `until` (and `next`,
///   `releases` once those are added to the expression language).
/// - **Past-time liveness:** `previously`, `since`.
///
/// Safety operators (`always` — implicit per, `historically`,
/// `once`) are explicitly allowed and recurse normally.
pub(super) fn check_invariant_body_no_liveness(expr: &EExpr, errors: &mut Vec<ElabError>) {
    fn walk(e: &EExpr, errors: &mut Vec<ElabError>) {
        match e {
            EExpr::Eventually(_, _, sp)
            | EExpr::Until(_, _, _, sp)
            | EExpr::Previously(_, _, sp)
            | EExpr::Since(_, _, _, sp) => {
                let kind = match e {
                    EExpr::Eventually(_, _, _) => "eventually",
                    EExpr::Until(_, _, _, _) => "until",
                    EExpr::Previously(_, _, _) => "previously",
                    EExpr::Since(_, _, _, _) => "since",
                    _ => unreachable!(),
                };
                let mut err = if let Some(span) = sp {
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `{kind}` is a liveness operator",
                            crate::messages::INVARIANT_LIVENESS_NOT_ALLOWED
                        ),
                        "invariant body".to_owned(),
                        *span,
                    )
                } else {
                    ElabError::new(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `{kind}` is a liveness operator",
                            crate::messages::INVARIANT_LIVENESS_NOT_ALLOWED
                        ),
                        "invariant body".to_owned(),
                    )
                };
                err.help = Some(crate::messages::HINT_INVARIANT_LIVENESS_NOT_ALLOWED.into());
                errors.push(err);
                // Continue walking to surface multiple violations.
                match e {
                    EExpr::Eventually(_, body, _) | EExpr::Previously(_, body, _) => {
                        walk(body, errors);
                    }
                    EExpr::Until(_, l, r, _) | EExpr::Since(_, l, r, _) => {
                        walk(l, errors);
                        walk(r, errors);
                    }
                    _ => unreachable!(),
                }
            }
            // Recurse through all other forms.
            EExpr::Always(_, body, _)
            | EExpr::Historically(_, body, _)
            | EExpr::Once(_, body, _)
            | EExpr::UnOp(_, _, body, _)
            | EExpr::Field(_, body, _, _)
            | EExpr::Prime(_, body, _)
            | EExpr::Card(_, body, _)
            | EExpr::Assert(_, body, _)
            | EExpr::Assume(_, body, _)
            | EExpr::NamedPair(_, _, body, _)
            | EExpr::Quant(_, _, _, _, body, _)
            | EExpr::Lam(_, _, body, _) => walk(body, errors),
            EExpr::Choose(_, _, _, predicate, _) => {
                if let Some(pred) = predicate {
                    walk(pred, errors);
                }
            }
            EExpr::BinOp(_, _, l, r, _)
            | EExpr::Assign(_, l, r, _)
            | EExpr::Seq(_, l, r, _)
            | EExpr::SameStep(_, l, r, _)
            | EExpr::In(_, l, r, _)
            | EExpr::Pipe(_, l, r, _)
            | EExpr::Index(_, l, r, _)
            | EExpr::MapUpdate(_, l, _, r, _) => {
                walk(l, errors);
                walk(r, errors);
            }
            EExpr::Call(_, callee, args, _) => {
                walk(callee, errors);
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::CallR(_, callee, refs, args, _) => {
                walk(callee, errors);
                for a in refs {
                    walk(a, errors);
                }
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::QualCall(_, _, _, args, _) => {
                for a in args {
                    walk(a, errors);
                }
            }
            EExpr::TupleLit(_, elems, _)
            | EExpr::SetLit(_, elems, _)
            | EExpr::SeqLit(_, elems, _) => {
                for el in elems {
                    walk(el, errors);
                }
            }
            EExpr::MapLit(_, entries, _) => {
                for (k, v) in entries {
                    walk(k, errors);
                    walk(v, errors);
                }
            }
            EExpr::SetComp(_, proj, _, _, body, _) => {
                if let Some(p) = proj {
                    walk(p, errors);
                }
                walk(body, errors);
            }
            EExpr::RelComp(_, projection, bindings, filter, _) => {
                walk(projection, errors);
                for binding in bindings {
                    if let Some(source) = &binding.source {
                        walk(source, errors);
                    }
                }
                walk(filter, errors);
            }
            EExpr::Match(scrut, arms, _) => {
                walk(scrut, errors);
                for (_, guard, body) in arms {
                    if let Some(g) = guard {
                        walk(g, errors);
                    }
                    walk(body, errors);
                }
            }
            EExpr::Let(bindings, body, _) => {
                for (_, _, init) in bindings {
                    walk(init, errors);
                }
                walk(body, errors);
            }
            EExpr::Saw(_, _, _, args, sp) => {
                let mut err = if let Some(span) = sp {
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `saw` is a past-time temporal operator",
                            crate::messages::SAW_NOT_ALLOWED_IN_INVARIANT
                        ),
                        "invariant body".to_owned(),
                        *span,
                    )
                } else {
                    ElabError::new(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: `saw` is a past-time temporal operator",
                            crate::messages::SAW_NOT_ALLOWED_IN_INVARIANT
                        ),
                        "invariant body".to_owned(),
                    )
                };
                err.help = Some(crate::messages::HINT_INVARIANT_LIVENESS_NOT_ALLOWED.into());
                errors.push(err);
                // Recurse into args to surface nested violations.
                for e in args.iter().flatten() {
                    walk(e, errors);
                }
            }
            EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
                for (_, fv) in fields {
                    walk(fv, errors);
                }
            }
            EExpr::Block(exprs, _) => {
                for ex in exprs {
                    walk(ex, errors);
                }
            }
            EExpr::VarDecl(_, _, init, rest, _) => {
                walk(init, errors);
                walk(rest, errors);
            }
            EExpr::While(cond, _contracts, body, _) => {
                walk(cond, errors);
                walk(body, errors);
            }
            EExpr::IfElse(cond, then_b, else_b, _) => {
                walk(cond, errors);
                walk(then_b, errors);
                if let Some(eb) = else_b {
                    walk(eb, errors);
                }
            }
            EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
                walk(body, errors);
                if let Some(f) = in_filter {
                    walk(f, errors);
                }
            }
            // Leaves: nothing to recurse into.
            EExpr::Lit(_, _, _)
            | EExpr::Var(_, _, _)
            | EExpr::Qual(_, _, _, _)
            | EExpr::Unresolved(_, _)
            | EExpr::Sorry(_)
            | EExpr::Todo(_) => {}
        }
    }
    walk(expr, errors);
}

pub(super) fn check_field(entity_name: &str, field: &EField) -> Vec<ElabError> {
    use crate::elab::types::EFieldDefault;

    let ctx_str = format!("entity {entity_name}, field {}", field.name);

    let def_expr = match &field.default {
        Some(EFieldDefault::Value(e)) => e,
        Some(EFieldDefault::In(es)) => {
            let mut errors = Vec::new();
            for e in es {
                // For enum fields: each value must be a valid constructor
                if let Ty::Enum(_, ctors) = &field.ty {
                    match e {
                        EExpr::Var(_, v, _) => {
                            if !ctors.iter().any(|c| c == v) {
                                errors.push(ElabError::new(
                                    ErrorKind::InvalidDefault,
                                    format!("{v} is not a constructor of {}", field.ty.name()),
                                    &ctx_str,
                                ));
                            }
                        }
                        _ => {
                            errors.push(ElabError::new(
                                ErrorKind::InvalidDefault,
                                crate::messages::in_value_not_constructor(field.ty.name()),
                                &ctx_str,
                            ));
                        }
                    }
                }
                // For non-enum fields: check type compatibility
                if let Ty::Builtin(_) = &field.ty {
                    let ok = super::expr_compatible_with_ty(e, &field.ty);
                    if !ok {
                        errors.push(ElabError::new(
                            ErrorKind::InvalidDefault,
                            format!(
                                "`in` value has type {}, expected {}",
                                e.ty().name(),
                                field.ty.name()
                            ),
                            &ctx_str,
                        ));
                    }
                }
            }
            return errors;
        }
        Some(EFieldDefault::Where(pred)) => {
            // `where` predicate must have Bool type
            let pred_ty = pred.ty();
            if !matches!(pred_ty, Ty::Builtin(BuiltinTy::Bool) | Ty::Error) {
                return vec![ElabError::new(
                    ErrorKind::InvalidDefault,
                    crate::messages::where_predicate_not_bool(pred_ty.name()),
                    &ctx_str,
                )];
            }
            return Vec::new();
        }
        None => return Vec::new(),
    };

    match (&field.ty, def_expr) {
        (Ty::Enum(_, ctors), EExpr::Var(_, v, _)) if !ctors.iter().any(|c| c == v) => {
            let err = if let Some(span) = field.span {
                ElabError::with_span(
                    ErrorKind::InvalidDefault,
                    format!("{v} is not a constructor of {}", field.ty.name()),
                    &ctx_str,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::InvalidDefault,
                    format!("{v} is not a constructor of {}", field.ty.name()),
                    &ctx_str,
                )
            };
            let help = if let Some(closest) = super::find_closest_name(v, ctors) {
                format!(
                    "did you mean '@{closest}'? Valid constructors: {}",
                    ctors.join(", ")
                )
            } else {
                format!("valid constructors: {}", ctors.join(", "))
            };
            vec![err.with_help(help)]
        }
        // Enum field with non-constructor expression (e.g., numeric literal)
        (Ty::Enum(name, ctors), _) if !matches!(def_expr, EExpr::Var(_, _, _)) => {
            vec![ElabError::new(
                ErrorKind::InvalidDefault,
                crate::messages::enum_default_not_constructor(name, &ctors.join(", ")),
                &ctx_str,
            )]
        }
        // Builtin type mismatch (e.g., Int literal for Bool field)
        (Ty::Builtin(_), _) => {
            let ok = super::expr_compatible_with_ty(def_expr, &field.ty);
            if ok {
                Vec::new()
            } else {
                vec![ElabError::new(
                    ErrorKind::InvalidDefault,
                    format!(
                        "default value has type {}, expected {}",
                        def_expr.ty().name(),
                        field.ty.name()
                    ),
                    &ctx_str,
                )]
            }
        }
        _ => Vec::new(),
    }
}

pub(super) fn check_action(
    entity: &EEntity,
    action: &EAction,
    all_known_names: &[String],
) -> Vec<ElabError> {
    let ctx = format!("entity {}, action {}", entity.name, action.name);
    let mut errors = Vec::new();

    // Check requires are boolean-typed
    for req in &action.requires {
        if !super::is_bool_expr(req) {
            let err = if let Some(span) = action.span {
                ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL,
                    &ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::TypeMismatch,
                    crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL,
                    &ctx,
                )
            };
            errors.push(err);
        }
    }

    // Check for unresolved uppercase names that might be missing @ prefix.
    // Known names include entity fields + all global names (types, constructors,
    // entities, preds, fns, consts) for broad "did you mean?" suggestions.
    let mut known: Vec<String> = entity.fields.iter().map(|f| f.name.clone()).collect();
    known.extend_from_slice(all_known_names);
    for req in &action.requires {
        super::check_unresolved_constructors(req, &ctx, action.span, &known, &mut errors);
    }

    // Check primed assignments target known fields
    for expr in &action.body {
        errors.extend(check_assignment(entity, action, &ctx, expr));
    }

    errors
}

fn check_assignment(entity: &EEntity, action: &EAction, ctx: &str, expr: &EExpr) -> Vec<ElabError> {
    if let EExpr::Assign(_, lhs, _, _) = expr {
        if let EExpr::Prime(_, inner, _) = lhs.as_ref() {
            if let EExpr::Var(_, field_name, _) = inner.as_ref() {
                let field_names: Vec<String> =
                    entity.fields.iter().map(|f| f.name.clone()).collect();
                let field_strs: Vec<&str> = field_names.iter().map(String::as_str).collect();
                if !field_strs.contains(&field_name.as_str()) {
                    let err = if let Some(span) = action.span {
                        ElabError::with_span(
                            ErrorKind::InvalidPrime,
                            format!("'{field_name}' is not a field of {}", entity.name),
                            ctx,
                            span,
                        )
                    } else {
                        ElabError::new(
                            ErrorKind::InvalidPrime,
                            format!("'{field_name}' is not a field of {}", entity.name),
                            ctx,
                        )
                    };
                    let help =
                        if let Some(closest) = super::find_closest_name(field_name, &field_names) {
                            format!("did you mean '{closest}'?")
                        } else {
                            crate::messages::HELP_PRIME_FIELDS_ONLY.to_owned()
                        };
                    return vec![err.with_help(help)];
                }
            }
        }
    }
    Vec::new()
}
