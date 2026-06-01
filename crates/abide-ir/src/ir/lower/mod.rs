//! Lower elaborated AST to Core IR.
//!
//! Desugars, resolves primed variables, computes frame conditions,
//! and produces a flat `IRProgram`.

mod expr;
mod qualify;
#[cfg(test)]
mod relation_expr;
mod system;

use expr::{card_from_text, lower_expr};
use system::{lower_extern, lower_system, synthesize_proc_entities};

use crate::elab::types as E;
use abide_core::diagnostic::{Diagnostic, DiagnosticSink};

use super::types::{
    IRAxiom, IRConst, IRDecreases, IREntity, IRExpr, IRField, IRFunction, IRLemma, IRProgram,
    IRRecordField, IRScene, IRSceneEvent, IRSceneGiven, IRTheorem, IRTransParam, IRTransRef,
    IRTransition, IRType, IRTypeEntry, IRUpdate, IRVerify, IRVerifySystem, LitVal,
};

/// Unwrap `Ty::Alias` wrappers to get to the underlying type.
///
/// `Alias("Positive", Refinement(Int, pred))` → `Refinement(Int, pred)`
/// This is needed because type aliases like `type Positive = Int { $ > 0 }`
/// are stored as `Alias("Positive", Refinement(...))`, and the lowering
/// needs to see the `Refinement` to extract `requires` clauses.
fn unwrap_alias(ty: &E::Ty) -> &E::Ty {
    let mut current = ty;
    while let E::Ty::Alias(_, inner) | E::Ty::Newtype(_, inner) = current {
        current = inner;
    }
    current
}

// ── Top-level lowering ───────────────────────────────────────────────

/// Resolve an alias to its canonical name, or return the name as-is.
fn canonical<'a>(aliases: &'a std::collections::HashMap<String, String>, name: &'a str) -> &'a str {
    aliases.get(name).map_or(name, String::as_str)
}

/// Diagnostics collected during IR lowering.
#[derive(Debug, Default)]
pub struct LowerDiagnostics {
    pub diagnostics: Vec<Diagnostic>,
}

impl LowerDiagnostics {
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }
}

pub fn lower(er: &E::ElabResult) -> (IRProgram, LowerDiagnostics) {
    let a = &er.aliases;

    // Build variant info map from elaborated types so that lower_ty can
    // carry constructor field information into IRType::Enum.
    let variant_info: VariantInfo<'_> = er
        .types
        .iter()
        .map(|t| (t.name.clone(), t.variants.as_slice()))
        .collect();
    // Collect newtype names so constructor calls can be made transparent.
    let newtypes: std::collections::HashSet<String> = er
        .types
        .iter()
        .filter(|t| matches!(t.ty, E::Ty::Newtype(_, _)))
        .map(|t| t.name.clone())
        .collect();
    let ctx = LowerCtx::new(&variant_info, newtypes);

    // All definitions (fn, pred, prop) are lowered uniformly into IRFunction.
    // pred is fn -> Bool with params. prop is nullary fn -> Bool.
    let mut functions: Vec<IRFunction> = Vec::new();
    for f in &er.fns {
        functions.push(lower_fn(f, &ctx));
    }
    for pred in &er.preds {
        functions.push(lower_pred(pred, &ctx));
    }
    for prop in &er.props {
        functions.push(lower_prop(prop, &ctx));
    }

    let mut entities: Vec<IREntity> = er.entities.iter().map(|e| lower_entity(e, &ctx)).collect();
    entities.extend(
        er.systems
            .iter()
            .flat_map(|s| synthesize_proc_entities(s, a, &ctx)),
    );
    let program = IRProgram {
        types: er.types.iter().map(|t| lower_type(t, &ctx)).collect(),
        constants: er.consts.iter().map(|c| lower_const(c, &ctx)).collect(),
        functions,
        entities,
        systems: er
            .systems
            .iter()
            .map(|s| lower_system(s, &er.systems, a, &ctx))
            .chain(er.externs.iter().map(|e| lower_extern(e, &ctx)))
            .collect(),
        verifies: er
            .verifies
            .iter()
            .map(|v| lower_verify(v, a, &ctx))
            .collect(),
        theorems: er
            .theorems
            .iter()
            .map(|t| lower_theorem(t, a, &ctx))
            .collect(),
        axioms: er.axioms.iter().map(|ax| lower_axiom(ax, &ctx)).collect(),
        lemmas: er.lemmas.iter().map(|l| lower_lemma(l, &ctx)).collect(),
        scenes: er.scenes.iter().map(|s| lower_scene(s, a, &ctx)).collect(),
    };

    (program, ctx.take_diagnostics())
}

// ── Lowering context ────────────────────────────────────────────────

type VariantInfo<'a> = std::collections::HashMap<String, &'a [E::EVariant]>;

/// Context threaded through all lowering functions. Carries variant
/// metadata for enum field lowering and accumulates diagnostics for
/// any issues discovered during lowering (e.g. unresolved types that
/// survived elaboration).
pub struct LowerCtx<'a> {
    pub variants: &'a VariantInfo<'a>,
    /// Names of newtype declarations. Used to detect newtype constructor
    /// calls during lowering and make them transparent (identity).
    pub newtypes: std::collections::HashSet<String>,
    pub diagnostics: std::cell::RefCell<DiagnosticSink>,
}

impl<'a> LowerCtx<'a> {
    fn new(variants: &'a VariantInfo<'a>, newtypes: std::collections::HashSet<String>) -> Self {
        Self {
            variants,
            newtypes,
            diagnostics: std::cell::RefCell::new(DiagnosticSink::new()),
        }
    }

    pub fn push_error(&self, message: String, span: Option<crate::span::Span>) {
        let mut diagnostic = Diagnostic::error(message).with_code("abide::lower");
        if let Some(span) = span {
            diagnostic = diagnostic.with_span(span);
        }
        self.diagnostics.borrow_mut().push(diagnostic);
    }

    fn take_diagnostics(self) -> LowerDiagnostics {
        LowerDiagnostics {
            diagnostics: self.diagnostics.into_inner().into_sorted_deduped(),
        }
    }
}

fn lower_type(et: &E::EType, ctx: &LowerCtx<'_>) -> IRTypeEntry {
    IRTypeEntry {
        name: et.name.clone(),
        ty: lower_ty(&et.ty, ctx),
    }
}

fn lower_ty(ty: &E::Ty, ctx: &LowerCtx<'_>) -> IRType {
    match ty {
        E::Ty::Enum(n, cs) => {
            // Look up field info from the elab variant map
            let variants = if let Some(elab_variants) = ctx.variants.get(n.as_str()) {
                elab_variants
                    .iter()
                    .map(|ev| match ev {
                        E::EVariant::Simple(name) => super::types::IRVariant::simple(name),
                        E::EVariant::Record(name, fields) => super::types::IRVariant {
                            name: name.clone(),
                            fields: fields
                                .iter()
                                .map(|(fname, fty)| super::types::IRVariantField {
                                    name: fname.clone(),
                                    ty: lower_ty(fty, ctx),
                                })
                                .collect(),
                        },
                        E::EVariant::Param(name, _tys) => super::types::IRVariant::simple(name),
                    })
                    .collect()
            } else {
                // Fallback: no elab info, treat all constructors as fieldless
                cs.iter().map(super::types::IRVariant::simple).collect()
            };
            IRType::Enum {
                name: n.clone(),
                variants,
            }
        }
        E::Ty::Record(n, fs) => IRType::Record {
            name: n.clone(),
            fields: fs
                .iter()
                .map(|(fn_, ft)| IRRecordField {
                    name: fn_.clone(),
                    ty: lower_ty(ft, ctx),
                })
                .collect(),
        },
        E::Ty::Alias(_, t) | E::Ty::Newtype(_, t) => lower_ty(t, ctx),
        E::Ty::Builtin(b) => lower_builtin(*b),
        E::Ty::Param(n, _) => {
            // After monomorphization, all generic type references should
            // be resolved to concrete Ty::Enum. If we reach here, either a generic
            // was used with wrong arity (already diagnosed) or monomorphization
            // missed a case. Emit a placeholder so compilation continues.
            ctx.push_error(
                format!("Ty::Param(`{n}`) reached IR lowering — should have been monomorphized"),
                None,
            );
            IRType::Record {
                name: n.clone(),
                fields: Vec::new(),
            }
        }
        E::Ty::Fn(a, b) => IRType::Fn {
            param: Box::new(lower_ty(a, ctx)),
            result: Box::new(lower_ty(b, ctx)),
        },
        E::Ty::Entity(n) => IRType::Entity { name: n.clone() },
        E::Ty::Named(n) => {
            if let Some(elab_variants) = ctx.variants.get(n.as_str()) {
                let variants = elab_variants
                    .iter()
                    .map(|variant| match variant {
                        E::EVariant::Simple(name)
                        | E::EVariant::Record(name, _)
                        | E::EVariant::Param(name, _) => super::types::IRVariant::simple(name),
                    })
                    .collect();
                return IRType::Enum {
                    name: n.clone(),
                    variants,
                };
            }
            ctx.push_error(format!("named type `{n}` reached IR lowering"), None);
            IRType::Int
        }
        E::Ty::Error => IRType::Int,
        E::Ty::Set(a) => IRType::Set {
            element: Box::new(lower_ty(a, ctx)),
        },
        E::Ty::Seq(a) => IRType::Seq {
            element: Box::new(lower_ty(a, ctx)),
        },
        E::Ty::Map(k, v) => IRType::Map {
            key: Box::new(lower_ty(k, ctx)),
            value: Box::new(lower_ty(v, ctx)),
        },
        E::Ty::Store(entity) => IRType::Set {
            element: Box::new(IRType::Entity {
                name: entity.clone(),
            }),
        },
        E::Ty::Relation(columns) => IRType::Set {
            element: Box::new(IRType::Tuple {
                elements: columns.iter().map(|column| lower_ty(column, ctx)).collect(),
            }),
        },
        E::Ty::Tuple(ts) => IRType::Tuple {
            elements: ts.iter().map(|t| lower_ty(t, ctx)).collect(),
        },
        E::Ty::Refinement(base, pred) => IRType::Refinement {
            base: Box::new(lower_ty(base, ctx)),
            predicate: Box::new(lower_expr(pred, ctx)),
        },
    }
}

fn lower_builtin(b: E::BuiltinTy) -> IRType {
    match b {
        E::BuiltinTy::Int => IRType::Int,
        E::BuiltinTy::Bool => IRType::Bool,
        E::BuiltinTy::String => IRType::String,
        E::BuiltinTy::Identity => IRType::Identity,
        E::BuiltinTy::Real => IRType::Real,
        E::BuiltinTy::Float => IRType::Float,
    }
}

// ── Constants and Functions ──────────────────────────────────────────

fn lower_const(ec: &E::EConst, ctx: &LowerCtx<'_>) -> IRConst {
    IRConst {
        name: ec.name.clone(),
        ty: lower_ty(&ec.body.ty(), ctx),
        value: lower_expr(&ec.body, ctx),
    }
}

fn lower_contracts(
    contracts: &[E::EContract],
    ctx: &LowerCtx<'_>,
) -> (Vec<IRExpr>, Vec<IRExpr>, Option<IRDecreases>) {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut decreases = None;
    for c in contracts {
        match c {
            E::EContract::Requires(e) => requires.push(lower_expr(e, ctx)),
            E::EContract::Ensures(e) => ensures.push(lower_expr(e, ctx)),
            E::EContract::Decreases { measures, star } => {
                decreases = Some(IRDecreases {
                    measures: measures.iter().map(|m| lower_expr(m, ctx)).collect(),
                    star: *star,
                });
            }
            E::EContract::Invariant(_) => {
                // Invariant contracts are handled separately (while loops)
            }
        }
    }
    (requires, ensures, decreases)
}

/// Extract invariants and decreases from while-loop contracts.
fn lower_while_contracts(
    contracts: &[E::EContract],
    ctx: &LowerCtx<'_>,
) -> (Vec<IRExpr>, Option<IRDecreases>) {
    let mut invariants = Vec::new();
    let mut decreases = None;
    for c in contracts {
        match c {
            E::EContract::Invariant(e) => invariants.push(lower_expr(e, ctx)),
            E::EContract::Decreases { measures, star } => {
                decreases = Some(IRDecreases {
                    measures: measures.iter().map(|m| lower_expr(m, ctx)).collect(),
                    star: *star,
                });
            }
            _ => {}
        }
    }
    (invariants, decreases)
}

fn lower_fn(ef: &E::EFn, ctx: &LowerCtx<'_>) -> IRFunction {
    // Extract refinement predicates from params, strip refinement from types.
    // Unwrap Alias wrappers so that alias-based refinements like `x: Positive`
    // (where `type Positive = Int { $ > 0 }`) are handled the same as inline
    // refinements like `x: Int { $ > 0 }`.
    let stripped_params: Vec<(String, E::Ty)> = ef
        .params
        .iter()
        .map(|(n, t)| match unwrap_alias(t) {
            E::Ty::Refinement(base, _) => (n.clone(), (**base).clone()),
            _ => (n.clone(), t.clone()),
        })
        .collect();
    let refinement_requires: Vec<IRExpr> = ef
        .params
        .iter()
        .filter_map(|(name, ty)| {
            if let E::Ty::Refinement(_, pred) = unwrap_alias(ty) {
                Some(lower_expr(&subst_dollar_elab(name, pred), ctx))
            } else {
                None
            }
        })
        .collect();
    let ret_ty = lower_ty(&ef.ret_ty, ctx);
    let fn_ty = stripped_params
        .iter()
        .rev()
        .fold(ret_ty.clone(), |acc, (_, pt)| IRType::Fn {
            param: Box::new(lower_ty(pt, ctx)),
            result: Box::new(acc),
        });
    let body = stripped_params
        .iter()
        .rev()
        .fold(lower_expr(&ef.body, ctx), |acc, (pn, pt)| IRExpr::Lam {
            param: pn.clone(),
            param_type: lower_ty(pt, ctx),
            body: Box::new(acc),
            span: ef.span,
        });
    let (mut requires, ensures, decreases) = lower_contracts(&ef.contracts, ctx);
    // Prepend refinement-derived requires before explicit contracts
    let mut all_requires = refinement_requires;
    all_requires.append(&mut requires);
    IRFunction {
        name: ef.name.clone(),
        ty: fn_ty,
        body,
        prop_target: None,
        requires: all_requires,
        ensures,
        decreases,
        span: ef.span,
        file: ef.file.clone(),
    }
}

/// Lower a pred to an `IRFunction`. `pred p(x: T) = body` becomes a curried
/// function returning Bool: `Lam(x, T, body)` with type `T -> Bool`.
fn lower_pred(ep: &E::EPred, ctx: &LowerCtx<'_>) -> IRFunction {
    let fn_ty = ep
        .params
        .iter()
        .rev()
        .fold(IRType::Bool, |acc, (_, pt)| IRType::Fn {
            param: Box::new(lower_ty(pt, ctx)),
            result: Box::new(acc),
        });
    let body = ep
        .params
        .iter()
        .rev()
        .fold(lower_expr(&ep.body, ctx), |acc, (pn, pt)| IRExpr::Lam {
            param: pn.clone(),
            param_type: lower_ty(pt, ctx),
            body: Box::new(acc),
            span: ep.span,
        });
    IRFunction {
        name: ep.name.clone(),
        ty: fn_ty,
        body,
        prop_target: None,
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: ep.span,
        file: ep.file.clone(),
    }
}

/// Lower a prop to an `IRFunction`. `prop p = body` becomes a nullary function
/// returning Bool: body is the expression, type is `Bool`.
fn lower_prop(ep: &E::EProp, ctx: &LowerCtx<'_>) -> IRFunction {
    IRFunction {
        name: ep.name.clone(),
        ty: IRType::Bool,
        body: lower_expr(&ep.body, ctx),
        prop_target: ep.target.clone(),
        requires: vec![],
        ensures: vec![],
        decreases: None,
        span: ep.span,
        file: ep.file.clone(),
    }
}

// ── Entities ─────────────────────────────────────────────────────────

fn lower_entity(ee: &E::EEntity, ctx: &LowerCtx<'_>) -> IREntity {
    IREntity {
        name: ee.name.clone(),
        fields: ee.fields.iter().map(|f| lower_field(f, ctx)).collect(),
        transitions: ee.actions.iter().map(|a| lower_action(a, ctx)).collect(),
        // lower entity-level derived fields.
        derived_fields: ee
            .derived_fields
            .iter()
            .map(|d| lower_derived_field(d, ctx))
            .collect(),
        // lower entity-level invariants.
        invariants: ee
            .invariants
            .iter()
            .map(|inv| lower_invariant(inv, ctx))
            .collect(),
        // lower fsm declarations. The verifier
        // consults `IREntity::fsm_decls` when encoding actions to
        // assert transition validity.
        fsm_decls: ee.fsm_decls.iter().map(lower_fsm).collect(),
    }
}

/// lower an elaborated derived field to its IR
/// form. The body lowering is identical to function-body lowering since
/// derived field bodies are pure expressions in the same expression
/// language as fn bodies.
fn lower_derived_field(d: &E::EDerived, ctx: &LowerCtx<'_>) -> crate::ir::types::IRDerivedField {
    crate::ir::types::IRDerivedField {
        name: d.name.clone(),
        body: lower_expr(&d.body, ctx),
        ty: lower_ty(&d.ty, ctx),
    }
}

/// lower an elaborated invariant to its IR form.
/// The body is a Boolean expression and is lowered with the same
/// machinery as derived field bodies and theorem invariants.
fn lower_invariant(inv: &E::EInvariant, ctx: &LowerCtx<'_>) -> crate::ir::types::IRInvariant {
    crate::ir::types::IRInvariant {
        name: inv.name.clone(),
        body: lower_expr(&inv.body, ctx),
    }
}

/// lower an elaborated fsm declaration to its IR
/// form. The elab-level row form (one source, N targets) is flattened
/// into separate `(from, to)` pairs so the verifier's per-action
/// validity check can iterate them as a flat allowlist.
fn lower_fsm(fsm: &E::EFsm) -> crate::ir::types::IRFsm {
    let mut transitions: Vec<crate::ir::types::IRFsmTransition> = Vec::new();
    for row in &fsm.rows {
        for tgt in &row.targets {
            transitions.push(crate::ir::types::IRFsmTransition {
                from: row.from.clone(),
                to: tgt.clone(),
            });
        }
    }
    crate::ir::types::IRFsm {
        field: fsm.field.clone(),
        enum_name: fsm.enum_name.clone(),
        transitions,
    }
}

/// flatten system fields into IRFields.
///
/// Primitive fields (Int, bool, enum) produce one IRField each.
/// Struct-typed fields are flattened: `ui: UiState = UiState { screen: @home, mode: @normal }`
/// becomes `[IRField("ui.screen",...), IRField("ui.mode",...)]`.
fn flatten_system_fields(fields: &[E::EField], ctx: &LowerCtx<'_>) -> Vec<IRField> {
    let mut out = Vec::new();
    for f in fields {
        match &f.ty {
            E::Ty::Record(_, sub_fields) => {
                // Extract per-sub-field defaults from the struct constructor.
                let ctor_defaults = extract_struct_ctor_defaults(&f.default);
                for (sub_name, sub_ty) in sub_fields {
                    let compound_name = format!("{}.{sub_name}", f.name);
                    let sub_default = ctor_defaults.get(sub_name.as_str());
                    let (default, initial_constraint) = match sub_default {
                        Some(e) => (Some(lower_expr(e, ctx)), None),
                        None => (None, None),
                    };
                    out.push(IRField {
                        name: compound_name,
                        ty: lower_ty(sub_ty, ctx),
                        default,
                        initial_constraint,
                    });
                }
            }
            _ => {
                out.push(lower_field(f, ctx));
            }
        }
    }
    out
}

/// Extract named field defaults from a StructCtor expression.
/// Returns a map of sub-field name → expression.
fn extract_struct_ctor_defaults(
    default: &Option<E::EFieldDefault>,
) -> std::collections::HashMap<&str, &E::EExpr> {
    let mut map = std::collections::HashMap::new();
    if let Some(E::EFieldDefault::Value(E::EExpr::StructCtor(_, _, fields, _))) = default {
        for (name, expr) in fields {
            map.insert(name.as_str(), expr);
        }
    }
    map
}

fn lower_field(ef: &E::EField, ctx: &LowerCtx<'_>) -> IRField {
    use crate::elab::types::EFieldDefault;
    let (default, initial_constraint) = match &ef.default {
        Some(EFieldDefault::Value(e)) => (Some(lower_expr(e, ctx)), None),
        Some(EFieldDefault::In(es)) => {
            // default = None: nondeterministic, so induction/IC3 treat as unconstrained
            // (stronger: proves safety for ALL possible initial values)
            // constraint = $ == a || $ == b ||...
            let dollar_var = IRExpr::Var {
                name: "$".to_owned(),
                ty: lower_ty(&ef.ty, ctx),
                span: None,
            };
            let mut disj: Option<IRExpr> = None;
            for e in es {
                let eq = IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(dollar_var.clone()),
                    right: Box::new(lower_expr(e, ctx)),
                    ty: crate::ir::types::IRType::Bool,
                    span: None,
                };
                disj = Some(match disj {
                    None => eq,
                    Some(prev) => IRExpr::BinOp {
                        op: "OpOr".to_owned(),
                        left: Box::new(prev),
                        right: Box::new(eq),
                        ty: crate::ir::types::IRType::Bool,
                        span: None,
                    },
                });
            }
            (None, disj)
        }
        Some(EFieldDefault::Where(e)) => (None, Some(lower_expr(e, ctx))),
        None => (None, None),
    };
    IRField {
        name: ef.name.clone(),
        ty: lower_ty(&ef.ty, ctx),
        default,
        initial_constraint,
    }
}

fn lower_action(ea: &E::EAction, ctx: &LowerCtx<'_>) -> IRTransition {
    // Extract refinement predicates from params and add to guard
    let refinement_reqs = extract_param_refinements(&ea.params);
    let mut all_requires: Vec<&E::EExpr> = refinement_reqs.iter().collect();
    all_requires.extend(ea.requires.iter());
    IRTransition {
        name: ea.name.clone(),
        refs: ea
            .refs
            .iter()
            .map(|(rn, rt)| IRTransRef {
                name: rn.clone(),
                entity: rt.name().to_owned(),
            })
            .collect(),
        params: ea
            .params
            .iter()
            .map(|(pn, pt)| {
                let base_ty = match unwrap_alias(pt) {
                    E::Ty::Refinement(base, _) => base.as_ref(),
                    _ => pt,
                };
                IRTransParam {
                    name: pn.clone(),
                    ty: lower_ty(base_ty, ctx),
                }
            })
            .collect(),
        guard: lower_guard_refs(&all_requires, ctx),
        updates: extract_updates(&ea.body, ctx),
        postcondition: if ea.ensures.is_empty() {
            None
        } else {
            Some(lower_guard_refs(
                &ea.ensures.iter().collect::<Vec<_>>(),
                ctx,
            ))
        },
    }
}

/// Extract refinement predicates from params, substituting $ with param name.
fn extract_param_refinements(params: &[(String, E::Ty)]) -> Vec<E::EExpr> {
    params
        .iter()
        .filter_map(|(name, ty)| {
            if let E::Ty::Refinement(_, pred) = unwrap_alias(ty) {
                Some(subst_dollar_elab(name, pred))
            } else {
                None
            }
        })
        .collect()
}

/// Substitute $ with a parameter name in an elaborated expression.
fn subst_dollar_elab(name: &str, expr: &E::EExpr) -> E::EExpr {
    match expr {
        E::EExpr::Var(ty, n, sp) if n == "$" => E::EExpr::Var(ty.clone(), name.to_owned(), *sp),
        E::EExpr::Lit(_, _, _)
        | E::EExpr::Var(_, _, _)
        | E::EExpr::Qual(_, _, _, _)
        | E::EExpr::Sorry(_)
        | E::EExpr::Todo(_) => expr.clone(),
        E::EExpr::Field(ty, inner, field, span) => E::EExpr::Field(
            ty.clone(),
            Box::new(subst_dollar_elab(name, inner)),
            field.clone(),
            *span,
        ),
        E::EExpr::Prime(ty, inner, span) => {
            E::EExpr::Prime(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::BinOp(ty, op, a, b, sp) => E::EExpr::BinOp(
            ty.clone(),
            *op,
            Box::new(subst_dollar_elab(name, a)),
            Box::new(subst_dollar_elab(name, b)),
            *sp,
        ),
        E::EExpr::UnOp(ty, op, inner, span) => E::EExpr::UnOp(
            ty.clone(),
            *op,
            Box::new(subst_dollar_elab(name, inner)),
            *span,
        ),
        E::EExpr::Call(ty, func, args, span) => E::EExpr::Call(
            ty.clone(),
            Box::new(subst_dollar_elab(name, func)),
            args.iter()
                .map(|arg| subst_dollar_elab(name, arg))
                .collect(),
            *span,
        ),
        E::EExpr::CallR(ty, func, args, refs, span) => E::EExpr::CallR(
            ty.clone(),
            Box::new(subst_dollar_elab(name, func)),
            args.iter()
                .map(|arg| subst_dollar_elab(name, arg))
                .collect(),
            refs.iter()
                .map(|reference| subst_dollar_elab(name, reference))
                .collect(),
            *span,
        ),
        E::EExpr::Quant(ty, quant, var, domain_ty, body, span) => E::EExpr::Quant(
            ty.clone(),
            *quant,
            var.clone(),
            domain_ty.clone(),
            if var == "$" {
                body.clone()
            } else {
                Box::new(subst_dollar_elab(name, body))
            },
            *span,
        ),
        E::EExpr::Always(ty, inner, span) => {
            E::EExpr::Always(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Eventually(ty, inner, span) => {
            E::EExpr::Eventually(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Until(ty, left, right, span) => E::EExpr::Until(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::Historically(ty, inner, span) => {
            E::EExpr::Historically(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Once(ty, inner, span) => {
            E::EExpr::Once(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Previously(ty, inner, span) => {
            E::EExpr::Previously(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Since(ty, left, right, span) => E::EExpr::Since(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::Assert(ty, inner, span) => {
            E::EExpr::Assert(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Assume(ty, inner, span) => {
            E::EExpr::Assume(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Assign(ty, left, right, span) => E::EExpr::Assign(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::NamedPair(ty, pair_name, inner, span) => E::EExpr::NamedPair(
            ty.clone(),
            pair_name.clone(),
            Box::new(subst_dollar_elab(name, inner)),
            *span,
        ),
        E::EExpr::Seq(ty, left, right, span) => E::EExpr::Seq(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::SameStep(ty, left, right, span) => E::EExpr::SameStep(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::Let(bindings, body, span) => {
            let mut shadowed = false;
            let bindings = bindings
                .iter()
                .map(|(binding_name, ty, value)| {
                    let value = if shadowed {
                        value.clone()
                    } else {
                        subst_dollar_elab(name, value)
                    };
                    if binding_name == "$" {
                        shadowed = true;
                    }
                    (binding_name.clone(), ty.clone(), value)
                })
                .collect();
            E::EExpr::Let(
                bindings,
                if shadowed {
                    body.clone()
                } else {
                    Box::new(subst_dollar_elab(name, body))
                },
                *span,
            )
        }
        E::EExpr::Lam(params, ret_ty, body, span) => E::EExpr::Lam(
            params.clone(),
            ret_ty.clone(),
            if params.iter().any(|(param, _)| param == "$") {
                body.clone()
            } else {
                Box::new(subst_dollar_elab(name, body))
            },
            *span,
        ),
        E::EExpr::Unresolved(unresolved, span) if unresolved == "$" => {
            E::EExpr::Unresolved(name.to_owned(), *span)
        }
        E::EExpr::Unresolved(_, _) => expr.clone(),
        E::EExpr::TupleLit(ty, elements, span) => E::EExpr::TupleLit(
            ty.clone(),
            elements
                .iter()
                .map(|element| subst_dollar_elab(name, element))
                .collect(),
            *span,
        ),
        E::EExpr::In(ty, left, right, span) => E::EExpr::In(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::Card(ty, inner, span) => {
            E::EExpr::Card(ty.clone(), Box::new(subst_dollar_elab(name, inner)), *span)
        }
        E::EExpr::Pipe(ty, left, right, span) => E::EExpr::Pipe(
            ty.clone(),
            Box::new(subst_dollar_elab(name, left)),
            Box::new(subst_dollar_elab(name, right)),
            *span,
        ),
        E::EExpr::Match(scrutinee, arms, span) => E::EExpr::Match(
            Box::new(subst_dollar_elab(name, scrutinee)),
            arms.iter()
                .map(|(pattern, guard, body)| {
                    if pattern_binds_elab_var(pattern, "$") {
                        (pattern.clone(), guard.clone(), body.clone())
                    } else {
                        (
                            pattern.clone(),
                            guard.as_ref().map(|guard| subst_dollar_elab(name, guard)),
                            subst_dollar_elab(name, body),
                        )
                    }
                })
                .collect(),
            *span,
        ),
        E::EExpr::Choose(ty, var, domain_ty, filter, span) => E::EExpr::Choose(
            ty.clone(),
            var.clone(),
            domain_ty.clone(),
            if var == "$" {
                filter.clone()
            } else {
                filter
                    .as_ref()
                    .map(|filter| Box::new(subst_dollar_elab(name, filter)))
            },
            *span,
        ),
        E::EExpr::MapUpdate(ty, map, key, value, span) => E::EExpr::MapUpdate(
            ty.clone(),
            Box::new(subst_dollar_elab(name, map)),
            Box::new(subst_dollar_elab(name, key)),
            Box::new(subst_dollar_elab(name, value)),
            *span,
        ),
        E::EExpr::Index(ty, map, key, span) => E::EExpr::Index(
            ty.clone(),
            Box::new(subst_dollar_elab(name, map)),
            Box::new(subst_dollar_elab(name, key)),
            *span,
        ),
        E::EExpr::SetComp(ty, source, var, domain_ty, filter, projection, span) => {
            let source = source
                .as_ref()
                .map(|source| Box::new(subst_dollar_elab(name, source)));
            E::EExpr::SetComp(
                ty.clone(),
                source,
                var.clone(),
                domain_ty.clone(),
                if var == "$" {
                    filter.clone()
                } else {
                    filter
                        .as_ref()
                        .map(|filter| Box::new(subst_dollar_elab(name, filter)))
                },
                if var == "$" {
                    projection.clone()
                } else {
                    Box::new(subst_dollar_elab(name, projection))
                },
                *span,
            )
        }
        E::EExpr::RelComp(ty, projection, bindings, filter, span) => {
            let mut shadowed = false;
            let bindings = bindings
                .iter()
                .map(|binding| {
                    let source = if shadowed {
                        binding.source.clone()
                    } else {
                        binding
                            .source
                            .as_ref()
                            .map(|source| Box::new(subst_dollar_elab(name, source)))
                    };
                    if binding.var == "$" {
                        shadowed = true;
                    }
                    E::ERelCompBinding {
                        var: binding.var.clone(),
                        domain: binding.domain.clone(),
                        source,
                    }
                })
                .collect();
            E::EExpr::RelComp(
                ty.clone(),
                if shadowed {
                    projection.clone()
                } else {
                    Box::new(subst_dollar_elab(name, projection))
                },
                bindings,
                if shadowed {
                    filter.clone()
                } else {
                    Box::new(subst_dollar_elab(name, filter))
                },
                *span,
            )
        }
        E::EExpr::SetLit(ty, elements, span) => E::EExpr::SetLit(
            ty.clone(),
            elements
                .iter()
                .map(|element| subst_dollar_elab(name, element))
                .collect(),
            *span,
        ),
        E::EExpr::SeqLit(ty, elements, span) => E::EExpr::SeqLit(
            ty.clone(),
            elements
                .iter()
                .map(|element| subst_dollar_elab(name, element))
                .collect(),
            *span,
        ),
        E::EExpr::MapLit(ty, entries, span) => E::EExpr::MapLit(
            ty.clone(),
            entries
                .iter()
                .map(|(key, value)| (subst_dollar_elab(name, key), subst_dollar_elab(name, value)))
                .collect(),
            *span,
        ),
        E::EExpr::QualCall(ty, qualifier, func, args, span) => E::EExpr::QualCall(
            ty.clone(),
            qualifier.clone(),
            func.clone(),
            args.iter()
                .map(|arg| subst_dollar_elab(name, arg))
                .collect(),
            *span,
        ),
        E::EExpr::Block(expressions, span) => E::EExpr::Block(
            expressions
                .iter()
                .map(|expression| subst_dollar_elab(name, expression))
                .collect(),
            *span,
        ),
        E::EExpr::VarDecl(var, ty, init, rest, span) => E::EExpr::VarDecl(
            var.clone(),
            ty.clone(),
            Box::new(subst_dollar_elab(name, init)),
            if var == "$" {
                rest.clone()
            } else {
                Box::new(subst_dollar_elab(name, rest))
            },
            *span,
        ),
        E::EExpr::While(cond, contracts, body, span) => E::EExpr::While(
            Box::new(subst_dollar_elab(name, cond)),
            contracts
                .iter()
                .map(|contract| subst_dollar_elab_contract(name, contract))
                .collect(),
            Box::new(subst_dollar_elab(name, body)),
            *span,
        ),
        E::EExpr::IfElse(cond, then_body, else_body, span) => E::EExpr::IfElse(
            Box::new(subst_dollar_elab(name, cond)),
            Box::new(subst_dollar_elab(name, then_body)),
            else_body
                .as_ref()
                .map(|else_body| Box::new(subst_dollar_elab(name, else_body))),
            *span,
        ),
        E::EExpr::Aggregate(ty, kind, var, domain_ty, body, in_filter, span) => {
            E::EExpr::Aggregate(
                ty.clone(),
                *kind,
                var.clone(),
                domain_ty.clone(),
                if var == "$" {
                    body.clone()
                } else {
                    Box::new(subst_dollar_elab(name, body))
                },
                if var == "$" {
                    in_filter.clone()
                } else {
                    in_filter
                        .as_ref()
                        .map(|in_filter| Box::new(subst_dollar_elab(name, in_filter)))
                },
                *span,
            )
        }
        E::EExpr::Saw(ty, system, event, args, span) => E::EExpr::Saw(
            ty.clone(),
            system.clone(),
            event.clone(),
            args.iter()
                .map(|arg| {
                    arg.as_ref()
                        .map(|arg| Box::new(subst_dollar_elab(name, arg)))
                })
                .collect(),
            *span,
        ),
        E::EExpr::CtorRecord(ty, qualifier, ctor, fields, span) => E::EExpr::CtorRecord(
            ty.clone(),
            qualifier.clone(),
            ctor.clone(),
            fields
                .iter()
                .map(|(field, value)| (field.clone(), subst_dollar_elab(name, value)))
                .collect(),
            *span,
        ),
        E::EExpr::StructCtor(ty, struct_name, fields, span) => E::EExpr::StructCtor(
            ty.clone(),
            struct_name.clone(),
            fields
                .iter()
                .map(|(field, value)| (field.clone(), subst_dollar_elab(name, value)))
                .collect(),
            *span,
        ),
    }
}

fn subst_dollar_elab_contract(name: &str, contract: &E::EContract) -> E::EContract {
    match contract {
        E::EContract::Requires(expr) => E::EContract::Requires(subst_dollar_elab(name, expr)),
        E::EContract::Ensures(expr) => E::EContract::Ensures(subst_dollar_elab(name, expr)),
        E::EContract::Invariant(expr) => E::EContract::Invariant(subst_dollar_elab(name, expr)),
        E::EContract::Decreases { measures, star } => E::EContract::Decreases {
            measures: measures
                .iter()
                .map(|measure| subst_dollar_elab(name, measure))
                .collect(),
            star: *star,
        },
    }
}

fn pattern_binds_elab_var(pattern: &E::EPattern, name: &str) -> bool {
    match pattern {
        E::EPattern::Var(var) => var == name,
        E::EPattern::Ctor(_, fields) => fields
            .iter()
            .any(|(_, pattern)| pattern_binds_elab_var(pattern, name)),
        E::EPattern::Wild => false,
        E::EPattern::Or(left, right) => {
            pattern_binds_elab_var(left, name) || pattern_binds_elab_var(right, name)
        }
    }
}

/// Lower a list of expression references (not owned) to a conjunction guard.
fn lower_guard_refs(reqs: &[&E::EExpr], ctx: &LowerCtx<'_>) -> IRExpr {
    match reqs {
        [] => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
        [e] => lower_expr(e, ctx),
        [e, rest @ ..] => IRExpr::BinOp {
            op: "OpAnd".to_owned(),
            left: Box::new(lower_expr(e, ctx)),
            right: Box::new(lower_guard_refs(rest, ctx)),
            ty: IRType::Bool,
            span: None,
        },
    }
}

fn extract_updates(body: &[E::EExpr], ctx: &LowerCtx<'_>) -> Vec<IRUpdate> {
    body.iter()
        .filter_map(|e| {
            if let E::EExpr::Assign(_, lhs, rhs, _) = e {
                if let E::EExpr::Prime(_, inner, _) = lhs.as_ref() {
                    if let E::EExpr::Var(_, field, _) = inner.as_ref() {
                        return Some(IRUpdate {
                            field: field.clone(),
                            value: lower_expr(rhs, ctx),
                        });
                    }
                }
            }
            None
        })
        .collect()
}

// ── Verification ─────────────────────────────────────────────────────

fn lower_verify(
    ev: &E::EVerify,
    aliases: &std::collections::HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRVerify {
    // derive systems from let bindings. The system
    // list records which systems are in scope; entity pool sizing is
    // driven by the per-store `IRStoreDecl` entries, not by a collapsed
    // max(hi) on the system.
    let mut systems = Vec::new();
    for lb in &ev.let_bindings {
        let sys_name = canonical(aliases, &lb.system_type).to_owned();
        systems.push(IRVerifySystem {
            name: sys_name,
            lo: 0,
            hi: 1, // placeholder — real bounds come from stores
        });
    }
    // Populate per-store bounds so compute_verify_scope can size each
    // entity type independently.
    let mut stores: Vec<crate::ir::types::IRStoreDecl> = ev
        .stores
        .iter()
        .map(|s| crate::ir::types::IRStoreDecl {
            name: s.name.clone(),
            entity_type: canonical(aliases, &s.entity_type).to_owned(),
            lo: s.lo,
            hi: s.hi,
        })
        .collect();
    stores.extend(
        ev.proc_bounds
            .iter()
            .map(|p| crate::ir::types::IRStoreDecl {
                name: format!("__abide_procbound__{}__{}", p.system_type, p.proc),
                entity_type: format!(
                    "__abide_procinst__{}__{}",
                    canonical(aliases, &p.system_type),
                    p.proc
                ),
                lo: p.lo,
                hi: p.hi,
            }),
    );
    IRVerify {
        name: ev.name.clone(),
        depth: ev.depth,
        systems,
        stores,
        assumption_set: crate::ir::types::IRAssumptionSet::from_elab(&ev.assumption_set),
        activations: ev
            .activations
            .iter()
            .map(|a| crate::ir::types::IRActivation {
                instances: a.instances.clone(),
                store_name: a.store_name.clone(),
            })
            .collect(),
        initial_constraints: ev
            .initial_constraints
            .iter()
            .map(|e| lower_expr(e, ctx))
            .collect(),
        asserts: ev.asserts.iter().map(|e| lower_expr(e, ctx)).collect(),
        span: ev.span,
        file: ev.file.clone(),
    }
}

fn lower_theorem(
    et: &E::ETheorem,
    aliases: &std::collections::HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRTheorem {
    IRTheorem {
        name: et.name.clone(),
        systems: et
            .targets
            .iter()
            .map(|t| canonical(aliases, t).to_owned())
            .collect(),
        assumption_set: crate::ir::types::IRAssumptionSet::from_elab(&et.assumption_set),
        invariants: et.invariants.iter().map(|e| lower_expr(e, ctx)).collect(),
        shows: et.shows.iter().map(|e| lower_expr(e, ctx)).collect(),
        by_file: et.by_file.clone(),
        by_lemmas: et.by_lemmas.iter().map(|r| r.segments.join("::")).collect(),
        span: et.span,
        file: et.file.clone(),
    }
}

fn lower_axiom(ea: &E::EAxiom, ctx: &LowerCtx<'_>) -> IRAxiom {
    IRAxiom {
        name: ea.name.clone(),
        body: lower_expr(&ea.body, ctx),
        by_file: ea.by_file.clone(),
        span: ea.span,
        file: ea.file.clone(),
    }
}

fn lower_lemma(el: &E::ELemma, ctx: &LowerCtx<'_>) -> IRLemma {
    IRLemma {
        name: el.name.clone(),
        assumption_set: crate::ir::types::IRAssumptionSet::from_elab(&el.assumption_set),
        body: el.body.iter().map(|e| lower_expr(e, ctx)).collect(),
        span: el.span,
        file: el.file.clone(),
    }
}

fn lower_scene(
    es: &E::EScene,
    aliases: &std::collections::HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRScene {
    let (actions, assumes): (Vec<_>, Vec<_>) = es
        .whens
        .iter()
        .partition(|w| !matches!(w, E::ESceneWhen::Assume(_)));
    let events: Vec<_> = actions
        .iter()
        .map(|w| lower_scene_action(w, aliases, ctx))
        .collect();
    let mut ordering: Vec<_> = assumes
        .iter()
        .filter_map(|w| match w {
            E::ESceneWhen::Assume(e) => Some(lower_expr(e, ctx)),
            E::ESceneWhen::Action { .. } => None,
        })
        .collect();
    if ordering.is_empty() {
        if let Some(textual_ordering) = lower_scene_textual_ordering(&events) {
            ordering.push(textual_ordering);
        }
    }

    // derive systems from let bindings.
    let systems: Vec<String> = es
        .let_bindings
        .iter()
        .map(|lb| canonical(aliases, &lb.system_type).to_owned())
        .collect();

    IRScene {
        name: es.name.clone(),
        systems,
        stores: es
            .stores
            .iter()
            .map(|s| crate::ir::types::IRStoreDecl {
                name: s.name.clone(),
                entity_type: canonical(aliases, &s.entity_type).to_owned(),
                lo: s.lo,
                hi: s.hi,
            })
            .collect(),
        givens: es
            .givens
            .iter()
            .map(|g| lower_given(g, aliases, ctx))
            .collect(),
        events,
        ordering,
        assertions: es.thens.iter().map(|e| lower_expr(e, ctx)).collect(),
        given_constraints: es
            .given_constraints
            .iter()
            .map(|e| lower_expr(e, ctx))
            .collect(),
        activations: es
            .activations
            .iter()
            .map(|a| crate::ir::types::IRActivation {
                instances: a.instances.clone(),
                store_name: a.store_name.clone(),
            })
            .collect(),
        span: es.span,
        file: es.file.clone(),
    }
}

fn lower_scene_textual_ordering(events: &[IRSceneEvent]) -> Option<IRExpr> {
    let mut vars = events.iter().map(|event| IRExpr::Var {
        ty: IRType::Bool,
        name: event.var.clone(),
        span: None,
    });
    let first = vars.next()?;
    vars.next().map(|second| {
        vars.fold(
            IRExpr::BinOp {
                ty: IRType::Bool,
                op: "OpSeq".to_owned(),
                left: Box::new(first),
                right: Box::new(second),
                span: None,
            },
            |left, right| IRExpr::BinOp {
                ty: IRType::Bool,
                op: "OpSeq".to_owned(),
                left: Box::new(left),
                right: Box::new(right),
                span: None,
            },
        )
    })
}

fn lower_given(
    g: &E::ESceneGiven,
    aliases: &std::collections::HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRSceneGiven {
    let constraint = match &g.condition {
        Some(e) => lower_expr(e, ctx),
        None => IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        },
    };
    IRSceneGiven {
        var: g.var.clone(),
        entity: canonical(aliases, &g.entity_type).to_owned(),
        store_name: g.store_name.clone(),
        constraint,
    }
}

fn lower_scene_action(
    w: &E::ESceneWhen,
    aliases: &std::collections::HashMap<String, String>,
    ctx: &LowerCtx<'_>,
) -> IRSceneEvent {
    match w {
        E::ESceneWhen::Action {
            var,
            system,
            event,
            args,
            card,
        } => IRSceneEvent {
            var: var.clone(),
            system: canonical(aliases, system).to_owned(),
            event: event.clone(),
            args: args.iter().map(|a| lower_expr(a, ctx)).collect(),
            cardinality: card_from_text(card.as_deref()),
        },
        E::ESceneWhen::Assume(_) => unreachable!("assumes partitioned out"),
    }
}

#[cfg(test)]
mod tests;
