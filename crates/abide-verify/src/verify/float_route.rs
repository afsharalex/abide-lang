//! IEEE-754 `float` backend routing (DDR-059).
//!
//! The cvc5 backend has no floating-point arithmetic, so any obligation that
//! mentions `float` must be solved with Z3. This module detects whether a
//! lowered program uses `float` anywhere so the dispatcher can route to Z3 when
//! Z3 is allowed, or emit a focused unsupported-backend diagnostic when the user
//! has forced cvc5 — instead of reaching the solver's hard floating-point stop.
//!
//! The two core walkers ([`ty_uses_float`] and [`expr_uses_float`]) and the
//! action walker are written **without catch-all arms** so the compiler forces
//! every present and future IR variant to be classified — a missed float path
//! would otherwise silently re-introduce the panic it is meant to prevent.

use crate::ir::types::{
    IRAction, IRActionMatchScrutinee, IREntity, IRExpr, IRField, IRFunction, IRProgram, IRScene,
    IRSystem, IRTheorem, IRType, IRVerify, LitVal,
};

/// Returns `true` if any declaration in `ir` mentions the IEEE-754 `float`
/// type or a `float` literal — in a type, signature, field, contract,
/// expression, or operational action.
pub fn program_uses_float(ir: &IRProgram) -> bool {
    ir.types.iter().any(|entry| ty_uses_float(&entry.ty))
        || ir
            .constants
            .iter()
            .any(|c| ty_uses_float(&c.ty) || expr_uses_float(&c.value))
        || ir.functions.iter().any(function_uses_float)
        || ir.entities.iter().any(entity_uses_float)
        || ir.systems.iter().any(system_uses_float)
        || ir.verifies.iter().any(verify_uses_float)
        || ir.theorems.iter().any(theorem_uses_float)
        || ir.axioms.iter().any(|a| expr_uses_float(&a.body))
        || ir.lemmas.iter().any(|l| l.body.iter().any(expr_uses_float))
        || ir.scenes.iter().any(scene_uses_float)
}

// ── Types ───────────────────────────────────────────────────────────

/// Recursively test whether an [`IRType`] mentions `float`. No catch-all arm:
/// the compiler enforces that every variant is classified.
fn ty_uses_float(ty: &IRType) -> bool {
    match ty {
        IRType::Float => true,
        IRType::Int
        | IRType::Bool
        | IRType::String
        | IRType::Identity
        | IRType::Real
        | IRType::Entity { .. } => false,
        IRType::Enum { variants, .. } => variants
            .iter()
            .any(|v| v.fields.iter().any(|f| ty_uses_float(&f.ty))),
        IRType::Record { fields, .. } => fields.iter().any(|f| ty_uses_float(&f.ty)),
        IRType::Fn { param, result } => ty_uses_float(param) || ty_uses_float(result),
        IRType::Set { element } | IRType::Seq { element } => ty_uses_float(element),
        IRType::Map { key, value } => ty_uses_float(key) || ty_uses_float(value),
        IRType::Tuple { elements } => elements.iter().any(ty_uses_float),
        IRType::Refinement { base, predicate } => ty_uses_float(base) || expr_uses_float(predicate),
    }
}

// ── Expressions ─────────────────────────────────────────────────────

/// Recursively test whether an [`IRExpr`] mentions `float` — a `float` literal,
/// or any embedded/sub-expression type that does. No catch-all arm.
fn expr_uses_float(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Lit { ty, value, .. } => ty_uses_float(ty) || matches!(value, LitVal::Float { .. }),
        IRExpr::Var { ty, .. } => ty_uses_float(ty),
        IRExpr::Sorry { .. } | IRExpr::Todo { .. } => false,
        IRExpr::Ctor { args, .. } => args.iter().any(|(_, e)| expr_uses_float(e)),
        IRExpr::BinOp {
            left, right, ty, ..
        } => expr_uses_float(left) || expr_uses_float(right) || ty_uses_float(ty),
        IRExpr::UnOp { operand, ty, .. } => expr_uses_float(operand) || ty_uses_float(ty),
        IRExpr::App { func, arg, ty, .. } => {
            expr_uses_float(func) || expr_uses_float(arg) || ty_uses_float(ty)
        }
        IRExpr::Lam {
            param_type, body, ..
        } => ty_uses_float(param_type) || expr_uses_float(body),
        IRExpr::Let { bindings, body, .. } => {
            bindings
                .iter()
                .any(|b| ty_uses_float(&b.ty) || expr_uses_float(&b.expr))
                || expr_uses_float(body)
        }
        IRExpr::Forall { domain, body, .. }
        | IRExpr::Exists { domain, body, .. }
        | IRExpr::One { domain, body, .. }
        | IRExpr::Lone { domain, body, .. } => ty_uses_float(domain) || expr_uses_float(body),
        IRExpr::Choose {
            domain,
            predicate,
            ty,
            ..
        } => {
            ty_uses_float(domain)
                || predicate.as_deref().is_some_and(expr_uses_float)
                || ty_uses_float(ty)
        }
        IRExpr::Field { expr, ty, .. } => expr_uses_float(expr) || ty_uses_float(ty),
        IRExpr::Prime { expr, .. } => expr_uses_float(expr),
        IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. } => expr_uses_float(body),
        IRExpr::Until { left, right, .. } | IRExpr::Since { left, right, .. } => {
            expr_uses_float(left) || expr_uses_float(right)
        }
        IRExpr::Aggregate {
            domain,
            body,
            in_filter,
            ..
        } => {
            ty_uses_float(domain)
                || expr_uses_float(body)
                || in_filter.as_deref().is_some_and(expr_uses_float)
        }
        IRExpr::Saw { args, .. } => args.iter().flatten().any(|e| expr_uses_float(e)),
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            expr_uses_float(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(expr_uses_float) || expr_uses_float(&arm.body)
                })
        }
        IRExpr::SetLit { elements, ty, .. }
        | IRExpr::SeqLit { elements, ty, .. }
        | IRExpr::Tuple { elements, ty, .. } => {
            elements.iter().any(expr_uses_float) || ty_uses_float(ty)
        }
        IRExpr::MapLit { entries, ty, .. } => {
            entries
                .iter()
                .any(|(k, v)| expr_uses_float(k) || expr_uses_float(v))
                || ty_uses_float(ty)
        }
        IRExpr::MapUpdate {
            map,
            key,
            value,
            ty,
            ..
        } => {
            expr_uses_float(map)
                || expr_uses_float(key)
                || expr_uses_float(value)
                || ty_uses_float(ty)
        }
        IRExpr::Index { map, key, ty, .. } => {
            expr_uses_float(map) || expr_uses_float(key) || ty_uses_float(ty)
        }
        IRExpr::Card { expr, .. } => expr_uses_float(expr),
        IRExpr::SetComp {
            domain,
            source,
            filter,
            projection,
            ty,
            ..
        } => {
            ty_uses_float(domain)
                || source.as_deref().is_some_and(expr_uses_float)
                || expr_uses_float(filter)
                || projection.as_deref().is_some_and(expr_uses_float)
                || ty_uses_float(ty)
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ty,
            ..
        } => {
            expr_uses_float(projection)
                || bindings.iter().any(|b| {
                    ty_uses_float(&b.domain) || b.source.as_deref().is_some_and(expr_uses_float)
                })
                || expr_uses_float(filter)
                || ty_uses_float(ty)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => expr_uses_float(expr),
        IRExpr::Block { exprs, .. } => exprs.iter().any(expr_uses_float),
        IRExpr::VarDecl { ty, init, rest, .. } => {
            ty_uses_float(ty) || expr_uses_float(init) || expr_uses_float(rest)
        }
        IRExpr::While {
            cond,
            invariants,
            decreases,
            body,
            ..
        } => {
            expr_uses_float(cond)
                || invariants.iter().any(expr_uses_float)
                || decreases
                    .as_ref()
                    .is_some_and(|d| d.measures.iter().any(expr_uses_float))
                || expr_uses_float(body)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            expr_uses_float(cond)
                || expr_uses_float(then_body)
                || else_body.as_deref().is_some_and(expr_uses_float)
        }
    }
}

// ── Operational actions ─────────────────────────────────────────────

/// Recursively test whether an [`IRAction`] mentions `float`. No catch-all arm.
fn action_uses_float(action: &IRAction) -> bool {
    match action {
        IRAction::Choose { filter, ops, .. } => {
            expr_uses_float(filter) || ops.iter().any(action_uses_float)
        }
        IRAction::ForAll { ops, .. } => ops.iter().any(action_uses_float),
        IRAction::Create { fields, .. } => fields.iter().any(|f| expr_uses_float(&f.value)),
        IRAction::LetCrossCall { args, .. }
        | IRAction::Apply { args, .. }
        | IRAction::CrossCall { args, .. } => args.iter().any(expr_uses_float),
        IRAction::Match { scrutinee, arms } => {
            scrutinee_uses_float(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(expr_uses_float)
                        || arm.body.iter().any(action_uses_float)
                })
        }
        IRAction::ExprStmt { expr } => expr_uses_float(expr),
    }
}

fn scrutinee_uses_float(scrutinee: &IRActionMatchScrutinee) -> bool {
    match scrutinee {
        IRActionMatchScrutinee::Var { .. } => false,
        IRActionMatchScrutinee::CrossCall { args, .. } => args.iter().any(expr_uses_float),
    }
}

// ── Declaration walkers ─────────────────────────────────────────────

fn function_uses_float(func: &IRFunction) -> bool {
    ty_uses_float(&func.ty)
        || expr_uses_float(&func.body)
        || func.requires.iter().any(expr_uses_float)
        || func.ensures.iter().any(expr_uses_float)
        || func
            .decreases
            .as_ref()
            .is_some_and(|d| d.measures.iter().any(expr_uses_float))
}

fn entity_uses_float(entity: &IREntity) -> bool {
    entity.fields.iter().any(field_uses_float)
        || entity.transitions.iter().any(|t| {
            t.params.iter().any(|p| ty_uses_float(&p.ty))
                || expr_uses_float(&t.guard)
                || t.updates.iter().any(|u| expr_uses_float(&u.value))
                || t.postcondition.as_ref().is_some_and(expr_uses_float)
        })
        || entity
            .derived_fields
            .iter()
            .any(|d| ty_uses_float(&d.ty) || expr_uses_float(&d.body))
        || entity.invariants.iter().any(|i| expr_uses_float(&i.body))
}

fn field_uses_float(field: &IRField) -> bool {
    ty_uses_float(&field.ty)
        || field.default.as_ref().is_some_and(expr_uses_float)
        || field
            .initial_constraint
            .as_ref()
            .is_some_and(expr_uses_float)
}

fn system_uses_float(system: &IRSystem) -> bool {
    system.fields.iter().any(field_uses_float)
        || system.commands.iter().any(|c| {
            c.params.iter().any(|p| ty_uses_float(&p.ty))
                || c.return_type.as_ref().is_some_and(ty_uses_float)
        })
        || system.actions.iter().any(|a| {
            a.params.iter().any(|p| ty_uses_float(&p.ty))
                || expr_uses_float(&a.guard)
                || a.body.iter().any(action_uses_float)
                || a.return_expr.as_ref().is_some_and(expr_uses_float)
        })
        || system
            .derived_fields
            .iter()
            .any(|d| ty_uses_float(&d.ty) || expr_uses_float(&d.body))
        || system.invariants.iter().any(|i| expr_uses_float(&i.body))
        || system.queries.iter().any(|q| {
            q.params.iter().any(|p| ty_uses_float(&p.ty))
                || q.requires.iter().any(expr_uses_float)
                || expr_uses_float(&q.body)
        })
        || system.preds.iter().any(function_uses_float)
}

fn verify_uses_float(block: &IRVerify) -> bool {
    block.initial_constraints.iter().any(expr_uses_float)
        || block.asserts.iter().any(expr_uses_float)
}

fn theorem_uses_float(block: &IRTheorem) -> bool {
    block.invariants.iter().any(expr_uses_float) || block.shows.iter().any(expr_uses_float)
}

fn scene_uses_float(scene: &IRScene) -> bool {
    scene.ordering.iter().any(expr_uses_float)
        || scene.assertions.iter().any(expr_uses_float)
        || scene.given_constraints.iter().any(expr_uses_float)
        || scene.givens.iter().any(|g| expr_uses_float(&g.constraint))
        || scene
            .events
            .iter()
            .any(|e| e.args.iter().any(expr_uses_float))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::{
        IRAssumptionSet, IRAxiom, IRConst, IRField, IRLemma, IRTypeEntry, IRVerifySystem,
    };

    #[test]
    fn program_uses_float_detects_each_top_level_collection_independently() {
        assert!(!program_uses_float(&empty_program()));

        let mut cases: Vec<(&str, IRProgram)> = Vec::new();

        let mut program = empty_program();
        program.types.push(IRTypeEntry {
            name: "FloatAlias".to_owned(),
            ty: IRType::Float,
        });
        cases.push(("types", program));

        let mut program = empty_program();
        program.constants.push(IRConst {
            name: "typed_c".to_owned(),
            ty: IRType::Float,
            value: bool_lit(),
        });
        cases.push(("constants with float type", program));

        let mut program = empty_program();
        program.constants.push(IRConst {
            name: "value_c".to_owned(),
            ty: IRType::Bool,
            value: float_lit(),
        });
        cases.push(("constants with float value", program));

        let mut program = empty_program();
        program.functions.push(IRFunction {
            name: "f".to_owned(),
            ty: IRType::Fn {
                param: Box::new(IRType::Float),
                result: Box::new(IRType::Bool),
            },
            body: bool_lit(),
            prop_target: None,
            requires: Vec::new(),
            ensures: Vec::new(),
            decreases: None,
            span: None,
            file: None,
        });
        cases.push(("functions", program));

        let mut program = empty_program();
        program.entities.push(IREntity {
            name: "Thing".to_owned(),
            fields: vec![float_field("weight")],
            transitions: Vec::new(),
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            fsm_decls: Vec::new(),
        });
        cases.push(("entities", program));

        let mut program = empty_program();
        program.systems.push(IRSystem {
            name: "System".to_owned(),
            store_params: Vec::new(),
            fields: vec![float_field("level")],
            entities: Vec::new(),
            commands: Vec::new(),
            actions: Vec::new(),
            fsm_decls: Vec::new(),
            derived_fields: Vec::new(),
            invariants: Vec::new(),
            queries: Vec::new(),
            preds: Vec::new(),
            let_bindings: Vec::new(),
            procs: Vec::new(),
        });
        cases.push(("systems", program));

        let mut program = empty_program();
        program.verifies.push(IRVerify {
            name: "check".to_owned(),
            depth: None,
            systems: vec![IRVerifySystem {
                name: "System".to_owned(),
                lo: 0,
                hi: 1,
            }],
            stores: Vec::new(),
            assumption_set: IRAssumptionSet::default_for_verify(),
            activations: Vec::new(),
            initial_constraints: Vec::new(),
            asserts: vec![float_lit()],
            span: None,
            file: None,
        });
        cases.push(("verifies", program));

        let mut program = empty_program();
        program.theorems.push(IRTheorem {
            name: "thm".to_owned(),
            systems: vec!["System".to_owned()],
            assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
            invariants: Vec::new(),
            shows: vec![float_lit()],
            by_file: None,
            by_lemmas: Vec::new(),
            span: None,
            file: None,
        });
        cases.push(("theorems", program));

        let mut program = empty_program();
        program.axioms.push(IRAxiom {
            name: "ax".to_owned(),
            body: float_lit(),
            by_file: None,
            span: None,
            file: None,
        });
        cases.push(("axioms", program));

        let mut program = empty_program();
        program.lemmas.push(IRLemma {
            name: "lemma".to_owned(),
            assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
            body: vec![float_lit()],
            span: None,
            file: None,
        });
        cases.push(("lemmas", program));

        let mut program = empty_program();
        program.scenes.push(IRScene {
            name: "scene".to_owned(),
            systems: vec!["System".to_owned()],
            stores: Vec::new(),
            givens: Vec::new(),
            events: Vec::new(),
            ordering: Vec::new(),
            assertions: vec![float_lit()],
            given_constraints: Vec::new(),
            activations: Vec::new(),
            span: None,
            file: None,
        });
        cases.push(("scenes", program));

        for (name, program) in cases {
            assert!(
                program_uses_float(&program),
                "program-level float routing missed {name}"
            );
        }
    }

    fn empty_program() -> IRProgram {
        IRProgram {
            types: Vec::new(),
            constants: Vec::new(),
            functions: Vec::new(),
            entities: Vec::new(),
            interfaces: Vec::new(),
            systems: Vec::new(),
            verifies: Vec::new(),
            theorems: Vec::new(),
            axioms: Vec::new(),
            lemmas: Vec::new(),
            scenes: Vec::new(),
        }
    }

    fn float_lit() -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Float,
            value: LitVal::Float { value: 1.25 },
            span: None,
        }
    }

    fn bool_lit() -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value: true },
            span: None,
        }
    }

    fn float_field(name: &str) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Float,
            default: None,
            initial_constraint: None,
        }
    }
}
