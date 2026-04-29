//! Extract a `FlowModel` from IR.
//!
//! Walks the `IRProgram` to build state graphs for each finite graph-backed
//! entity or system field,
//! extracts system/event structure for cross-system queries, and lifts declared
//! fsm metadata from both entities and systems.

use std::collections::HashMap;

use crate::ir::types::{
    IRAction, IREntity, IRExpr, IRField, IRProgram, IRSystem, IRType, IRVariant,
};

use super::model::{
    ActionContract, ApplyInfo, CrossCall, EventInfo, FieldGraphMeta, FlowModel, FsmInfo, OwnerKind,
    StateGraph, SystemInfo, TransitionEdge,
};

/// Extract a `FlowModel` from an `IRProgram`.
pub fn extract(ir: &IRProgram) -> FlowModel {
    let mut state_graphs = HashMap::new();
    let mut field_graph_meta = HashMap::new();

    for entity in &ir.entities {
        record_entity_field_meta(entity, &mut field_graph_meta);
        let graphs = extract_entity_graphs(entity);
        for sg in graphs {
            state_graphs.insert((sg.owner.clone(), sg.field.clone()), sg);
        }
    }

    let mut systems = HashMap::new();
    for system in &ir.systems {
        record_system_field_meta(system, &mut field_graph_meta);
        for sg in extract_system_graphs(system) {
            state_graphs.insert((sg.owner.clone(), sg.field.clone()), sg);
        }
        systems.insert(system.name.clone(), extract_system_info(system));
    }

    let entity_names = ir.entities.iter().map(|e| e.name.clone()).collect();
    let system_names = ir.systems.iter().map(|s| s.name.clone()).collect();
    let type_names = ir.types.iter().map(|t| t.name.clone()).collect();

    let mut action_contracts = HashMap::new();
    for entity in &ir.entities {
        for transition in &entity.transitions {
            let contract = ActionContract {
                entity: entity.name.clone(),
                action: transition.name.clone(),
                guard: display_ir_expr(&transition.guard),
                postcondition: transition.postcondition.as_ref().map(display_ir_expr),
                updates: transition
                    .updates
                    .iter()
                    .map(|u| format!("{}' = {}", u.field, display_ir_expr(&u.value)))
                    .collect(),
            };
            action_contracts.insert((entity.name.clone(), transition.name.clone()), contract);
        }
    }

    // extract fsm metadata for `ask fsms on Owner`,
    // `ask transitions of Owner::field`, `ask terminal states of Owner::field`.
    //
    // The terminal set is computed against the field's FULL enum
    // variant list (not just the variants mentioned in the table) to
    // match the compiler's synthesized `is_terminal` semantics in
    // `synthesize_fsm_is_terminal`. A variant the user omitted from
    // the fsm table entirely is terminal-by-omission: it has no
    // outgoing transitions, so it must show up in `ask terminal
    // states of E::field`. The earlier "mentioned-only" extraction
    // would silently drop such variants and diverge from elaboration.
    let mut fsm_decls = HashMap::new();
    for entity in &ir.entities {
        for fsm in &entity.fsm_decls {
            let pairs: Vec<(String, String)> = fsm
                .transitions
                .iter()
                .map(|t| (t.from.clone(), t.to.clone()))
                .collect();
            // Resolve the field's enum variant list from the entity's
            // own field list. We rely on `IREntity::fields` (rather
            // than the global type registry) so this works for any
            // qualified-name or aliased enum that already lowered
            // through the entity's `IRField::ty`.
            let variants: Vec<String> = entity
                .fields
                .iter()
                .find(|f| f.name == fsm.field)
                .and_then(|f| match &f.ty {
                    IRType::Enum { variants: vs, .. } => {
                        Some(vs.iter().map(|v| v.name.clone()).collect())
                    }
                    _ => None,
                })
                .unwrap_or_default();
            let terminal_states: Vec<String> = variants
                .into_iter()
                .filter(|v| !pairs.iter().any(|(from, _)| from == v))
                .collect();
            fsm_decls.insert(
                (entity.name.clone(), fsm.field.clone()),
                FsmInfo {
                    owner: entity.name.clone(),
                    field: fsm.field.clone(),
                    enum_name: fsm.enum_name.clone(),
                    transitions: pairs,
                    terminal_states,
                },
            );
        }
    }
    for system in &ir.systems {
        for fsm in &system.fsm_decls {
            let pairs: Vec<(String, String)> = fsm
                .transitions
                .iter()
                .map(|t| (t.from.clone(), t.to.clone()))
                .collect();
            let variants: Vec<String> = system
                .fields
                .iter()
                .find(|f| f.name == fsm.field)
                .and_then(|f| match &f.ty {
                    IRType::Enum { variants: vs, .. } => {
                        Some(vs.iter().map(|v| v.name.clone()).collect())
                    }
                    _ => None,
                })
                .unwrap_or_default();
            let terminal_states: Vec<String> = variants
                .into_iter()
                .filter(|v| !pairs.iter().any(|(from, _)| from == v))
                .collect();
            fsm_decls.insert(
                (system.name.clone(), fsm.field.clone()),
                FsmInfo {
                    owner: system.name.clone(),
                    field: fsm.field.clone(),
                    enum_name: fsm.enum_name.clone(),
                    transitions: pairs,
                    terminal_states,
                },
            );
        }
    }

    FlowModel {
        state_graphs,
        field_graph_meta,
        systems,
        entity_names,
        system_names,
        type_names,
        action_contracts,
        fsm_decls,
    }
}

fn record_entity_field_meta(
    entity: &IREntity,
    field_graph_meta: &mut HashMap<(String, String), FieldGraphMeta>,
) {
    for field in &entity.fields {
        field_graph_meta.insert(
            (entity.name.clone(), field.name.clone()),
            FieldGraphMeta {
                owner: entity.name.clone(),
                field: field.name.clone(),
                owner_kind: OwnerKind::Entity,
                graphable: is_graphable_field_type(&field.ty),
                type_name: display_ir_type(&field.ty),
            },
        );
    }
}

fn record_system_field_meta(
    system: &IRSystem,
    field_graph_meta: &mut HashMap<(String, String), FieldGraphMeta>,
) {
    for field in &system.fields {
        field_graph_meta.insert(
            (system.name.clone(), field.name.clone()),
            FieldGraphMeta {
                owner: system.name.clone(),
                field: field.name.clone(),
                owner_kind: OwnerKind::System,
                graphable: is_graphable_field_type(&field.ty),
                type_name: display_ir_type(&field.ty),
            },
        );
    }
}

/// Extract state graphs for all finite scalar fields of an entity.
fn extract_entity_graphs(entity: &IREntity) -> Vec<StateGraph> {
    let mut graphs = Vec::new();

    for field in &entity.fields {
        let Some(states) = finite_field_states(&field.ty) else {
            continue;
        };

        let initial = field
            .default
            .as_ref()
            .and_then(|expr| extract_finite_state_name(expr, &field.ty));

        let mut transitions = Vec::new();
        for transition in &entity.transitions {
            // Check if this transition updates this field
            for update in &transition.updates {
                if update.field == field.name {
                    let Some(to) = extract_finite_state_name(&update.value, &field.ty) else {
                        continue;
                    };
                    let from = extract_guard_state(&transition.guard, &field.name, &field.ty);
                    transitions.push(TransitionEdge {
                        action: transition.name.clone(),
                        from,
                        to,
                    });
                }
            }
        }

        graphs.push(StateGraph {
            owner: entity.name.clone(),
            owner_kind: OwnerKind::Entity,
            field: field.name.clone(),
            states,
            initial,
            transitions,
        });
    }

    graphs
}

/// Extract state graphs for all finite scalar fields of a system.
fn extract_system_graphs(system: &IRSystem) -> Vec<StateGraph> {
    let mut graphs = Vec::new();

    for field in &system.fields {
        let Some(states) = finite_field_states(&field.ty) else {
            continue;
        };

        let initial = field
            .default
            .as_ref()
            .and_then(|expr| extract_finite_state_name(expr, &field.ty));

        let mut transitions = Vec::new();
        for step in &system.actions {
            collect_system_field_transitions(
                &step.body,
                &step.guard,
                field,
                &step.name,
                &mut transitions,
            );
        }

        graphs.push(StateGraph {
            owner: system.name.clone(),
            owner_kind: OwnerKind::System,
            field: field.name.clone(),
            states,
            initial,
            transitions,
        });
    }

    graphs
}

fn collect_system_field_transitions(
    body: &[IRAction],
    guard: &IRExpr,
    field: &IRField,
    action_name: &str,
    out: &mut Vec<TransitionEdge>,
) {
    for action in body {
        match action {
            IRAction::ExprStmt { expr } => {
                if let Some(to) = extract_system_field_update(expr, &field.name, &field.ty) {
                    out.push(TransitionEdge {
                        action: action_name.to_owned(),
                        from: extract_guard_state(guard, &field.name, &field.ty),
                        to,
                    });
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                collect_system_field_transitions(ops, guard, field, action_name, out);
            }
            IRAction::Match { arms, .. } => {
                for arm in arms {
                    collect_system_field_transitions(&arm.body, guard, field, action_name, out);
                }
            }
            IRAction::Create { .. }
            | IRAction::LetCrossCall { .. }
            | IRAction::Apply { .. }
            | IRAction::CrossCall { .. } => {}
        }
    }
}

fn extract_system_field_update(
    expr: &IRExpr,
    field_name: &str,
    field_ty: &IRType,
) -> Option<String> {
    match expr {
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => match left.as_ref() {
            IRExpr::Prime { expr, .. } => match expr.as_ref() {
                IRExpr::Var { name, .. } if name == field_name => {
                    extract_finite_state_name(right, field_ty)
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// Try to extract the source state from a guard expression.
/// Looks for patterns like `status == @Pending` or `ready == true`.
fn extract_guard_state(guard: &IRExpr, field_name: &str, field_ty: &IRType) -> Option<String> {
    match guard {
        // Direct: field == State
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpEq" => {
            if is_field_ref(left, field_name) {
                return extract_finite_state_name(right, field_ty);
            }
            if is_field_ref(right, field_name) {
                return extract_finite_state_name(left, field_ty);
            }
            None
        }
        // Conjunction:... and field == @State
        IRExpr::BinOp {
            op, left, right, ..
        } if op == "OpAnd" => extract_guard_state(left, field_name, field_ty)
            .or_else(|| extract_guard_state(right, field_name, field_ty)),
        _ => None,
    }
}

fn finite_field_states(ty: &IRType) -> Option<Vec<String>> {
    finite_field_states_inner(ty, &mut Vec::new())
}

fn finite_field_states_inner(ty: &IRType, visiting_enums: &mut Vec<String>) -> Option<Vec<String>> {
    match ty {
        IRType::Bool => Some(vec!["false".to_owned(), "true".to_owned()]),
        IRType::Enum { name, variants } => {
            if visiting_enums.iter().any(|seen| seen == name) {
                return None;
            }
            visiting_enums.push(name.clone());
            let mut states = Vec::new();
            for variant in variants {
                states.extend(finite_variant_states(variant, visiting_enums)?);
            }
            visiting_enums.pop();
            Some(states)
        }
        _ => None,
    }
}

fn finite_variant_states(
    variant: &IRVariant,
    visiting_enums: &mut Vec<String>,
) -> Option<Vec<String>> {
    if variant.fields.is_empty() {
        return Some(vec![variant.name.clone()]);
    }

    let mut field_domains = Vec::with_capacity(variant.fields.len());
    for field in &variant.fields {
        field_domains.push((
            field.name.clone(),
            finite_field_states_inner(&field.ty, visiting_enums)?,
        ));
    }

    let mut labels = Vec::new();
    enumerate_variant_states(variant, &field_domains, 0, &mut Vec::new(), &mut labels);
    Some(labels)
}

fn enumerate_variant_states(
    variant: &IRVariant,
    field_domains: &[(String, Vec<String>)],
    index: usize,
    current: &mut Vec<(String, String)>,
    labels: &mut Vec<String>,
) {
    if index == field_domains.len() {
        labels.push(render_variant_state(&variant.name, current));
        return;
    }

    let (field_name, states) = &field_domains[index];
    for state in states {
        current.push((field_name.clone(), state.clone()));
        enumerate_variant_states(variant, field_domains, index + 1, current, labels);
        current.pop();
    }
}

fn render_variant_state(variant_name: &str, fields: &[(String, String)]) -> String {
    if fields.is_empty() {
        return variant_name.to_owned();
    }

    let parts: Vec<String> = fields
        .iter()
        .map(|(name, value)| format!("{name}={value}"))
        .collect();
    format!("{variant_name}{{{}}}", parts.join(","))
}

fn is_graphable_field_type(ty: &IRType) -> bool {
    finite_field_states(ty).is_some()
}

fn extract_finite_state_name(expr: &IRExpr, field_ty: &IRType) -> Option<String> {
    match (field_ty, expr) {
        (IRType::Enum { variants, .. }, IRExpr::Ctor { ctor, args, .. }) => {
            let variant = variants.iter().find(|variant| variant.name == *ctor)?;
            if variant.fields.is_empty() {
                return args.is_empty().then(|| ctor.clone());
            }
            if args.len() != variant.fields.len() {
                return None;
            }

            let mut rendered_fields = Vec::with_capacity(variant.fields.len());
            for field in &variant.fields {
                let (_, value) = args.iter().find(|(name, _)| name == &field.name)?;
                rendered_fields.push((
                    field.name.clone(),
                    extract_finite_state_name(value, &field.ty)?,
                ));
            }
            Some(render_variant_state(ctor, &rendered_fields))
        }
        (
            IRType::Bool,
            IRExpr::Lit {
                value: crate::ir::types::LitVal::Bool { value },
                ..
            },
        ) => Some(value.to_string()),
        _ => None,
    }
}

/// Check if an expression is a reference to a field (`Var` with `field_name`).
fn is_field_ref(expr: &IRExpr, field_name: &str) -> bool {
    match expr {
        IRExpr::Var { name, .. } => name == field_name,
        _ => false,
    }
}

/// Extract system information from an `IRSystem`.
fn extract_system_info(system: &IRSystem) -> SystemInfo {
    let events = system
        .actions
        .iter()
        .map(|ev| {
            let mut cross_calls = Vec::new();
            let mut applies = Vec::new();
            collect_event_actions(&ev.body, &mut cross_calls, &mut applies);
            EventInfo {
                name: ev.name.clone(),
                cross_calls,
                applies,
            }
        })
        .collect();

    SystemInfo {
        name: system.name.clone(),
        entities: system.entities.clone(),
        events,
    }
}

/// Recursively collect cross-calls and applies from event actions.
fn collect_event_actions(
    actions: &[IRAction],
    cross_calls: &mut Vec<CrossCall>,
    applies: &mut Vec<ApplyInfo>,
) {
    for action in actions {
        match action {
            IRAction::Apply {
                target, transition, ..
            } => {
                // target is a variable name bound to an entity
                applies.push(ApplyInfo {
                    entity: target.clone(),
                    action: transition.clone(),
                });
            }
            IRAction::CrossCall {
                system, command, ..
            } => {
                cross_calls.push(CrossCall {
                    target_system: system.clone(),
                    target_event: command.clone(),
                });
            }
            IRAction::LetCrossCall {
                system, command, ..
            } => {
                cross_calls.push(CrossCall {
                    target_system: system.clone(),
                    target_event: command.clone(),
                });
            }
            IRAction::Match { arms, .. } => {
                for arm in arms {
                    collect_event_actions(&arm.body, cross_calls, applies);
                }
            }
            IRAction::Choose { ops, .. } | IRAction::ForAll { ops, .. } => {
                collect_event_actions(ops, cross_calls, applies);
            }
            IRAction::Create { .. } | IRAction::ExprStmt { .. } => {}
        }
    }
}

/// Render an IR expression as a human-readable string for QA output.
fn display_ir_expr(expr: &IRExpr) -> String {
    match expr {
        IRExpr::Lit { value, .. } => match value {
            crate::ir::types::LitVal::Int { value } => value.to_string(),
            crate::ir::types::LitVal::Bool { value } => value.to_string(),
            crate::ir::types::LitVal::Real { value } => value.to_string(),
            crate::ir::types::LitVal::Float { value } => value.to_string(),
            crate::ir::types::LitVal::Str { value } => format!("\"{value}\""),
        },
        IRExpr::Var { name, .. } => name.clone(),
        IRExpr::Ctor { ctor, args, .. } => {
            if args.is_empty() {
                format!("@{ctor}")
            } else {
                let fields: Vec<String> = args
                    .iter()
                    .map(|(name, val)| format!("{name}: {}", display_ir_expr(val)))
                    .collect();
                format!("@{ctor} {{ {} }}", fields.join(", "))
            }
        }
        IRExpr::Field { expr, field, .. } => {
            format!("{}.{field}", display_ir_expr(expr))
        }
        IRExpr::Prime { expr, .. } => format!("{}'", display_ir_expr(expr)),
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let op_str = match op.as_str() {
                "OpEq" => "==",
                "OpNEq" => "!=",
                "OpLt" => "<",
                "OpGt" => ">",
                "OpLe" => "<=",
                "OpGe" => ">=",
                "OpAnd" => "and",
                "OpOr" => "or",
                "OpAdd" => "+",
                "OpSub" => "-",
                "OpMul" => "*",
                "OpDiv" => "/",
                "OpMod" => "%",
                "OpImplies" => "implies",
                other => other,
            };
            format!(
                "{} {} {}",
                display_ir_expr(left),
                op_str,
                display_ir_expr(right)
            )
        }
        IRExpr::UnOp { op, operand, .. } => {
            let op_str = match op.as_str() {
                "OpNot" => "not",
                "OpNeg" => "-",
                other => other,
            };
            format!("{op_str} {}", display_ir_expr(operand))
        }
        IRExpr::Always { body, .. } => format!("always {}", display_ir_expr(body)),
        IRExpr::Eventually { body, .. } => format!("eventually {}", display_ir_expr(body)),
        IRExpr::Until { left, right, .. } => {
            format!("{} until {}", display_ir_expr(left), display_ir_expr(right))
        }
        // / — past-time temporal operators.
        IRExpr::Historically { body, .. } => format!("historically {}", display_ir_expr(body)),
        IRExpr::Once { body, .. } => format!("once {}", display_ir_expr(body)),
        IRExpr::Previously { body, .. } => format!("previously {}", display_ir_expr(body)),
        IRExpr::Since { left, right, .. } => {
            format!("{} since {}", display_ir_expr(left), display_ir_expr(right))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            let arms_str: Vec<String> = arms
                .iter()
                .map(|arm| {
                    let pat = display_ir_pattern(&arm.pattern);
                    let guard = arm
                        .guard
                        .as_ref()
                        .map(|g| format!(" if {}", display_ir_expr(g)))
                        .unwrap_or_default();
                    format!("{pat}{guard} => {}", display_ir_expr(&arm.body))
                })
                .collect();
            format!(
                "match {} {{ {} }}",
                display_ir_expr(scrutinee),
                arms_str.join(", ")
            )
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => format!(
            "all {var}: {} | {}",
            display_ir_type(domain),
            display_ir_expr(body)
        ),
        IRExpr::Exists {
            var, domain, body, ..
        } => format!(
            "exists {var}: {} | {}",
            display_ir_type(domain),
            display_ir_expr(body)
        ),
        IRExpr::One {
            var, domain, body, ..
        } => format!(
            "one {var}: {} | {}",
            display_ir_type(domain),
            display_ir_expr(body)
        ),
        IRExpr::Lone {
            var, domain, body, ..
        } => format!(
            "lone {var}: {} | {}",
            display_ir_type(domain),
            display_ir_expr(body)
        ),
        IRExpr::App { func, arg, .. } => {
            format!("{}({})", display_ir_expr(func), display_ir_expr(arg))
        }
        IRExpr::Lam { param, body, .. } => format!("fn({param}) => {}", display_ir_expr(body)),
        IRExpr::Let { bindings, body, .. } => {
            let binds: Vec<String> = bindings
                .iter()
                .map(|b| format!("{} = {}", b.name, display_ir_expr(&b.expr)))
                .collect();
            format!("let {} in {}", binds.join(", "), display_ir_expr(body))
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let else_str = else_body
                .as_ref()
                .map(|e| format!(" else {}", display_ir_expr(e)))
                .unwrap_or_default();
            format!(
                "if {} then {}{}",
                display_ir_expr(cond),
                display_ir_expr(then_body),
                else_str
            )
        }
        IRExpr::Card { expr, .. } => format!("#{}", display_ir_expr(expr)),
        IRExpr::SetLit { elements, .. } => {
            let elems: Vec<String> = elements.iter().map(display_ir_expr).collect();
            format!("Set({})", elems.join(", "))
        }
        IRExpr::SeqLit { elements, .. } => {
            let elems: Vec<String> = elements.iter().map(display_ir_expr).collect();
            format!("Seq({})", elems.join(", "))
        }
        IRExpr::MapLit { entries, .. } => {
            let pairs: Vec<String> = entries
                .iter()
                .map(|(k, v)| format!("({}, {})", display_ir_expr(k), display_ir_expr(v)))
                .collect();
            format!("Map({})", pairs.join(", "))
        }
        IRExpr::Index { map, key, .. } => {
            format!("{}[{}]", display_ir_expr(map), display_ir_expr(key))
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => format!(
            "{}[{} := {}]",
            display_ir_expr(map),
            display_ir_expr(key),
            display_ir_expr(value)
        ),
        IRExpr::Assert { expr, .. } => format!("assert {}", display_ir_expr(expr)),
        IRExpr::Assume { expr, .. } => format!("assume {}", display_ir_expr(expr)),
        IRExpr::Sorry { .. } => "sorry".to_string(),
        IRExpr::Todo { .. } => "todo".to_string(),
        IRExpr::Block { exprs, .. } => {
            let stmts: Vec<String> = exprs.iter().map(display_ir_expr).collect();
            format!("{{ {} }}", stmts.join("; "))
        }
        // / — saw operator.
        IRExpr::Saw {
            system_name,
            event_name,
            args,
            ..
        } => {
            let args_str: Vec<String> = args
                .iter()
                .map(|a| match a {
                    Some(e) => display_ir_expr(e),
                    None => "_".to_string(),
                })
                .collect();
            if args_str.is_empty() {
                format!("saw {system_name}::{event_name}")
            } else {
                format!("saw {system_name}::{event_name}({})", args_str.join(", "))
            }
        }
        _ => format!("{expr:?}"),
    }
}

/// Render an IR pattern as a human-readable string.
fn display_ir_pattern(pat: &crate::ir::types::IRPattern) -> String {
    use crate::ir::types::IRPattern;
    match pat {
        IRPattern::PWild => "_".to_string(),
        IRPattern::PVar { name } => name.clone(),
        IRPattern::PCtor { name, fields } => {
            if fields.is_empty() {
                name.clone()
            } else {
                let fs: Vec<String> = fields
                    .iter()
                    .map(|fp| format!("{}: {}", fp.name, display_ir_pattern(&fp.pattern)))
                    .collect();
                format!("{name} {{ {} }}", fs.join(", "))
            }
        }
        IRPattern::POr { left, right } => {
            format!(
                "{} | {}",
                display_ir_pattern(left),
                display_ir_pattern(right)
            )
        }
    }
}

/// Render an IR type as a human-readable string.
fn display_ir_type(ty: &IRType) -> String {
    match ty {
        IRType::Bool => "bool".to_string(),
        IRType::Int => "int".to_string(),
        IRType::Real => "real".to_string(),
        IRType::Float => "float".to_string(),
        IRType::String => "string".to_string(),
        IRType::Identity => "identity".to_string(),
        IRType::Enum { name, .. } => name.clone(),
        IRType::Entity { name } => name.clone(),
        IRType::Set { element } => format!("Set<{}>", display_ir_type(element)),
        IRType::Seq { element } => format!("Seq<{}>", display_ir_type(element)),
        IRType::Map { key, value } => {
            format!("Map<{}, {}>", display_ir_type(key), display_ir_type(value))
        }
        _ => format!("{ty:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::types::*;

    fn make_enum_field(name: &str, variants: &[&str], default: Option<&str>) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Enum {
                name: format!("{name}Status"),
                variants: variants
                    .iter()
                    .map(|s| crate::ir::types::IRVariant::simple(*s))
                    .collect(),
            },
            default: default.map(|d| IRExpr::Ctor {
                enum_name: format!("{name}Status"),
                ctor: d.to_owned(),
                args: vec![],
                span: None,
            }),
            initial_constraint: None,
        }
    }

    fn make_bool_field(name: &str, default: bool) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Bool,
            default: Some(IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: default },
                span: None,
            }),
            initial_constraint: None,
        }
    }

    fn make_payload_enum_field(name: &str, default_ready: bool) -> IRField {
        IRField {
            name: name.to_owned(),
            ty: IRType::Enum {
                name: "WorkflowMode".to_owned(),
                variants: vec![
                    crate::ir::types::IRVariant::simple("Idle"),
                    crate::ir::types::IRVariant {
                        name: "Ready".to_owned(),
                        fields: vec![crate::ir::types::IRVariantField {
                            name: "armed".to_owned(),
                            ty: IRType::Bool,
                        }],
                    },
                ],
            },
            default: Some(IRExpr::Ctor {
                enum_name: "WorkflowMode".to_owned(),
                ctor: "Ready".to_owned(),
                args: vec![(
                    "armed".to_owned(),
                    IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool {
                            value: default_ready,
                        },
                        span: None,
                    },
                )],
                span: None,
            }),
            initial_constraint: None,
        }
    }

    fn make_transition(
        name: &str,
        field: &str,
        guard_state: Option<&str>,
        to: &str,
    ) -> IRTransition {
        let guard = match guard_state {
            Some(from) => IRExpr::BinOp {
                op: "OpEq".to_owned(),
                left: Box::new(IRExpr::Var {
                    name: field.to_owned(),
                    ty: IRType::String,
                    span: None,
                }),
                right: Box::new(IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: from.to_owned(),
                    args: vec![],
                    span: None,
                }),
                ty: IRType::Bool,
                span: None,
            },
            None => IRExpr::Lit {
                ty: IRType::Bool,
                value: LitVal::Bool { value: true },
                span: None,
            },
        };
        IRTransition {
            name: name.to_owned(),
            refs: vec![],
            params: vec![],
            guard,
            updates: vec![IRUpdate {
                field: field.to_owned(),
                value: IRExpr::Ctor {
                    enum_name: "Status".to_owned(),
                    ctor: to.to_owned(),
                    args: vec![],
                    span: None,
                },
            }],
            postcondition: None,
        }
    }

    #[test]
    fn extract_simple_entity() {
        let entity = IREntity {
            name: "Order".to_owned(),
            fields: vec![make_enum_field(
                "status",
                &["Pending", "Confirmed", "Shipped"],
                Some("Pending"),
            )],
            transitions: vec![
                make_transition("submit", "status", Some("Pending"), "Confirmed"),
                make_transition("ship", "status", Some("Confirmed"), "Shipped"),
            ],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let model = extract(&ir);
        let sg = model
            .state_graphs
            .get(&("Order".to_owned(), "status".to_owned()))
            .expect("state graph for Order.status");
        assert_eq!(sg.states.len(), 3);
        assert_eq!(sg.owner, "Order");
        assert_eq!(sg.owner_kind, OwnerKind::Entity);
        assert_eq!(sg.initial, Some("Pending".to_owned()));
        assert_eq!(sg.transitions.len(), 2);
        assert_eq!(sg.transitions[0].action, "submit");
        assert_eq!(sg.transitions[0].from, Some("Pending".to_owned()));
        assert_eq!(sg.transitions[0].to, "Confirmed");
        assert_eq!(sg.transitions[1].action, "ship");
        assert_eq!(sg.transitions[1].to, "Shipped");
    }

    #[test]
    fn extract_multi_field_entity() {
        let entity = IREntity {
            name: "Ticket".to_owned(),
            fields: vec![
                make_enum_field("status", &["Open", "Closed"], Some("Open")),
                make_enum_field("priority", &["Low", "High"], Some("Low")),
                IRField {
                    name: "title".to_owned(),
                    ty: IRType::String,
                    default: None,
                    initial_constraint: None,
                },
            ],
            transitions: vec![make_transition("close", "status", Some("Open"), "Closed")],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };
        let model = extract(&ir);
        // Should have graphs for status and priority, but not title (String, not Enum)
        assert!(model
            .state_graphs
            .contains_key(&("Ticket".to_owned(), "status".to_owned())));
        assert!(model
            .state_graphs
            .contains_key(&("Ticket".to_owned(), "priority".to_owned())));
        assert!(!model
            .state_graphs
            .contains_key(&("Ticket".to_owned(), "title".to_owned())));
        let title_meta = model
            .field_graph_meta
            .get(&("Ticket".to_owned(), "title".to_owned()))
            .expect("title field metadata");
        assert!(!title_meta.graphable);
        assert_eq!(title_meta.type_name, "string");
    }

    #[test]
    fn extract_system_info() {
        let system = IRSystem {
            name: "Commerce".to_owned(),
            fields: vec![],
            store_params: vec![],
            entities: vec!["Order".to_owned()],
            commands: vec![],
            actions: vec![IRSystemAction {
                name: "submit_order".to_owned(),
                params: vec![],
                guard: IRExpr::Lit {
                    ty: IRType::Bool,
                    value: LitVal::Bool { value: true },
                    span: None,
                },
                body: vec![IRAction::Choose {
                    var: "o".to_owned(),
                    entity: "Order".to_owned(),
                    filter: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    }),
                    ops: vec![IRAction::Apply {
                        target: "o".to_owned(),
                        transition: "submit".to_owned(),
                        refs: vec![],
                        args: vec![],
                    }],
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let info = super::extract_system_info(&system);
        assert_eq!(info.name, "Commerce");
        assert_eq!(info.entities, vec!["Order"]);
        assert_eq!(info.events.len(), 1);
        assert_eq!(info.events[0].name, "submit_order");
        assert_eq!(info.events[0].applies.len(), 1);
        assert_eq!(info.events[0].applies[0].action, "submit");
    }

    #[test]
    fn extract_bool_graphs_for_entity_and_system_fields() {
        let entity = IREntity {
            name: "Ticket".to_owned(),
            fields: vec![make_bool_field("ready", false)],
            transitions: vec![IRTransition {
                name: "activate".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "ready".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: false },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "ready".to_owned(),
                    value: IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: true },
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let system = IRSystem {
            name: "Workflow".to_owned(),
            fields: vec![make_bool_field("running", false)],
            store_params: vec![],
            entities: vec![],
            commands: vec![IRCommand {
                name: "start".to_owned(),
                params: vec![],
                return_type: None,
            }],
            actions: vec![IRSystemAction {
                name: "start".to_owned(),
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "running".to_owned(),
                        ty: IRType::Bool,
                        span: None,
                    }),
                    right: Box::new(IRExpr::Lit {
                        ty: IRType::Bool,
                        value: LitVal::Bool { value: false },
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                body: vec![IRAction::ExprStmt {
                    expr: IRExpr::BinOp {
                        op: "OpEq".to_owned(),
                        left: Box::new(IRExpr::Prime {
                            expr: Box::new(IRExpr::Var {
                                name: "running".to_owned(),
                                ty: IRType::Bool,
                                span: None,
                            }),
                            span: None,
                        }),
                        right: Box::new(IRExpr::Lit {
                            ty: IRType::Bool,
                            value: LitVal::Bool { value: true },
                            span: None,
                        }),
                        ty: IRType::Bool,
                        span: None,
                    },
                }],
                return_expr: None,
            }],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            queries: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![system],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let model = extract(&ir);
        let entity_graph = model
            .state_graphs
            .get(&("Ticket".to_owned(), "ready".to_owned()))
            .expect("entity bool graph");
        assert_eq!(
            entity_graph.states,
            vec!["false".to_owned(), "true".to_owned()]
        );
        assert_eq!(entity_graph.initial, Some("false".to_owned()));
        assert_eq!(entity_graph.transitions[0].to, "true");

        let system_graph = model
            .state_graphs
            .get(&("Workflow".to_owned(), "running".to_owned()))
            .expect("system bool graph");
        assert_eq!(system_graph.owner_kind, OwnerKind::System);
        assert_eq!(system_graph.initial, Some("false".to_owned()));
        assert_eq!(system_graph.transitions[0].action, "start");
        assert_eq!(system_graph.transitions[0].from, Some("false".to_owned()));
        assert_eq!(system_graph.transitions[0].to, "true");
    }

    #[test]
    fn extract_payload_enum_graphs_for_entity_fields() {
        let mode_ty = IRType::Enum {
            name: "WorkflowMode".to_owned(),
            variants: vec![
                crate::ir::types::IRVariant::simple("Idle"),
                crate::ir::types::IRVariant {
                    name: "Ready".to_owned(),
                    fields: vec![crate::ir::types::IRVariantField {
                        name: "armed".to_owned(),
                        ty: IRType::Bool,
                    }],
                },
            ],
        };
        let entity = IREntity {
            name: "Workflow".to_owned(),
            fields: vec![make_payload_enum_field("mode", false)],
            transitions: vec![IRTransition {
                name: "arm".to_owned(),
                refs: vec![],
                params: vec![],
                guard: IRExpr::BinOp {
                    op: "OpEq".to_owned(),
                    left: Box::new(IRExpr::Var {
                        name: "mode".to_owned(),
                        ty: mode_ty.clone(),
                        span: None,
                    }),
                    right: Box::new(IRExpr::Ctor {
                        enum_name: "WorkflowMode".to_owned(),
                        ctor: "Ready".to_owned(),
                        args: vec![(
                            "armed".to_owned(),
                            IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: false },
                                span: None,
                            },
                        )],
                        span: None,
                    }),
                    ty: IRType::Bool,
                    span: None,
                },
                updates: vec![IRUpdate {
                    field: "mode".to_owned(),
                    value: IRExpr::Ctor {
                        enum_name: "WorkflowMode".to_owned(),
                        ctor: "Ready".to_owned(),
                        args: vec![(
                            "armed".to_owned(),
                            IRExpr::Lit {
                                ty: IRType::Bool,
                                value: LitVal::Bool { value: true },
                                span: None,
                            },
                        )],
                        span: None,
                    },
                }],
                postcondition: None,
            }],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
        };
        let ir = IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![entity],
            systems: vec![],
            verifies: vec![],
            theorems: vec![],
            axioms: vec![],
            lemmas: vec![],
            scenes: vec![],
        };

        let model = extract(&ir);
        let graph = model
            .state_graphs
            .get(&("Workflow".to_owned(), "mode".to_owned()))
            .expect("state graph for Workflow.mode");
        assert_eq!(
            graph.states,
            vec![
                "Idle".to_owned(),
                "Ready{armed=false}".to_owned(),
                "Ready{armed=true}".to_owned(),
            ]
        );
        assert_eq!(graph.initial, Some("Ready{armed=false}".to_owned()));
        assert_eq!(graph.transitions.len(), 1);
        assert_eq!(
            graph.transitions[0].from,
            Some("Ready{armed=false}".to_owned())
        );
        assert_eq!(graph.transitions[0].to, "Ready{armed=true}");
    }
}
