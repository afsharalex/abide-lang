use std::collections::{HashMap, HashSet};

use super::*;

mod actions;
mod expr;
mod property;

pub(super) use self::actions::*;
pub(super) use self::expr::*;
pub(super) use self::property::*;

#[derive(Clone, Copy)]
struct SystemChcCtx<'a> {
    entities: &'a [&'a IREntity],
    systems: &'a [&'a IRSystem],
    vctx: &'a VerifyContext,
    slots_per_entity: &'a HashMap<String, usize>,
}

/// Build unified CHC encoding for multiple entity types and systems.
#[cfg(test)]
pub(super) fn build_system_chc(
    entities: &[&IREntity],
    systems: &[&IRSystem],
    vctx: &VerifyContext,
    property: &IRExpr,
    slots_per_entity: &HashMap<String, usize>,
) -> Result<String, String> {
    build_system_chc_with_semantics(
        entities,
        systems,
        vctx,
        property,
        slots_per_entity,
        Ic3TransitionSemantics::default(),
    )
}

/// Build unified CHC encoding for multiple entity types and systems.
#[allow(clippy::format_push_string)]
pub(super) fn build_system_chc_with_semantics(
    entities: &[&IREntity],
    systems: &[&IRSystem],
    vctx: &VerifyContext,
    property: &IRExpr,
    slots_per_entity: &HashMap<String, usize>,
    semantics: Ic3TransitionSemantics,
) -> Result<String, String> {
    if !semantics.allow_stutter && !systems.is_empty() {
        return Err(
            "no-stutter IC3 for system actions requires deadlock-aware enabledness encoding"
                .to_owned(),
        );
    }

    let ctx = SystemChcCtx {
        entities,
        systems,
        vctx,
        slots_per_entity,
    };
    let mut chc = String::new();
    let all_vars_str = emit_system_state_declarations(&mut chc, ctx, property);
    emit_system_initial_rule(&mut chc, ctx)?;

    let mut enabled_steps = Vec::new();
    if semantics.allow_stutter {
        chc.push_str(&format!(
            "(rule (=> (State {all_vars_str}) (State {all_vars_str})) stutter)\n"
        ));
    }
    emit_entity_rules(&mut chc, ctx, &all_vars_str, &mut enabled_steps)?;
    emit_deadlock_rule(&mut chc, semantics, &all_vars_str, enabled_steps.as_slice());
    emit_system_event_rules(&mut chc, ctx, &all_vars_str)?;
    emit_domain_constraints(&mut chc, ctx, &all_vars_str);

    let neg_prop = negate_property_smt_system(property, entities, vctx, slots_per_entity)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}

#[allow(clippy::format_push_string)]
fn emit_system_state_declarations(
    chc: &mut String,
    ctx: SystemChcCtx<'_>,
    property: &IRExpr,
) -> String {
    emit_ic3_datatype_decls_with_expr(
        ctx.entities
            .iter()
            .flat_map(|entity| entity.fields.iter().map(|field| &field.ty)),
        property,
        chc,
    );

    let columns = system_slot_columns(ctx);
    chc.push_str("(declare-rel State (");
    for col in &columns {
        chc.push_str(&col.sort_name);
        chc.push(' ');
    }
    chc.push_str("))\n");
    chc.push_str("(declare-rel Error ())\n");

    for col in &columns {
        chc.push_str(&format!(
            "(declare-var {} {})\n",
            col.var_name, col.sort_name
        ));
    }

    columns
        .iter()
        .map(|c| c.var_name.as_str())
        .collect::<Vec<_>>()
        .join(" ")
}

fn system_slot_columns(ctx: SystemChcCtx<'_>) -> Vec<SlotColumn> {
    let mut columns = Vec::new();
    for entity in ctx.entities {
        let n_slots = ctx.slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                columns.push(SlotColumn {
                    var_name: format!("{}_{}_f{}", entity.name, slot, fi),
                    sort_name: ir_type_to_sort_name(&f.ty),
                });
            }
            columns.push(SlotColumn {
                var_name: format!("{}_{}_active", entity.name, slot),
                sort_name: "Bool".to_owned(),
            });
        }
    }
    columns
}

#[allow(clippy::format_push_string)]
fn emit_system_initial_rule(chc: &mut String, ctx: SystemChcCtx<'_>) -> Result<(), String> {
    chc.push_str("(rule (State ");
    for entity in ctx.entities {
        let n_slots = ctx.slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if let Some(ref default_expr) = f.default {
                    chc.push_str(&expr_to_smt(default_expr, entity, ctx.vctx)?);
                } else {
                    chc.push_str(&format!("{}_{}_f{}", entity.name, slot, fi));
                }
                chc.push(' ');
            }
            chc.push_str("false ");
        }
    }
    chc.push_str(") init)\n");
    Ok(())
}

fn emit_entity_rules(
    chc: &mut String,
    ctx: SystemChcCtx<'_>,
    all_vars_str: &str,
    enabled_steps: &mut Vec<String>,
) -> Result<(), String> {
    for entity in ctx.entities {
        let n_slots = ctx.slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            emit_entity_transition_rules(chc, ctx, entity, slot, all_vars_str, enabled_steps)?;
            emit_entity_create_rule(chc, ctx, entity, slot, all_vars_str, enabled_steps)?;
        }
    }
    Ok(())
}

#[allow(clippy::format_push_string)]
fn emit_entity_transition_rules(
    chc: &mut String,
    ctx: SystemChcCtx<'_>,
    entity: &IREntity,
    slot: usize,
    all_vars_str: &str,
    enabled_steps: &mut Vec<String>,
) -> Result<(), String> {
    for transition in &entity.transitions {
        let guard = guard_to_smt_sys(&transition.guard, entity, ctx.vctx, &entity.name, slot)?;
        let active_var = format!("{}_{}_active", entity.name, slot);
        enabled_steps.push(format!("(and {active_var} {guard})"));
        let next_str = build_transition_next(
            ctx.entities,
            ctx.slots_per_entity,
            entity,
            &entity.name,
            slot,
            transition,
            ctx.vctx,
        )?;

        chc.push_str(&format!(
            "(rule (=> (and (State {all_vars_str}) {active_var} {guard}) \
             (State {next_str})) trans_{}_{}_{slot})\n",
            entity.name, transition.name
        ));
    }
    Ok(())
}

#[allow(clippy::format_push_string)]
fn emit_entity_create_rule(
    chc: &mut String,
    ctx: SystemChcCtx<'_>,
    entity: &IREntity,
    slot: usize,
    all_vars_str: &str,
    enabled_steps: &mut Vec<String>,
) -> Result<(), String> {
    let create_str = build_create_next(
        ctx.entities,
        ctx.slots_per_entity,
        entity,
        &entity.name,
        slot,
        &[],
        ctx.vctx,
    )?;
    let create_guard = system_create_guard(entity, slot, ctx.vctx);
    enabled_steps.push(create_guard.clone());

    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {create_guard}) \
         (State {create_str})) create_{}_{slot})\n",
        entity.name
    ));
    Ok(())
}

fn system_create_guard(entity: &IREntity, slot: usize, vctx: &VerifyContext) -> String {
    let inactive_var = format!("{}_{}_active", entity.name, slot);
    let mut create_guard = if slot == 0 {
        format!("(not {inactive_var})")
    } else {
        format!(
            "(and (not {inactive_var}) {}_{}_active)",
            entity.name,
            slot - 1
        )
    };

    for (fi, f) in entity.fields.iter().enumerate() {
        if let Some(ref constraint) = f.initial_constraint {
            let field_var = format!("{}_{}_f{}", entity.name, slot, fi);
            if let Ok(constraint_smt) =
                constraint_to_smt_with_dollar(constraint, &field_var, entity, vctx)
            {
                create_guard = format!("(and {create_guard} {constraint_smt})");
            }
        }
    }
    create_guard
}

#[allow(clippy::format_push_string)]
fn emit_deadlock_rule(
    chc: &mut String,
    semantics: Ic3TransitionSemantics,
    all_vars_str: &str,
    enabled_steps: &[String],
) {
    if semantics.allow_stutter {
        return;
    }
    let no_enabled = enabled_steps
        .iter()
        .map(|enabled| format!("(not {enabled})"))
        .collect::<Vec<_>>()
        .join(" ");
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {no_enabled}) Error) \
         deadlock_no_stutter)\n"
    ));
}

fn emit_system_event_rules(
    chc: &mut String,
    ctx: SystemChcCtx<'_>,
    all_vars_str: &str,
) -> Result<(), String> {
    for system in ctx.systems {
        for event in &system.actions {
            let mut visited = HashSet::new();
            visited.insert((system.name.clone(), event.name.clone()));
            encode_step_chc(
                chc,
                Ic3SystemActionCtx {
                    entities: ctx.entities,
                    vctx: ctx.vctx,
                    slots_per_entity: ctx.slots_per_entity,
                    all_vars_str,
                    all_systems: ctx.systems,
                },
                EncodeStepChcInput {
                    actions: &event.body,
                    event_guard: &event.guard,
                    rule_prefix: &format!("{}_{}", system.name, event.name),
                    extra_guards: &[],
                },
                &mut visited,
            )?;
        }
    }
    Ok(())
}

#[allow(clippy::format_push_string)]
fn emit_domain_constraints(chc: &mut String, ctx: SystemChcCtx<'_>, all_vars_str: &str) {
    for entity in ctx.entities {
        let n_slots = ctx.slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                emit_enum_domain_constraint(chc, ctx, entity, slot, fi, f, all_vars_str);
            }
        }
    }
}

#[allow(clippy::format_push_string)]
fn emit_enum_domain_constraint(
    chc: &mut String,
    ctx: SystemChcCtx<'_>,
    entity: &IREntity,
    slot: usize,
    field_index: usize,
    field: &crate::ir::types::IRField,
    all_vars_str: &str,
) {
    let IRType::Enum { name, variants } = &field.ty else {
        return;
    };
    if variants.iter().any(|variant| !variant.fields.is_empty()) {
        return;
    }
    let Some(&(min_id, max_id)) = ctx.vctx.enum_ranges.get(name) else {
        return;
    };
    let var = format!("{}_{}_f{}", entity.name, slot, field_index);
    let active = format!("{}_{}_active", entity.name, slot);
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {active} \
         (or (< {var} {min_id}) (> {var} {max_id}))) Error) \
         domain_{}_{}_{field_index})\n",
        entity.name, slot
    ));
}
