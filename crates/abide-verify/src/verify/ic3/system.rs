use std::collections::{HashMap, HashSet};

use super::*;

mod actions;
mod expr;
mod property;

pub(super) use self::actions::*;
pub(super) use self::expr::*;
pub(super) use self::property::*;

/// Build unified CHC encoding for multiple entity types and systems.
#[allow(clippy::format_push_string, clippy::too_many_lines)]
pub(super) fn build_system_chc(
    entities: &[&IREntity],
    systems: &[&IRSystem],
    vctx: &VerifyContext,
    property: &IRExpr,
    slots_per_entity: &HashMap<String, usize>,
) -> Result<String, String> {
    let mut chc = String::new();
    emit_ic3_datatype_decls(
        entities
            .iter()
            .flat_map(|entity| entity.fields.iter().map(|field| &field.ty)),
        &mut chc,
    );

    // Build column layout: for each entity type, for each slot, fields + active
    let mut columns: Vec<SlotColumn> = Vec::new();
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
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

    // Declare State relation
    chc.push_str("(declare-rel State (");
    for col in &columns {
        chc.push_str(&col.sort_name);
        chc.push(' ');
    }
    chc.push_str("))\n");
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables
    for col in &columns {
        chc.push_str(&format!(
            "(declare-var {} {})\n",
            col.var_name, col.sort_name
        ));
    }
    let all_vars_str: String = columns
        .iter()
        .map(|c| c.var_name.as_str())
        .collect::<Vec<_>>()
        .join(" ");

    // ── Initial state: all slots inactive ──────────────────────────
    chc.push_str("(rule (State ");
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if let Some(ref default_expr) = f.default {
                    chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
                } else {
                    chc.push_str(&format!("{}_{}_f{}", entity.name, slot, fi));
                }
                chc.push(' ');
            }
            chc.push_str("false "); // inactive
        }
    }
    chc.push_str(") init)\n");

    // ── Stutter rule ───────────────────────────────────────────────
    chc.push_str(&format!(
        "(rule (=> (State {all_vars_str}) (State {all_vars_str})) stutter)\n"
    ));

    // ── Entity transition rules ────────────────────────────────────
    // Only emitted when no systems are present (pure entity-level IC3).
    // When systems exist, transitions are constrained by system event rules.
    if systems.is_empty() {
        for entity in entities {
            let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
            for slot in 0..n_slots {
                for transition in &entity.transitions {
                    let guard =
                        guard_to_smt_sys(&transition.guard, entity, vctx, &entity.name, slot)?;

                    // Build next-state: update target slot, frame everything else
                    let mut next_vals: Vec<String> = Vec::new();
                    for ent in entities {
                        let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                        for s in 0..ns {
                            for (fi, f) in ent.fields.iter().enumerate() {
                                if ent.name == entity.name && s == slot {
                                    let updated =
                                        transition.updates.iter().find(|u| u.field == f.name);
                                    if let Some(upd) = updated {
                                        next_vals.push(expr_to_smt_sys(
                                            &upd.value,
                                            entity,
                                            vctx,
                                            &entity.name,
                                            slot,
                                        )?);
                                    } else {
                                        next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                                    }
                                } else {
                                    next_vals.push(format!("{}_{}_f{}", ent.name, s, fi));
                                }
                            }
                            if ent.name == entity.name && s == slot {
                                next_vals.push("true".to_owned());
                            } else {
                                next_vals.push(format!("{}_{}_active", ent.name, s));
                            }
                        }
                    }
                    let next_str = next_vals.join(" ");
                    let active_var = format!("{}_{}_active", entity.name, slot);

                    chc.push_str(&format!(
                        "(rule (=> (and (State {all_vars_str}) {active_var} {guard}) \
                     (State {next_str})) trans_{}_{}_{slot})\n",
                        entity.name, transition.name
                    ));
                }

                // Create rule for this entity slot
                let mut create_next: Vec<String> = Vec::new();
                for ent in entities {
                    let ns = slots_per_entity.get(&ent.name).copied().unwrap_or(1);
                    for s in 0..ns {
                        for (fi, f) in ent.fields.iter().enumerate() {
                            if ent.name == entity.name && s == slot {
                                if f.initial_constraint.is_some() {
                                    // Nondeterministic: leave as free variable
                                    // (the constraint is enforced by the BMC path, not CHC)
                                    create_next.push(format!("{}_{}_f{}", ent.name, s, fi));
                                } else if let Some(ref default_expr) = f.default {
                                    create_next.push(expr_to_smt(default_expr, entity, vctx)?);
                                } else {
                                    create_next.push(format!("{}_{}_f{}", ent.name, s, fi));
                                }
                            } else {
                                create_next.push(format!("{}_{}_f{}", ent.name, s, fi));
                            }
                        }
                        if ent.name == entity.name && s == slot {
                            create_next.push("true".to_owned());
                        } else {
                            create_next.push(format!("{}_{}_active", ent.name, s));
                        }
                    }
                }
                let create_str = create_next.join(" ");
                let inactive_var = format!("{}_{}_active", entity.name, slot);

                // Symmetry: slot i requires slot i-1 active
                let mut create_guard = if slot == 0 {
                    format!("(not {inactive_var})")
                } else {
                    format!(
                        "(and (not {inactive_var}) {}_{}_active)",
                        entity.name,
                        slot - 1
                    )
                };

                // Add initial_constraint guards for nondeterministic fields.
                // The free variable in create_next is `{ent}_{slot}_f{fi}` —
                // substitute $ for it in the constraint and add to the guard.
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

                chc.push_str(&format!(
                    "(rule (=> (and (State {all_vars_str}) {create_guard}) \
                 (State {create_str})) create_{}_{slot})\n",
                    entity.name
                ));
            }
        }
    } // if systems.is_empty()

    // ── System event rules ──────────────────────────────────────────
    // Encode system events as composite CHC rules via recursive action tree walk.
    // Choose/ForAll/Apply/Create/CrossCall are all handled with full context
    // guard propagation. CrossCall targets are recursively encoded (not just Creates).
    for system in systems {
        for event in &system.steps {
            // Fresh visited set per event tree — cycles within one event's
            // CrossCall graph are detected, but the same event can appear
            // in different top-level event trees.
            let mut visited = HashSet::new();
            visited.insert((system.name.clone(), event.name.clone()));
            encode_step_chc(
                &mut chc,
                &event.body,
                &event.guard,
                entities,
                vctx,
                slots_per_entity,
                &all_vars_str,
                systems,
                &format!("{}_{}", system.name, event.name),
                &[],
                &mut visited,
            )?;
        }
    }

    // ── Domain constraints ─────────────────────────────────────────
    for entity in entities {
        let n_slots = slots_per_entity.get(&entity.name).copied().unwrap_or(1);
        for slot in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if let IRType::Enum { name, variants } = &f.ty {
                    if variants.iter().any(|variant| !variant.fields.is_empty()) {
                        continue;
                    }
                    if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                        let var = format!("{}_{}_f{}", entity.name, slot, fi);
                        let active = format!("{}_{}_active", entity.name, slot);
                        chc.push_str(&format!(
                            "(rule (=> (and (State {all_vars_str}) {active} \
                             (or (< {var} {min_id}) (> {var} {max_id}))) Error) \
                             domain_{}_{}_{fi})\n",
                            entity.name, slot
                        ));
                    }
                }
            }
        }
    }

    // ── Error rule: property violation ──────────────────────────────
    let neg_prop = negate_property_smt_system(property, entities, vctx, slots_per_entity)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}
