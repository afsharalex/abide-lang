use std::collections::{HashMap, HashSet};

use super::*;
use crate::verify::smt;

mod choose;
mod decls;
mod expr;
mod patterns;
mod property;

pub(super) use self::choose::*;
pub(super) use self::decls::*;
pub(super) use self::expr::*;
pub(super) use self::patterns::*;
pub(super) use self::property::*;

pub(super) fn build_multi_slot_chc(
    entity: &IREntity,
    vctx: &VerifyContext,
    property: &IRExpr,
    n_slots: usize,
) -> Result<String, String> {
    let n_fields = entity.fields.len();

    let mut chc = String::new();
    emit_ic3_datatype_decls(entity.fields.iter().map(|field| &field.ty), &mut chc);

    // Declare State relation with all slot columns
    chc.push_str("(declare-rel State (");
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            let _ = (slot, fi); // used for ordering
            chc.push_str(&ir_type_to_sort_name(&f.ty));
            chc.push(' ');
        }
        chc.push_str("Bool "); // active flag for this slot
    }
    chc.push_str("))\n");
    chc.push_str("(declare-rel Error ())\n");

    // Declare variables for each slot's fields + active
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            chc.push_str(&format!(
                "(declare-var s{slot}_f{fi} {})\n",
                ir_type_to_sort_name(&f.ty)
            ));
        }
        chc.push_str(&format!("(declare-var s{slot}_active Bool)\n"));
    }
    // Helper: build a var list for all slots
    let all_vars: Vec<String> = (0..n_slots)
        .flat_map(|s| {
            let mut v: Vec<String> = (0..n_fields).map(|fi| format!("s{s}_f{fi}")).collect();
            v.push(format!("s{s}_active"));
            v
        })
        .collect();
    let all_vars_str = all_vars.join(" ");

    // ── Initial state: all slots inactive ──────────────────────────
    chc.push_str("(rule (State ");
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            if let Some(ref default_expr) = f.default {
                chc.push_str(&expr_to_smt(default_expr, entity, vctx)?);
            } else {
                chc.push_str(&format!("s{slot}_f{fi}"));
            }
            chc.push(' ');
        }
        chc.push_str("false "); // all inactive
    }
    chc.push_str(") init)\n");

    // ── Transition rules: for each slot × transition ───────────────
    for slot in 0..n_slots {
        for transition in &entity.transitions {
            let guard = guard_to_smt_slot(&transition.guard, entity, vctx, slot, n_slots)?;

            // Build next-state: this slot gets updates, all other slots frame
            let mut next_vals: Vec<String> = Vec::new();
            for s in 0..n_slots {
                for (fi, f) in entity.fields.iter().enumerate() {
                    if s == slot {
                        let updated = transition.updates.iter().find(|u| u.field == f.name);
                        if let Some(upd) = updated {
                            next_vals
                                .push(expr_to_smt_slot(&upd.value, entity, vctx, slot, n_slots)?);
                        } else {
                            next_vals.push(format!("s{s}_f{fi}")); // frame
                        }
                    } else {
                        next_vals.push(format!("s{s}_f{fi}")); // frame: other slot unchanged
                    }
                }
                if s == slot {
                    next_vals.push("true".to_owned()); // active stays true
                } else {
                    next_vals.push(format!("s{s}_active")); // frame: other slot's active unchanged
                }
            }
            let next_str = next_vals.join(" ");

            chc.push_str(&format!(
                "(rule (=> (and (State {all_vars_str}) s{slot}_active {guard}) \
                 (State {next_str})) trans_{}_s{slot})\n",
                transition.name
            ));
        }
    }

    // ── Create rules: for each slot, if inactive → activate with defaults ──
    for slot in 0..n_slots {
        let mut next_vals: Vec<String> = Vec::new();
        for s in 0..n_slots {
            for (fi, f) in entity.fields.iter().enumerate() {
                if s == slot {
                    if let Some(ref default_expr) = f.default {
                        next_vals.push(expr_to_smt(default_expr, entity, vctx)?);
                    } else {
                        next_vals.push(format!("s{s}_f{fi}")); // unconstrained
                    }
                } else {
                    next_vals.push(format!("s{s}_f{fi}")); // frame
                }
            }
            if s == slot {
                next_vals.push("true".to_owned()); // activate this slot
            } else {
                next_vals.push(format!("s{s}_active")); // frame
            }
        }
        let next_str = next_vals.join(" ");

        // Symmetry breaking: slot i can only be created if slot i-1 is active.
        // Slot 0 can always be created (no prerequisite).
        let create_guard = if slot == 0 {
            format!("(not s{slot}_active)")
        } else {
            format!("(and (not s{slot}_active) s{}_active)", slot - 1)
        };

        chc.push_str(&format!(
            "(rule (=> (and (State {all_vars_str}) {create_guard}) \
             (State {next_str})) create_s{slot})\n"
        ));
    }

    // ── Stutter rule ───────────────────────────────────────────────
    chc.push_str(&format!(
        "(rule (=> (State {all_vars_str}) (State {all_vars_str})) stutter)\n"
    ));

    // ── Domain constraints for enum fields ─────────────────────────
    // Use VerifyContext enum_ranges for correct globally-allocated variant IDs
    for slot in 0..n_slots {
        for (fi, f) in entity.fields.iter().enumerate() {
            if let IRType::Enum { name, variants } = &f.ty {
                if variants.iter().any(|variant| !variant.fields.is_empty()) {
                    continue;
                }
                if let Some(&(min_id, max_id)) = vctx.enum_ranges.get(name) {
                    chc.push_str(&format!(
                        "(rule (=> (and (State {all_vars_str}) s{slot}_active \
                         (or (< s{slot}_f{fi} {min_id}) (> s{slot}_f{fi} {max_id}))) Error) \
                         domain_s{slot}_f{fi})\n"
                    ));
                }
            }
        }
    }

    // ── Error rule: property violation on any active entity ────────
    let neg_prop = negate_property_smt_multi(property, entity, vctx, n_slots)?;
    chc.push_str(&format!(
        "(rule (=> (and (State {all_vars_str}) {neg_prop}) Error) error)\n"
    ));

    Ok(chc)
}
