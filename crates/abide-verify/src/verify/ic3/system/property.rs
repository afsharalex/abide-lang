use super::*;

#[derive(Clone, Copy)]
struct SystemPropertySlotBinding<'a> {
    entity: &'a IREntity,
    entity_name: &'a str,
    slot: usize,
    var: &'a str,
}

struct NegateSystemGuardInput<'a> {
    expr: &'a IRExpr,
    entities: &'a [&'a IREntity],
    slots_per_entity: &'a HashMap<String, usize>,
    vctx: &'a VerifyContext,
    binding: SystemPropertySlotBinding<'a>,
}

struct NegateSystemGuardTwoInput<'a> {
    expr: &'a IRExpr,
    entities: &'a [&'a IREntity],
    slots_per_entity: &'a HashMap<String, usize>,
    vctx: &'a VerifyContext,
    left: SystemPropertySlotBinding<'a>,
    right: SystemPropertySlotBinding<'a>,
}

#[derive(Clone, Copy)]
pub(in crate::verify::ic3) struct Ic3SystemPropertyCtx<'a> {
    pub(in crate::verify::ic3) entities: &'a [&'a IREntity],
    pub(in crate::verify::ic3) slots_per_entity: &'a HashMap<String, usize>,
    pub(in crate::verify::ic3) current_entity: &'a IREntity,
    pub(in crate::verify::ic3) vctx: &'a VerifyContext,
    pub(in crate::verify::ic3) current_ent_name: &'a str,
    pub(in crate::verify::ic3) current_slot: usize,
}

impl<'a> Ic3SystemPropertyCtx<'a> {
    const fn with_current_entity(
        self,
        current_entity: &'a IREntity,
        current_ent_name: &'a str,
        current_slot: usize,
    ) -> Self {
        Self {
            current_entity,
            current_ent_name,
            current_slot,
            ..self
        }
    }
}

pub(in crate::verify::ic3) fn negate_property_smt_system(
    property: &IRExpr,
    entities: &[&IREntity],
    vctx: &VerifyContext,
    slots_per_entity: &HashMap<String, usize>,
) -> Result<String, String> {
    match property {
        IRExpr::Always { body, .. } => {
            negate_property_smt_system(body, entities, vctx, slots_per_entity)
        }
        IRExpr::Forall {
            var,
            domain: IRType::Entity { name: entity_name },
            body,
            ..
        } => {
            let n_slots = slots_per_entity.get(entity_name).copied().unwrap_or(1);
            let entity = entities
                .iter()
                .find(|e| e.name == *entity_name)
                .ok_or_else(|| format!("entity {entity_name} not found in scope"))?;

            // Check for nested Forall
            if let IRExpr::Forall {
                var: var2,
                domain: IRType::Entity { name: ent2 },
                body: inner,
                ..
            } = body.as_ref()
            {
                let n_slots2 = slots_per_entity.get(ent2).copied().unwrap_or(1);
                let entity2 = entities
                    .iter()
                    .find(|e| e.name == *ent2)
                    .ok_or_else(|| format!("entity {ent2} not found in scope"))?;
                let mut disjuncts = Vec::new();
                for s1 in 0..n_slots {
                    for s2 in 0..n_slots2 {
                        let neg = negate_guard_sys_two(NegateSystemGuardTwoInput {
                            expr: inner,
                            entities,
                            slots_per_entity,
                            vctx,
                            left: SystemPropertySlotBinding {
                                entity,
                                entity_name,
                                slot: s1,
                                var,
                            },
                            right: SystemPropertySlotBinding {
                                entity: entity2,
                                entity_name: ent2,
                                slot: s2,
                                var: var2,
                            },
                        })?;
                        let a1 = format!("{entity_name}_{s1}_active");
                        let a2 = format!("{ent2}_{s2}_active");
                        disjuncts.push(format!("(and {a1} {a2} {neg})"));
                    }
                }
                return Ok(format!("(or {})", disjuncts.join(" ")));
            }

            // Single quantifier
            let mut disjuncts = Vec::new();
            for slot in 0..n_slots {
                let neg_body = negate_guard_sys(NegateSystemGuardInput {
                    expr: body,
                    entities,
                    slots_per_entity,
                    vctx,
                    binding: SystemPropertySlotBinding {
                        entity,
                        entity_name,
                        slot,
                        var,
                    },
                })?;
                let active = format!("{entity_name}_{slot}_active");
                disjuncts.push(format!("(and {active} {neg_body})"));
            }
            Ok(format!("(or {})", disjuncts.join(" ")))
        }
        _ => {
            let pure_entity = IREntity {
                name: "__PureProperty".to_owned(),
                fields: vec![],
                transitions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
            };
            let pos = guard_to_smt_sys_prop_scoped(
                property,
                Ic3SystemPropertyCtx {
                    entities,
                    slots_per_entity,
                    current_entity: &pure_entity,
                    vctx,
                    current_ent_name: "__PureProperty",
                    current_slot: 0,
                },
                &HashSet::new(),
                &Ic3SystemEntityLocals::new(),
            )?;
            Ok(format!("(not {pos})"))
        }
    }
}

/// Negate an inner property for a specific entity slot in system context.
fn negate_guard_sys(input: NegateSystemGuardInput<'_>) -> Result<String, String> {
    let NegateSystemGuardInput {
        expr,
        entities,
        slots_per_entity,
        vctx,
        binding,
    } = input;
    let mut entity_locals = Ic3SystemEntityLocals::new();
    entity_locals.insert(
        binding.var.to_owned(),
        (binding.entity_name.to_owned(), binding.slot),
    );
    let pos = guard_to_smt_sys_prop_scoped(
        expr,
        Ic3SystemPropertyCtx {
            entities,
            slots_per_entity,
            current_entity: binding.entity,
            vctx,
            current_ent_name: binding.entity_name,
            current_slot: binding.slot,
        },
        &HashSet::new(),
        &entity_locals,
    )?;
    Ok(format!("(not {pos})"))
}

/// Negate an inner property for two entity slots in system context.
fn negate_guard_sys_two(input: NegateSystemGuardTwoInput<'_>) -> Result<String, String> {
    let NegateSystemGuardTwoInput {
        expr,
        entities,
        slots_per_entity,
        vctx,
        left,
        right,
    } = input;
    let mut entity_locals = Ic3SystemEntityLocals::new();
    entity_locals.insert(
        left.var.to_owned(),
        (left.entity_name.to_owned(), left.slot),
    );
    entity_locals.insert(
        right.var.to_owned(),
        (right.entity_name.to_owned(), right.slot),
    );
    let pos = guard_to_smt_sys_prop_two_scoped(
        expr,
        Ic3SystemPropertyCtx {
            entities,
            slots_per_entity,
            current_entity: left.entity,
            vctx,
            current_ent_name: left.entity_name,
            current_slot: left.slot,
        },
        &HashSet::new(),
        &entity_locals,
    )?;
    Ok(format!("(not {pos})"))
}

pub(in crate::verify::ic3) fn ic3_find_entity<'a>(
    entities: &'a [&IREntity],
    name: &str,
) -> Result<&'a IREntity, String> {
    entities
        .iter()
        .find(|entity| entity.name == name)
        .copied()
        .ok_or_else(|| format!("entity {name} not found in IC3 system property scope"))
}

pub(in crate::verify::ic3) fn guard_let_to_smt_sys_prop_scoped(
    bindings: &[crate::ir::types::LetBinding],
    body: &IRExpr,
    ctx: Ic3SystemPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    let entities = ctx.entities;
    let slots_per_entity = ctx.slots_per_entity;
    let vctx = ctx.vctx;
    let current_ent_name = ctx.current_ent_name;
    let current_slot = ctx.current_slot;

    let Some((binding, rest)) = bindings.split_first() else {
        return guard_to_smt_sys_prop_scoped(body, ctx, locals, entity_locals);
    };

    if let IRExpr::Choose {
        var,
        domain,
        predicate,
        ..
    } = &binding.expr
    {
        if let IRType::Entity { name } = domain {
            let n_slots = slots_per_entity.get(name).copied().unwrap_or(1);
            let chosen_entity = ic3_find_entity(entities, name)?;
            let mut disjuncts = Vec::new();
            for chosen_slot in 0..n_slots {
                let active = format!("{name}_{chosen_slot}_active");
                let mut pred_entity_locals = entity_locals.clone();
                pred_entity_locals.insert(var.clone(), (name.clone(), chosen_slot));
                let pred = if let Some(predicate) = predicate {
                    guard_to_smt_sys_prop_scoped(predicate, ctx, locals, &pred_entity_locals)?
                } else {
                    "true".to_owned()
                };
                let mut rest_entity_locals = entity_locals.clone();
                rest_entity_locals.insert(binding.name.clone(), (name.clone(), chosen_slot));
                let rest_smt = guard_let_to_smt_sys_prop_scoped(
                    rest,
                    body,
                    ctx.with_current_entity(chosen_entity, current_ent_name, current_slot),
                    locals,
                    &rest_entity_locals,
                )?;
                disjuncts.push(format!("(and {active} {pred} {rest_smt})"));
            }
            return if disjuncts.is_empty() {
                Ok("false".to_owned())
            } else {
                Ok(format!("(or {})", disjuncts.join(" ")))
            };
        }

        let finite = ic3_finite_choose_witness(
            var,
            domain,
            predicate.as_deref(),
            vctx,
            locals,
            |predicate: &IRExpr, scope: &HashSet<String>| {
                guard_to_smt_sys_prop_scoped(predicate, ctx, scope, entity_locals)
            },
        )?;

        let mut scope = locals.clone();
        scope.insert(binding.name.clone());
        let rest_smt = guard_let_to_smt_sys_prop_scoped(rest, body, ctx, &scope, entity_locals)?;
        if let Some((exists, witness)) = finite {
            return Ok(format!(
                "(and {exists} (let (({} {})) {}))",
                binding.name, witness, rest_smt
            ));
        }
        if let Some(witness) = ic3_direct_choose_witness(
            Ic3DirectChooseInput {
                var,
                domain,
                predicate: predicate.as_deref(),
                locals,
            },
            Ic3DirectChooseHooks {
                encode_term: |term: &IRExpr, scope: &HashSet<String>| {
                    expr_to_smt_sys_prop_scoped(term, ctx, scope, entity_locals)
                },
                encode_predicate: |predicate: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_sys_prop_scoped(predicate, ctx, scope, entity_locals)
                },
                match_bindings: |scrutinee: &IRExpr,
                                 pattern: &crate::ir::types::IRPattern,
                                 scope: &HashSet<String>| {
                    let scrut = expr_to_smt_sys_prop_scoped(scrutinee, ctx, scope, entity_locals)?;
                    ic3_match_pattern_bindings(&scrut, pattern, vctx)
                },
                match_cond: |scrutinee: &IRExpr,
                             pattern: &crate::ir::types::IRPattern,
                             scope: &HashSet<String>| {
                    let scrut = expr_to_smt_sys_prop_scoped(scrutinee, ctx, scope, entity_locals)?;
                    ic3_match_pattern_cond(&scrut, pattern, vctx)
                },
            },
        )? {
            return ic3_witness_binding_formula(
                &binding.name,
                var,
                witness,
                predicate.as_deref(),
                locals,
                |predicate: &IRExpr, scope: &HashSet<String>| {
                    guard_to_smt_sys_prop_scoped(predicate, ctx, scope, entity_locals)
                },
                rest_smt,
            );
        }
        if let Some(formula) = ic3_quantified_choose_formula(
            &binding.name,
            var,
            domain,
            predicate.as_deref(),
            locals,
            |predicate: &IRExpr, scope: &HashSet<String>| {
                guard_to_smt_sys_prop_scoped(predicate, ctx, scope, entity_locals)
            },
            rest_smt.clone(),
        )? {
            return Ok(formula);
        }
        return Err("choose is not yet supported in IC3 CHC encoding for this domain".to_owned());
    }

    if matches!(binding.ty, IRType::Entity { .. }) {
        if let IRExpr::Var { name, .. } = &binding.expr {
            if let Some((bound_entity_name, bound_slot)) = entity_locals.get(name) {
                let mut scope_entity_locals = entity_locals.clone();
                scope_entity_locals.insert(
                    binding.name.clone(),
                    (bound_entity_name.clone(), *bound_slot),
                );
                return guard_let_to_smt_sys_prop_scoped(
                    rest,
                    body,
                    ctx,
                    locals,
                    &scope_entity_locals,
                );
            }
        }
    }

    let rhs = if binding.ty == IRType::Bool {
        guard_to_smt_sys_prop_scoped(&binding.expr, ctx, locals, entity_locals)?
    } else {
        expr_to_smt_sys_prop_scoped(&binding.expr, ctx, locals, entity_locals)?
    };
    let mut scope = locals.clone();
    scope.insert(binding.name.clone());
    let rest_smt = guard_let_to_smt_sys_prop_scoped(rest, body, ctx, &scope, entity_locals)?;
    Ok(format!("(let (({} {})) {})", binding.name, rhs, rest_smt))
}

pub(in crate::verify::ic3) fn expr_to_smt_sys_prop_scoped(
    expr: &IRExpr,
    ctx: Ic3SystemPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    let entities = ctx.entities;
    let current_entity = ctx.current_entity;
    let vctx = ctx.vctx;
    let current_ent_name = ctx.current_ent_name;
    let current_slot = ctx.current_slot;

    match expr {
        IRExpr::Var { name, .. } => {
            for (i, field) in current_entity.fields.iter().enumerate() {
                if field.name == *name {
                    return Ok(format!("{current_ent_name}_{current_slot}_f{i}"));
                }
            }
            if locals.contains(name) {
                return Ok(name.clone());
            }
            if entity_locals.contains_key(name) {
                return Err(format!(
                    "bare entity local {name} in system IC3 property — use field access instead"
                ));
            }
            Err(format!("unknown variable in system IC3 property: {name}"))
        }
        IRExpr::Field {
            expr: inner, field, ..
        } => {
            if ic3_expr_type(inner).is_some_and(|ty| ic3_enum_payload_type_has_field(ty, field)) {
                let inner_smt = expr_to_smt_sys_prop_scoped(inner, ctx, locals, entity_locals)?;
                return Ok(format!("({field} {inner_smt})"));
            }
            if let IRExpr::Var { name, .. } = inner.as_ref() {
                let (entity_name, slot) = if let Some((entity_name, slot)) = entity_locals.get(name)
                {
                    (entity_name.as_str(), *slot)
                } else {
                    (current_ent_name, current_slot)
                };
                let entity = ic3_find_entity(entities, entity_name)?;
                for (i, candidate) in entity.fields.iter().enumerate() {
                    if candidate.name == *field {
                        return Ok(format!("{entity_name}_{slot}_f{i}"));
                    }
                }
                return Err(format!("field {field} not found on entity {entity_name}"));
            }
            Err(format!(
                "unsupported field access in system IC3 property: {field}"
            ))
        }
        IRExpr::BinOp {
            op, left, right, ..
        } => {
            let l = expr_to_smt_sys_prop_scoped(left, ctx, locals, entity_locals)?;
            let r = expr_to_smt_sys_prop_scoped(right, ctx, locals, entity_locals)?;
            match op.as_str() {
                "OpAdd" => Ok(format!("(+ {l} {r})")),
                "OpSub" => Ok(format!("(- {l} {r})")),
                "OpMul" => Ok(format!("(* {l} {r})")),
                "OpDiv" => Ok(format!("(div {l} {r})")),
                "OpMod" => Ok(format!("(mod {l} {r})")),
                _ => Err(format!("unsupported op in system IC3 property value: {op}")),
            }
        }
        IRExpr::UnOp { op, operand, .. } if op == "OpNeg" => {
            let inner = expr_to_smt_sys_prop_scoped(operand, ctx, locals, entity_locals)?;
            Ok(format!("(- {inner})"))
        }
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            let m = expr_to_smt_sys_prop_scoped(map, ctx, locals, entity_locals)?;
            let k = expr_to_smt_sys_prop_scoped(key, ctx, locals, entity_locals)?;
            let v = expr_to_smt_sys_prop_scoped(value, ctx, locals, entity_locals)?;
            Ok(format!("(store {m} {k} {v})"))
        }
        IRExpr::Index { map, key, .. } => {
            let m = expr_to_smt_sys_prop_scoped(map, ctx, locals, entity_locals)?;
            let k = expr_to_smt_sys_prop_scoped(key, ctx, locals, entity_locals)?;
            Ok(format!("(select {m} {k})"))
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 property value encoding".to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_prop_scoped(scrutinee, ctx, locals, entity_locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = expr_to_smt_sys_prop_scoped(&last.body, ctx, &scope, entity_locals)?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt =
                        guard_to_smt_sys_prop_scoped(guard, ctx, &scope, entity_locals)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = expr_to_smt_sys_prop_scoped(&arm.body, ctx, &scope, entity_locals)?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_prop_scoped(cond, ctx, locals, entity_locals)?;
            let then_smt = expr_to_smt_sys_prop_scoped(then_body, ctx, locals, entity_locals)?;
            if let Some(else_body) = else_body {
                let else_smt = expr_to_smt_sys_prop_scoped(else_body, ctx, locals, entity_locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Err(
                    "if/else without else is not supported in system IC3 property value encoding"
                        .to_owned(),
                )
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            let mut scope = locals.clone();
            let mut out = String::new();
            for binding in bindings {
                let rhs = if binding.ty == IRType::Bool {
                    guard_to_smt_sys_prop_scoped(&binding.expr, ctx, &scope, entity_locals)?
                } else {
                    expr_to_smt_sys_prop_scoped(&binding.expr, ctx, &scope, entity_locals)?
                };
                out.push_str(&format!("(let (({} {})) ", binding.name, rhs));
                scope.insert(binding.name.clone());
            }
            out.push_str(&expr_to_smt_sys_prop_scoped(
                body,
                ctx,
                &scope,
                entity_locals,
            )?);
            for _ in bindings {
                out.push(')');
            }
            Ok(out)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            expr_to_smt_sys_prop_scoped(expr, ctx, locals, entity_locals)
        }
        IRExpr::Card { expr: inner, .. } => {
            if let Some(cardinality) = ic3_finite_literal_cardinality(inner) {
                return Ok(cardinality);
            }
            if let IRExpr::SetComp {
                var,
                domain,
                source: None,
                filter,
                projection,
                ..
            } = inner.as_ref()
            {
                if let Some(cardinality) = ic3_finite_setcomp_cardinality(
                    var,
                    domain,
                    filter,
                    projection.as_deref(),
                    vctx,
                    locals,
                    |body, scope| guard_to_smt_sys_prop_scoped(body, ctx, scope, entity_locals),
                )? {
                    return Ok(cardinality);
                }
            }
            Err("cardinality (#) not supported in system IC3 property value encoding".to_owned())
        }
        IRExpr::Lit { .. } | IRExpr::Ctor { .. } => expr_to_smt(expr, current_entity, vctx),
        _ => Err(format!(
            "unsupported expression in system IC3 property value encoding: {:?}",
            std::mem::discriminant(expr)
        )),
    }
}

pub(in crate::verify::ic3) fn guard_to_smt_sys_prop_scoped(
    guard: &IRExpr,
    ctx: Ic3SystemPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    let vctx = ctx.vctx;

    match guard {
        IRExpr::Lit {
            value: LitVal::Bool { value: true },
            ..
        } => Ok("true".to_owned()),
        IRExpr::Lit {
            value: LitVal::Bool { value: false },
            ..
        } => Ok("false".to_owned()),
        IRExpr::BinOp {
            op, left, right, ..
        } => match op.as_str() {
            "OpEq" | "OpNEq" | "OpLt" | "OpLe" | "OpGt" | "OpGe" => {
                let l = expr_to_smt_sys_prop_scoped(left, ctx, locals, entity_locals)?;
                let r = expr_to_smt_sys_prop_scoped(right, ctx, locals, entity_locals)?;
                Ok(match op.as_str() {
                    "OpEq" => format!("(= {l} {r})"),
                    "OpNEq" => format!("(not (= {l} {r}))"),
                    "OpLt" => format!("(< {l} {r})"),
                    "OpLe" => format!("(<= {l} {r})"),
                    "OpGt" => format!("(> {l} {r})"),
                    "OpGe" => format!("(>= {l} {r})"),
                    _ => unreachable!(),
                })
            }
            "OpAnd" => {
                let l = guard_to_smt_sys_prop_scoped(left, ctx, locals, entity_locals)?;
                let r = guard_to_smt_sys_prop_scoped(right, ctx, locals, entity_locals)?;
                Ok(format!("(and {l} {r})"))
            }
            "OpOr" => {
                let l = guard_to_smt_sys_prop_scoped(left, ctx, locals, entity_locals)?;
                let r = guard_to_smt_sys_prop_scoped(right, ctx, locals, entity_locals)?;
                Ok(format!("(or {l} {r})"))
            }
            "OpImplies" => {
                let l = guard_to_smt_sys_prop_scoped(left, ctx, locals, entity_locals)?;
                let r = guard_to_smt_sys_prop_scoped(right, ctx, locals, entity_locals)?;
                Ok(format!("(=> {l} {r})"))
            }
            _ => Err(format!("unsupported op in system IC3 property guard: {op}")),
        },
        IRExpr::UnOp { op, operand, .. } if op == "OpNot" => {
            let inner = guard_to_smt_sys_prop_scoped(operand, ctx, locals, entity_locals)?;
            Ok(format!("(not {inner})"))
        }
        IRExpr::Field { .. } | IRExpr::Var { .. } => {
            expr_to_smt_sys_prop_scoped(guard, ctx, locals, entity_locals)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            if !ic3_match_has_final_catch_all(arms) {
                return Err(
                    "non-exhaustive match without final wildcard/var arm is not supported in system IC3 property guard encoding".to_owned(),
                );
            }
            let scrut = expr_to_smt_sys_prop_scoped(scrutinee, ctx, locals, entity_locals)?;
            let mut acc = {
                let last = arms.last().expect("checked non-empty match arms");
                let bindings = ic3_match_pattern_bindings(&scrut, &last.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let body = guard_to_smt_sys_prop_scoped(&last.body, ctx, &scope, entity_locals)?;
                wrap_smt_let_bindings(&bindings, body)
            };
            for arm in arms[..arms.len() - 1].iter().rev() {
                let bindings = ic3_match_pattern_bindings(&scrut, &arm.pattern, vctx)?;
                let mut scope = locals.clone();
                for (name, _) in &bindings {
                    scope.insert(name.clone());
                }
                let pat = ic3_match_pattern_cond(&scrut, &arm.pattern, vctx)?;
                let cond = if let Some(guard) = &arm.guard {
                    let guard_smt =
                        guard_to_smt_sys_prop_scoped(guard, ctx, &scope, entity_locals)?;
                    wrap_smt_let_bindings(&bindings, format!("(and {pat} {guard_smt})"))
                } else {
                    wrap_smt_let_bindings(&bindings, pat)
                };
                let body = guard_to_smt_sys_prop_scoped(&arm.body, ctx, &scope, entity_locals)?;
                let body = wrap_smt_let_bindings(&bindings, body);
                acc = format!("(ite {cond} {body} {acc})");
            }
            Ok(acc)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let cond_smt = guard_to_smt_sys_prop_scoped(cond, ctx, locals, entity_locals)?;
            let then_smt = guard_to_smt_sys_prop_scoped(then_body, ctx, locals, entity_locals)?;
            if let Some(else_body) = else_body {
                let else_smt = guard_to_smt_sys_prop_scoped(else_body, ctx, locals, entity_locals)?;
                Ok(format!("(ite {cond_smt} {then_smt} {else_smt})"))
            } else {
                Ok(format!("(=> {cond_smt} {then_smt})"))
            }
        }
        IRExpr::Let { bindings, body, .. } => {
            guard_let_to_smt_sys_prop_scoped(bindings, body, ctx, locals, entity_locals)
        }
        IRExpr::Assert { expr, .. } | IRExpr::Assume { expr, .. } => {
            guard_to_smt_sys_prop_scoped(expr, ctx, locals, entity_locals)
        }
        IRExpr::Forall {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_prop_scoped(body, ctx, scope, entity_locals),
            "forall",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        IRExpr::Exists {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_prop_scoped(body, ctx, scope, entity_locals),
            "exists",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        IRExpr::One {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_prop_scoped(body, ctx, scope, entity_locals),
            "one",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        IRExpr::Lone {
            var, domain, body, ..
        } => ic3_finite_quantifier_formula(
            var,
            domain,
            body,
            vctx,
            locals,
            |body, scope| guard_to_smt_sys_prop_scoped(body, ctx, scope, entity_locals),
            "lone",
        )?
        .ok_or_else(|| {
            "quantifier domain is not yet supported in system IC3 property guard encoding"
                .to_owned()
        }),
        _ => Err(format!(
            "unsupported expression in system IC3 property guard: {:?}",
            std::mem::discriminant(guard)
        )),
    }
}

pub(in crate::verify::ic3) fn guard_to_smt_sys_prop_two_scoped(
    expr: &IRExpr,
    ctx: Ic3SystemPropertyCtx<'_>,
    locals: &HashSet<String>,
    entity_locals: &Ic3SystemEntityLocals,
) -> Result<String, String> {
    guard_to_smt_sys_prop_scoped(expr, ctx, locals, entity_locals)
}
