//! Theorem and lemma proving — IC3/PDR, 1-induction, tautology checking.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use abide_witness::{Countermodel, EvidenceEnvelope, WitnessEnvelope};

use crate::ir::types::{IRExpr, IRProgram, IRSystem, IRTheorem, IRVerify};

use super::context::VerifyContext;
use super::defenv;
use super::encode::encode_pure_expr_inner;
use super::harness::{
    create_slot_pool_with_systems, domain_constraints, initial_state_constraints,
    transition_constraints,
};
use super::property::{encode_prop_expr_with_ctx, PropertyCtx};
use super::smt::{self, AbideSolver, Bool, SatResult, SmtValue};
use super::{
    assert_lambda_axioms_on, collect_in_scope_invariants, compute_theorem_scope, contains_temporal,
    has_multi_entity_quantifier, ic3_trace_to_operational_witness, proof_artifact_ref_for_locator,
    select_verify_relevant, CompiledTemporalFormula,
};
use super::{
    clamp_timeout_to_deadline, elapsed_ms, encode_property_at_step, expand_through_defs, expr_span,
    find_unsupported_in_actions, find_unsupported_scene_expr, try_liveness_reduction,
    verification_timeout_hint, VerificationResult, VerifyConfig,
};

fn encode_pure_property_expr(
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    expr: &IRExpr,
) -> Result<Bool, String> {
    if !needs_property_encoder(expr) {
        let env = HashMap::<String, SmtValue>::new();
        let val = encode_pure_expr_inner(expr, &env, vctx, defs, None)?;
        return val.to_bool().map_err(|e| e.to_string());
    }
    let pool = create_slot_pool_with_systems(&[], &HashMap::new(), 0, &[]);
    encode_prop_expr_with_ctx(&pool, vctx, defs, &PropertyCtx::new(), expr, 0)
}

fn needs_property_encoder(expr: &IRExpr) -> bool {
    match expr {
        IRExpr::Choose { .. } | IRExpr::Assert { .. } | IRExpr::Assume { .. } => true,
        IRExpr::Lam { body, .. }
        | IRExpr::Always { body, .. }
        | IRExpr::Eventually { body, .. }
        | IRExpr::Historically { body, .. }
        | IRExpr::Once { body, .. }
        | IRExpr::Previously { body, .. }
        | IRExpr::Card { expr: body, .. }
        | IRExpr::UnOp { operand: body, .. } => needs_property_encoder(body),
        IRExpr::Let { bindings, body, .. } => {
            bindings
                .iter()
                .any(|binding| needs_property_encoder(&binding.expr))
                || needs_property_encoder(body)
        }
        IRExpr::VarDecl { init, rest, .. } => {
            needs_property_encoder(init) || needs_property_encoder(rest)
        }
        IRExpr::IfElse {
            cond,
            then_body,
            else_body,
            ..
        } => {
            needs_property_encoder(cond)
                || needs_property_encoder(then_body)
                || else_body
                    .as_ref()
                    .is_some_and(|e| needs_property_encoder(e))
        }
        IRExpr::BinOp { left, right, .. }
        | IRExpr::Until { left, right, .. }
        | IRExpr::Since { left, right, .. } => {
            needs_property_encoder(left) || needs_property_encoder(right)
        }
        IRExpr::App { func, arg, .. } => {
            needs_property_encoder(func) || needs_property_encoder(arg)
        }
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::One { body, .. }
        | IRExpr::Lone { body, .. } => needs_property_encoder(body),
        IRExpr::Aggregate {
            body, in_filter, ..
        } => {
            needs_property_encoder(body)
                || in_filter
                    .as_ref()
                    .is_some_and(|e| needs_property_encoder(e))
        }
        IRExpr::Field { expr, .. } => needs_property_encoder(expr),
        IRExpr::SetLit {
            elements: items, ..
        }
        | IRExpr::SeqLit {
            elements: items, ..
        } => items.iter().any(needs_property_encoder),
        IRExpr::MapLit { entries, .. } => entries
            .iter()
            .any(|(k, v)| needs_property_encoder(k) || needs_property_encoder(v)),
        IRExpr::MapUpdate {
            map, key, value, ..
        } => {
            needs_property_encoder(map)
                || needs_property_encoder(key)
                || needs_property_encoder(value)
        }
        IRExpr::Index { map, key, .. } => {
            needs_property_encoder(map) || needs_property_encoder(key)
        }
        IRExpr::Match {
            scrutinee, arms, ..
        } => {
            needs_property_encoder(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(needs_property_encoder)
                        || needs_property_encoder(&arm.body)
                })
        }
        IRExpr::Block { exprs, .. } => exprs.iter().any(needs_property_encoder),
        IRExpr::While {
            cond,
            invariants,
            body,
            ..
        } => {
            needs_property_encoder(cond)
                || invariants.iter().any(needs_property_encoder)
                || needs_property_encoder(body)
        }
        IRExpr::Ctor { args, .. } => args.iter().any(|(_, arg)| needs_property_encoder(arg)),
        IRExpr::Saw { args, .. } => args.iter().flatten().any(|arg| needs_property_encoder(arg)),
        IRExpr::SetComp {
            filter, projection, ..
        } => {
            needs_property_encoder(filter)
                || projection
                    .as_ref()
                    .is_some_and(|expr| needs_property_encoder(expr))
        }
        IRExpr::RelComp {
            projection,
            bindings,
            filter,
            ..
        } => {
            needs_property_encoder(projection)
                || needs_property_encoder(filter)
                || bindings.iter().any(|binding| {
                    binding
                        .source
                        .as_ref()
                        .is_some_and(|source| needs_property_encoder(source))
                })
        }
        IRExpr::Lit { .. }
        | IRExpr::Var { .. }
        | IRExpr::Prime { .. }
        | IRExpr::Sorry { .. }
        | IRExpr::Todo { .. } => false,
    }
}

// ── Theorem proving (IC3 → 1-induction) ─────────────────────────────

/// Check a theorem block using IC3/PDR, then 1-induction as fallback.
///
/// **IC3/PDR** is tried first — it automatically discovers strengthening
/// invariants, proving properties that aren't directly 1-inductive.
///
/// If IC3 fails or is skipped (`--no-ic3`), falls back to staged
/// 1-induction with user-provided invariants:
///
/// 0. Invariant base: I holds at step 0
/// 1. Invariant step: I(k) ∧ transition → I(k+1)
/// 2. Property base: P holds at step 0
/// 3. Property step: I(k) ∧ P(k) ∧ transition → P(k+1)
///
/// If every pass succeeds, return `PROVED`. Otherwise return `UNPROVABLE`
/// with a hint.
#[allow(clippy::too_many_lines)]
pub(super) fn check_theorem_block(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    theorem: &IRTheorem,
    config: &VerifyConfig,
    _deadline: Option<Instant>,
) -> VerificationResult {
    let start = Instant::now();

    if let Some(by_file) = theorem.by_file.as_deref() {
        let elapsed = elapsed_ms(&start);
        let evidence = match proof_artifact_ref_for_locator(by_file, Some(&theorem.name)) {
            Ok(proof_artifact) => Some(
                EvidenceEnvelope::proof_artifact_ref(proof_artifact).map_err(|err| {
                    format!("theorem proof artifact evidence validation failed: {err}")
                }),
            ),
            Err(err) => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: err,
                    span: theorem.span,
                    file: theorem.file.clone(),
                };
            }
        };
        let (evidence, evidence_error) = match evidence {
            Some(Ok(evidence)) => (Some(evidence), None),
            Some(Err(err)) => (None, Some(err)),
            None => (None, None),
        };
        let reason = if let Some(err) = evidence_error {
            format!("external proof artifact reference ({err})")
        } else {
            "external proof artifact reference".to_owned()
        };
        return VerificationResult::Admitted {
            name: theorem.name.clone(),
            reason,
            time_ms: elapsed,
            evidence,
            assumptions: super::build_assumptions_for_system_scope(
                ir,
                &theorem.systems,
                &theorem.assumption_set,
                &theorem.by_lemmas,
            ),
            span: theorem.span,
            file: theorem.file.clone(),
        };
    }

    // ── Build scope via the shared theorem helper ( ).
    // The induction passes encode both shows AND invariants, so the
    // scope needs to accommodate both in its quantifier-depth analysis.
    let quantifier_exprs: Vec<&IRExpr> = theorem
        .shows
        .iter()
        .chain(theorem.invariants.iter())
        .collect();
    let (scope, system_names, required_slots) =
        compute_theorem_scope(ir, theorem, &quantifier_exprs, defs);

    if scope.is_empty() {
        return VerificationResult::Unprovable {
            name: theorem.name.clone(),
            hint: crate::messages::VERIFY_EMPTY_SCOPE.to_owned(),
            span: None,
            file: None,
        };
    }

    // Check for entity quantifiers over types not in scope — these would be vacuous.
    for entity_name in required_slots.keys() {
        if !scope.contains_key(entity_name) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!(
                    "theorem quantifies over entity {entity_name} which is not in scope \
                     of systems {:?} — quantifier would be vacuous",
                    theorem.systems
                ),
                span: None,
                file: None,
            };
        }
    }

    let (relevant_entities, relevant_systems) = select_verify_relevant(ir, &scope, &system_names);

    // collect entity and system invariants in
    // scope and merge them into the theorem's invariants list. The
    // existing staged induction machinery treats `theorem.invariants`
    // as both proof obligation (preserved by every event) AND
    // assumption (available when proving the show), which matches the
    // semantics required for entity/system invariants. Per  // entity invariants travel; system invariants stay scoped.
    //
    // collect_in_scope_invariants returns `Always`-wrapped expressions;
    // theorem.invariants are stored without the `Always` wrapper, so
    // we strip it before merging.
    //
    // system invariants must stay scoped to
    // the LITERAL theorem target systems, not the crosscall-expanded
    // set. Build `target_systems` from `theorem.systems` by name and
    // pass it separately from `relevant_entities`.
    let target_system_names: HashSet<String> = theorem.systems.iter().cloned().collect();
    let target_systems: Vec<IRSystem> = ir
        .systems
        .iter()
        .filter(|s| target_system_names.contains(&s.name))
        .cloned()
        .collect();
    let extra_invariants = collect_in_scope_invariants(defs, &relevant_entities, &target_systems);
    let theorem_with_invariants;
    let theorem = if extra_invariants.is_empty() {
        theorem
    } else {
        let mut merged: Vec<IRExpr> = theorem.invariants.clone();
        for inv in extra_invariants {
            // Strip the Always wrapper added by collect_in_scope_invariants;
            // theorem.invariants is treated as state-level facts that
            // the encoder already wraps in Always semantics.
            let stripped = match inv {
                IRExpr::Always { body, .. } => *body,
                other => other,
            };
            merged.push(stripped);
        }
        theorem_with_invariants = IRTheorem {
            name: theorem.name.clone(),
            systems: theorem.systems.clone(),
            assumption_set: theorem.assumption_set.clone(),
            invariants: merged,
            shows: theorem.shows.clone(),
            by_file: theorem.by_file.clone(),
            by_lemmas: theorem.by_lemmas.clone(),
            span: theorem.span,
            file: theorem.file.clone(),
        };
        &theorem_with_invariants
    };

    // Strip `always` wrapper if present — induction proves always by construction.
    // Detect `eventually` which cannot be proved by induction.
    let mut show_exprs: Vec<&IRExpr> = Vec::new();
    for s in &theorem.shows {
        match s {
            IRExpr::Always { body, .. } => show_exprs.push(body.as_ref()),
            _ => show_exprs.push(s),
        }
    }

    // past-time temporal operators
    // (`historically`, `once`, `previously`, `since`) cannot be
    // soundly encoded by 1-induction or IC3 on the unbounded theorem
    // path — those backends instantiate properties at two adjacent
    // symbolic states without explicit history, so the past-time
    // unfolding `historically Q @ step n ≡ ⋀ k ≤ n. Q @ k` collapses
    // to a degenerate fragment of the actual semantics. Reject any
    // theorem whose show or merged invariant contains a past-time
    // operator with a dedicated diagnostic that points the user at
    // BMC, where the encoding is correct.
    //
    // The check runs BEFORE the existing liveness check so
    // `previously`/`since` (which `contains_liveness` also flags as
    // liveness) get the past-time-specific message instead of the
    // generic "liveness reduction failed" hint.
    for (i, show_expr) in show_exprs.iter().enumerate() {
        let compiled = CompiledTemporalFormula::from_expr(show_expr, defs);
        if compiled.contains_past_time() {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!(
                    "{}\n\t{}",
                    crate::messages::THEOREM_PAST_TIME_UNSUPPORTED,
                    crate::messages::HINT_THEOREM_PAST_TIME_UNSUPPORTED
                ),
                span: expr_span(theorem.shows.get(i).unwrap_or(show_expr)),
                file: None,
            };
        }
    }
    for inv_expr in &theorem.invariants {
        let compiled = CompiledTemporalFormula::from_expr(inv_expr, defs);
        if compiled.contains_past_time() {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!(
                    "{}: merged invariant contains a past-time operator\n\t{}",
                    crate::messages::THEOREM_PAST_TIME_UNSUPPORTED,
                    crate::messages::HINT_THEOREM_PAST_TIME_UNSUPPORTED
                ),
                span: expr_span(inv_expr),
                file: None,
            };
        }
    }

    // Check for `eventually` in show expressions.
    // Try liveness-to-safety reduction for liveness properties.
    // Expand through DefEnv first so pred/prop bodies with `eventually` are detected.
    let has_liveness_shows = show_exprs
        .iter()
        .any(|e| CompiledTemporalFormula::from_expr(e, defs).contains_liveness());

    if has_liveness_shows {
        // Build a virtual verify block from the theorem's shows for the
        // reduction. also include
        // `theorem.invariants` (which by this point already contains
        // any entity/system invariants merged in by the
        // collect_in_scope_invariants pass above) wrapped in `Always`,
        // so the liveness reduction's safety pass discharges them.
        // Without this the reduction would silently drop the
        // invariants and report PROVED for a model that violates them.
        let mut virtual_asserts: Vec<IRExpr> = theorem.shows.clone();
        for inv in &theorem.invariants {
            virtual_asserts.push(IRExpr::Always {
                body: Box::new(inv.clone()),
                span: None,
            });
        }
        let virtual_verify = IRVerify {
            name: theorem.name.clone(),
            depth: None,
            systems: theorem
                .systems
                .iter()
                .map(|s| crate::ir::types::IRVerifySystem {
                    name: s.clone(),
                    lo: 0,
                    hi: 10, // not used by reduction
                })
                .collect(),
            stores: vec![],
            // Inherit the theorem's assumption set so the synthetic verify
            // sees the same fairness/stutter context.
            assumption_set: theorem.assumption_set.clone(),
            asserts: virtual_asserts,
            span: theorem.span,
            file: theorem.file.clone(),
        };
        let config = VerifyConfig::default();
        if let Some(result) = try_liveness_reduction(ir, vctx, defs, &virtual_verify, &config) {
            return result;
        }
        // Reduction failed — can't prove liveness by induction
        return VerificationResult::Unprovable {
            name: theorem.name.clone(),
            hint: crate::messages::LIVENESS_REDUCTION_FAILED.to_owned(),
            span: None,
            file: None,
        };
    }

    for (i, show_expr) in show_exprs.iter().enumerate() {
        let compiled = CompiledTemporalFormula::from_expr(show_expr, defs);
        if compiled.contains_liveness() {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: crate::messages::THEOREM_LIVENESS_UNSUPPORTED.to_owned(),
                span: expr_span(theorem.shows.get(i).unwrap_or(show_expr)),
                file: None,
            };
        }
    }

    // Pre-validate: reject unsupported expression forms that would panic during encoding.
    // Expand through DefEnv first — a pred body might contain unsupported forms.
    for (i, show_expr) in show_exprs.iter().enumerate() {
        let expanded = expand_through_defs(show_expr, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!("unsupported expression kind in theorem show: {kind}"),
                span: expr_span(theorem.shows.get(i).unwrap_or(show_expr)),
                file: None,
            };
        }
    }
    for inv_expr in &theorem.invariants {
        let expanded = expand_through_defs(inv_expr, defs);
        if let Some(kind) = find_unsupported_scene_expr(&expanded) {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: format!("unsupported expression kind in theorem invariant: {kind}"),
                span: expr_span(inv_expr),
                file: None,
            };
        }
    }
    // Scan transition guards/updates and event bodies
    for entity in &relevant_entities {
        for trans in &entity.transitions {
            if let Some(kind) = find_unsupported_scene_expr(&trans.guard) {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} guard: {kind}",
                        entity.name, trans.name
                    ),
                    span: None,
                    file: None,
                };
            }
            for upd in &trans.updates {
                if let Some(kind) = find_unsupported_scene_expr(&upd.value) {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!(
                            "unsupported expression in {}.{} update of {}: {kind}",
                            entity.name, trans.name, upd.field
                        ),
                        span: None,
                        file: None,
                    };
                }
            }
        }
    }
    for sys in &relevant_systems {
        for event in &sys.actions {
            if let Some(kind) = find_unsupported_scene_expr(&event.guard) {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event guard: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
            if let Some(kind) = find_unsupported_in_actions(&event.body) {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "unsupported expression in {}.{} event body: {kind}",
                        sys.name, event.name
                    ),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── bounded-only: theorems cannot be proved by BMC ────────────
    if config.bounded_only {
        return VerificationResult::Unprovable {
            name: theorem.name.clone(),
            hint: "--bounded-only was specified — theorems require unbounded proof \
                   (induction or IC3), not bounded model checking"
                .to_owned(),
            span: None,
            file: None,
        };
    }

    // ── Try IC3/PDR (more powerful than 1-induction) ───────────────
    // IC3 discovers strengthening invariants automatically. If it proves
    // the property, we're done. If not, fall through to staged induction
    // which can leverage user-provided invariants.
    if let Some(result) = try_ic3_on_theorem(ir, vctx, defs, theorem, config, _deadline) {
        return result;
    }

    // ── Lemma injection: encode referenced lemma conclusions ────────
    // Lemma conclusions are state-independent (pure, no temporal — checked
    // by check_lemma_block). They hold at every state and are asserted as
    // global facts in each induction pass.
    let mut lemma_bools: Vec<Bool> = Vec::new();
    for lemma_name in &theorem.by_lemmas {
        // Try bare name first, then qualified — DefEnv stores lemmas under
        // bare names, but IR lowering joins qualified paths with "::".
        let bare = lemma_name.rsplit("::").next().unwrap_or(lemma_name);
        let body = defs
            .expand_var(lemma_name)
            .or_else(|| defs.expand_var(bare));
        match body {
            Some(body) => match encode_pure_property_expr(vctx, defs, &body) {
                Ok(b) => lemma_bools.push(b),
                Err(e) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("failed to encode lemma `{lemma_name}`: {e}"),
                        span: theorem.span,
                        file: theorem.file.clone(),
                    };
                }
            },
            None => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: format!(
                        "lemma `{lemma_name}` referenced by `by` was not proved \
                         or not found — cannot inject its conclusion as an assumption"
                    ),
                    span: theorem.span,
                    file: theorem.file.clone(),
                };
            }
        }
    }

    // ── Verify invariants hold at step 0 ──────────────────
    // This prevents false invariants from making the step case vacuously true.
    if !theorem.invariants.is_empty() {
        let pool = create_slot_pool_with_systems(&relevant_entities, &scope, 0, &relevant_systems);
        let Some(timeout_ms) = clamp_timeout_to_deadline(config.induction_timeout_ms, _deadline)
        else {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: verification_timeout_hint(config),
                span: theorem.span,
                file: theorem.file.clone(),
            };
        };
        let solver = AbideSolver::new();
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }

        for c in initial_state_constraints(&pool, &HashMap::new()) {
            solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }
        for lb in &lemma_bools {
            solver.assert(lb);
        }

        // Assert NOT I at step 0 — if UNSAT, invariants hold initially
        let mut negated = Vec::new();
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                inv_expr,
                0,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            negated.push(smt::bool_not(&inv));
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(smt::bool_or(&neg_refs));
        }

        match solver.check() {
            SatResult::Unsat => {} // invariants hold initially
            SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: "invariant does not hold at initial state — \
                           check that invariants are valid for the empty/initial configuration"
                        .to_owned(),
                    span: None,
                    file: None,
                };
            }
            SatResult::Unknown(_) => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_INV_BASE_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── Verify invariants are preserved by transitions ────
    // I(k) ∧ transition(k→k+1) → I(k+1)
    if !theorem.invariants.is_empty() {
        let pool = create_slot_pool_with_systems(&relevant_entities, &scope, 1, &relevant_systems);
        let Some(timeout_ms) = clamp_timeout_to_deadline(config.induction_timeout_ms, _deadline)
        else {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: verification_timeout_hint(config),
                span: theorem.span,
                file: theorem.file.clone(),
            };
        };
        let solver = AbideSolver::new();
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }

        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }
        for lb in &lemma_bools {
            solver.assert(lb);
        }

        // Assume I at step 0
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                inv_expr,
                0,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            solver.assert(&inv);
        }

        // stutter is conditional on the theorem's
        // `assume { stutter }` (on by default for theorems per / revised).
        let trans = transition_constraints(
            &pool,
            vctx,
            &relevant_entities,
            &relevant_systems,
            0,
            &theorem.assumption_set,
        );
        solver.assert(&trans);

        // when stutter is opted out, the
        // transition relation can be unsatisfiable (no events enabled
        // and no stutter to fall back on). Without this guard, the
        // invariant preservation step "holds" vacuously — `I ∧ false
        // → I'` is trivially true — and the theorem would be reported
        // PROVED from a contradictory transition relation. Theorems
        // have no BMC fallback, so we bail out to UNPROVABLE here
        // rather than returning None.
        if !theorem.assumption_set.stutter {
            match solver.check() {
                SatResult::Unsat => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: crate::messages::THEOREM_VACUOUS_UNDER_NO_STUTTER.to_owned(),
                        span: None,
                        file: None,
                    };
                }
                SatResult::Sat | SatResult::Unknown(_) => {}
            }
        }

        // Assert NOT I at step 1
        let mut negated = Vec::new();
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                inv_expr,
                1,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            negated.push(smt::bool_not(&inv));
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(smt::bool_or(&neg_refs));
        }

        match solver.check() {
            SatResult::Unsat => {} // invariants are inductive
            SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: "invariant is not preserved by transitions — \
                           the invariant itself is not inductive"
                        .to_owned(),
                    span: None,
                    file: None,
                };
            }
            SatResult::Unknown(_) => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_INV_STEP_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── Base case — P holds at step 0 ─────────────────────
    {
        let pool = create_slot_pool_with_systems(&relevant_entities, &scope, 0, &relevant_systems);
        let Some(timeout_ms) = clamp_timeout_to_deadline(config.induction_timeout_ms, _deadline)
        else {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: verification_timeout_hint(config),
                span: theorem.span,
                file: theorem.file.clone(),
            };
        };
        let solver = AbideSolver::new();
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }

        for c in initial_state_constraints(&pool, &HashMap::new()) {
            solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }
        for lb in &lemma_bools {
            solver.assert(lb);
        }

        // Assert NOT P at step 0 — if UNSAT, P holds at initial state
        let mut negated = Vec::new();
        for show_expr in &show_exprs {
            let prop = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                show_expr,
                0,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in show expression: {msg}"),
                        span: None,
                        file: None,
                    };
                }
            };
            negated.push(smt::bool_not(&prop));
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(smt::bool_or(&neg_refs));
        }

        match solver.check() {
            SatResult::Unsat => {} // base case holds
            SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_BASE_FAILED.to_owned(),
                    span: None,
                    file: None,
                };
            }
            SatResult::Unknown(_) => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_BASE_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // ── Step case — I(k) ∧ P(k) ∧ transition → P(k+1) ───
    {
        let pool = create_slot_pool_with_systems(&relevant_entities, &scope, 1, &relevant_systems);
        let Some(timeout_ms) = clamp_timeout_to_deadline(config.induction_timeout_ms, _deadline)
        else {
            return VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: verification_timeout_hint(config),
                span: theorem.span,
                file: theorem.file.clone(),
            };
        };
        let solver = AbideSolver::new();
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }

        for c in domain_constraints(&pool, vctx, &relevant_entities) {
            solver.assert(&c);
        }
        for lb in &lemma_bools {
            solver.assert(lb);
        }

        // Assume invariants at step 0
        for inv_expr in &theorem.invariants {
            let inv = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                inv_expr,
                0,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in invariant: {msg}"),
                        span: expr_span(inv_expr),
                        file: None,
                    };
                }
            };
            solver.assert(&inv);
        }

        // Assume P at step 0
        for show_expr in &show_exprs {
            let prop = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                show_expr,
                0,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in show expression: {msg}"),
                        span: None,
                        file: None,
                    };
                }
            };
            solver.assert(&prop);
        }

        // One transition step. stutter is conditional on the
        // theorem's `assume { stutter }`.
        let trans = transition_constraints(
            &pool,
            vctx,
            &relevant_entities,
            &relevant_systems,
            0,
            &theorem.assumption_set,
        );
        solver.assert(&trans);

        // same trace-validity guard as the
        // invariant preservation step above. Under no-stutter, an
        // unsatisfiable transition relation makes `P ∧ false → P'`
        // vacuously true and would otherwise let 1-induction "prove"
        // the theorem from a contradictory transition relation.
        if !theorem.assumption_set.stutter {
            match solver.check() {
                SatResult::Unsat => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: crate::messages::THEOREM_VACUOUS_UNDER_NO_STUTTER.to_owned(),
                        span: None,
                        file: None,
                    };
                }
                SatResult::Sat | SatResult::Unknown(_) => {}
            }
        }

        // Assert NOT P at step 1
        let mut negated = Vec::new();
        for show_expr in &show_exprs {
            let prop = match encode_property_at_step(
                &pool,
                vctx,
                defs,
                show_expr,
                1,
                &HashMap::new(),
                &relevant_systems,
            ) {
                Ok(p) => p,
                Err(msg) => {
                    return VerificationResult::Unprovable {
                        name: theorem.name.clone(),
                        hint: format!("encoding error in show expression: {msg}"),
                        span: None,
                        file: None,
                    };
                }
            };
            negated.push(smt::bool_not(&prop));
        }
        let neg_refs: Vec<&Bool> = negated.iter().collect();
        if !neg_refs.is_empty() {
            solver.assert(smt::bool_or(&neg_refs));
        }

        match solver.check() {
            SatResult::Unsat => {} // step case holds
            SatResult::Sat => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: "inductive step failed — property is not preserved by transitions"
                        .to_owned(),
                    span: None,
                    file: None,
                };
            }
            SatResult::Unknown(_) => {
                return VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: crate::messages::THEOREM_STEP_UNKNOWN.to_owned(),
                    span: None,
                    file: None,
                };
            }
        }
    }

    // Both base and step passed
    let elapsed = elapsed_ms(&start);

    // Report the method with scope details for inter-entity properties.
    let max_scope = scope.values().copied().max().unwrap_or(2);
    let method = if has_multi_entity_quantifier(&show_exprs) {
        format!("1-induction (scope: {max_scope} slots per entity type)")
    } else {
        "1-induction".to_owned()
    };

    VerificationResult::Proved {
        name: theorem.name.clone(),
        method,
        time_ms: elapsed,
        assumptions: super::build_assumptions_for_system_scope(
            ir,
            &theorem.systems,
            &theorem.assumption_set,
            &theorem.by_lemmas,
        ),
        span: None,
        file: None,
    }
}

/// Try to prove a theorem's show expressions using IC3/PDR.
///
/// IC3 discovers strengthening invariants automatically, so user-provided
/// invariants are not needed. This is tried before staged induction (since
/// IC3 is strictly more powerful for properties that need invariant discovery).
fn try_ic3_on_theorem(
    ir: &IRProgram,
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    theorem: &IRTheorem,
    config: &VerifyConfig,
    deadline: Option<Instant>,
) -> Option<VerificationResult> {
    if config.no_ic3 {
        return None;
    }

    let start = Instant::now();

    let Some(safety) =
        super::transition::TransitionSafetySpec::for_theorem(ir, vctx, theorem, defs)
    else {
        return None;
    };
    let system = safety.system();

    // trace-validity guard for the IC3 path.
    // When the theorem opts out of stutter and the transition relation
    // is unsatisfiable from the initial state (no events enabled, no
    // stutter to fall back on), IC3's CHC encoding has the same
    // vacuity hole as 1-induction: `forall states. trans → P'` is
    // trivially valid when `trans` is `false`, so IC3 reports PROVED
    // from a contradictory transition relation. Bail to UNPROVABLE
    // here (mirroring the induction-side fix in `check_theorem_block`).
    if !theorem.assumption_set.stutter {
        let pool = create_slot_pool_with_systems(
            system.relevant_entities(),
            system.slots_per_entity(),
            1,
            system.relevant_systems(),
        );
        let probe_solver = AbideSolver::new();
        if let Some(timeout_ms) = clamp_timeout_to_deadline(config.ic3_timeout_ms, deadline) {
            if timeout_ms > 0 {
                probe_solver.set_timeout(timeout_ms);
            }
        } else {
            return Some(VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: verification_timeout_hint(config),
                span: theorem.span,
                file: theorem.file.clone(),
            });
        }
        for c in initial_state_constraints(&pool, &HashMap::new()) {
            probe_solver.assert(&c);
        }
        for c in domain_constraints(&pool, vctx, system.relevant_entities()) {
            probe_solver.assert(&c);
        }
        let trans = transition_constraints(
            &pool,
            vctx,
            system.relevant_entities(),
            system.relevant_systems(),
            0,
            &theorem.assumption_set,
        );
        probe_solver.assert(&trans);

        if matches!(probe_solver.check(), SatResult::Unsat) {
            return Some(VerificationResult::Unprovable {
                name: theorem.name.clone(),
                hint: crate::messages::THEOREM_VACUOUS_UNDER_NO_STUTTER.to_owned(),
                span: None,
                file: None,
            });
        }
    }

    if config.progress {
        eprint!(" (trying IC3/PDR)");
    }

    // Try IC3 on each show expression
    for (property_index, _) in safety.step_properties().iter().enumerate() {
        let timeout_ms = match clamp_timeout_to_deadline(config.ic3_timeout_ms, deadline) {
            Some(timeout_ms) => timeout_ms,
            None => {
                return Some(VerificationResult::Unprovable {
                    name: theorem.name.clone(),
                    hint: verification_timeout_hint(config),
                    span: theorem.span,
                    file: theorem.file.clone(),
                })
            }
        };
        let result = super::transition::solve_transition_obligation(
            safety.obligation(property_index, timeout_ms),
        );
        match result {
            super::transition::TransitionResult::Proved => {}
            super::transition::TransitionResult::Violated(trace) if !trace.is_empty() => {
                // Theorems have no BMC fallback, so IC3's trace is the best
                // counterexample available. The trace is extracted from the
                // CHC derivation tree, which may reflect the ForAll per-slot
                // over-approximation (see encode_step_chc doc). For confirmed
                // traces, users should write a verify block with BMC depth.
                // IC3 path does not inject by_lemmas into the CHC encoding,
                // so do not claim them as assumptions in the result.
                let evidence = ic3_trace_to_operational_witness(
                    &trace,
                    system.relevant_entities(),
                    system.relevant_systems(),
                    &vctx.variants,
                )
                .map(|w| {
                    WitnessEnvelope::operational(w)
                        .map_err(|err| {
                            format!("IC3 operational witness envelope validation failed: {err}")
                        })
                        .and_then(|witness| {
                            EvidenceEnvelope::witness(witness).map_err(|err| {
                                format!("IC3 witness evidence validation failed: {err}")
                            })
                        })
                });
                let (evidence, evidence_extraction_error) = match evidence {
                    Ok(Ok(evidence)) => (Some(evidence), None),
                    Ok(Err(err)) => (None, Some(err)),
                    Err(err) => (None, Some(err)),
                };
                return Some(VerificationResult::Counterexample {
                    name: theorem.name.clone(),
                    evidence,
                    evidence_extraction_error,
                    assumptions: super::build_assumptions_for_system_scope(
                        ir,
                        &theorem.systems,
                        &theorem.assumption_set,
                        &[],
                    ),
                    span: None,
                    file: None,
                });
            }
            super::transition::TransitionResult::Violated(_)
            | super::transition::TransitionResult::Unknown(_) => return None,
        }
    }

    let elapsed = elapsed_ms(&start);
    // IC3 path does not inject by_lemmas into the CHC encoding,
    // so do not claim them as assumptions in the result.
    Some(VerificationResult::Proved {
        name: theorem.name.clone(),
        method: "IC3/PDR".to_owned(),
        time_ms: elapsed,
        assumptions: super::build_assumptions_for_system_scope(
            ir,
            &theorem.systems,
            &theorem.assumption_set,
            &[],
        ),
        span: None,
        file: None,
    })
}

/// Verify a lemma block.
///
/// Lemmas are system-independent properties: each body expression must be a
/// tautology (universally true). We encode the conjunction of all body
/// expressions via the pure expression encoder, negate it, and check UNSAT.
pub(super) fn check_lemma_block(
    vctx: &VerifyContext,
    defs: &defenv::DefEnv,
    lemma: &crate::ir::types::IRLemma,
    config: &VerifyConfig,
) -> VerificationResult {
    let start = Instant::now();

    if lemma.body.is_empty() {
        let elapsed = elapsed_ms(&start);
        return VerificationResult::Proved {
            name: lemma.name.clone(),
            method: "lemma (empty body)".to_owned(),
            time_ms: elapsed,
            assumptions: super::build_assumptions(&lemma.assumption_set, &[]),
            span: lemma.span,
            file: lemma.file.clone(),
        };
    }

    // detect temporal operators in the
    // lemma body BEFORE theorem/property encoding. The
    // property encoder rejects temporal operators here because lemmas
    // are state-independent tautologies, so surface a
    // lemma-specific diagnostic that points the user at `verify`
    // (BMC) or `theorem` (induction/IC3) instead.
    //
    // Past-time operators get the same treatment via this single
    // check — they have the same fundamental limitation in lemmas
    // (no trace state in the encoder), so a single message covers
    // both cases without conflating them with the theorem-path
    // past-time message (which is about induction unsoundness, not
    // pure-expression encoding).
    for body_expr in &lemma.body {
        let expanded = expand_through_defs(body_expr, defs);
        if contains_temporal(&expanded) {
            return VerificationResult::Unprovable {
                name: lemma.name.clone(),
                hint: format!(
                    "{}\n\t{}",
                    crate::messages::LEMMA_TEMPORAL_UNSUPPORTED,
                    crate::messages::HINT_LEMMA_TEMPORAL_UNSUPPORTED
                ),
                span: lemma.span,
                file: lemma.file.clone(),
            };
        }
    }

    // Encode each body expression and conjoin
    let mut conjuncts = Vec::new();
    for body_expr in &lemma.body {
        let expanded = expand_through_defs(body_expr, defs);
        match encode_pure_property_expr(vctx, defs, &expanded) {
            Ok(b) => conjuncts.push(b),
            Err(e) => {
                return VerificationResult::Unprovable {
                    name: lemma.name.clone(),
                    hint: format!("lemma body encoding error: {e}"),
                    span: lemma.span,
                    file: lemma.file.clone(),
                };
            }
        }
    }

    let refs: Vec<&Bool> = conjuncts.iter().collect();
    let lemma_body = smt::bool_and(&refs);

    // Negate and check: if UNSAT, the lemma is a tautology
    let solver = AbideSolver::new();
    if let Some(timeout_ms) = clamp_timeout_to_deadline(config.induction_timeout_ms, None) {
        if timeout_ms > 0 {
            solver.set_timeout(timeout_ms);
        }
    }
    assert_lambda_axioms_on(&solver);
    solver.assert(smt::bool_not(&lemma_body));

    let elapsed = elapsed_ms(&start);
    match solver.check() {
        SatResult::Unsat => VerificationResult::Proved {
            name: lemma.name.clone(),
            method: "lemma".to_owned(),
            time_ms: elapsed,
            assumptions: super::build_assumptions(&lemma.assumption_set, &[]),
            span: lemma.span,
            file: lemma.file.clone(),
        },
        SatResult::Sat => {
            let (evidence, evidence_extraction_error) = match super::countermodel_evidence(
                Countermodel::new()
                    .backend("z3")
                    .summary("satisfying model for negated lemma body"),
            ) {
                Ok(evidence) => (Some(evidence), None),
                Err(err) => (None, Some(err)),
            };
            VerificationResult::Counterexample {
                name: lemma.name.clone(),
                evidence,
                evidence_extraction_error,
                assumptions: super::build_assumptions(&lemma.assumption_set, &[]),
                span: lemma.span,
                file: lemma.file.clone(),
            }
        }
        SatResult::Unknown(_) => VerificationResult::Unprovable {
            name: lemma.name.clone(),
            hint: "Z3 returned unknown for lemma".to_owned(),
            span: lemma.span,
            file: lemma.file.clone(),
        },
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::types::{
        IRAggKind, IRAssumptionSet, IRAxiom, IREntity, IRExpr, IRLemma, IRMatchArm, IRPattern,
        IRProgram, IRScene, IRSystem, IRTheorem, IRType, IRVerify, LetBinding, LitVal,
    };

    use super::{
        check_lemma_block, check_theorem_block, encode_pure_property_expr, needs_property_encoder,
    };
    use crate::verify::context::VerifyContext;
    use crate::verify::defenv::DefEnv;
    use crate::verify::{VerificationResult, VerifyConfig};

    fn bool_lit(value: bool) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Bool,
            value: LitVal::Bool { value },
            span: None,
        }
    }

    fn int_lit(value: i64) -> IRExpr {
        IRExpr::Lit {
            ty: IRType::Int,
            value: LitVal::Int { value },
            span: None,
        }
    }

    fn var(name: &str, ty: IRType) -> IRExpr {
        IRExpr::Var {
            name: name.to_owned(),
            ty,
            span: None,
        }
    }

    fn empty_ir() -> IRProgram {
        IRProgram {
            types: vec![],
            constants: vec![],
            functions: vec![],
            entities: vec![],
            systems: vec![],
            verifies: Vec::<IRVerify>::new(),
            theorems: Vec::<IRTheorem>::new(),
            axioms: Vec::<IRAxiom>::new(),
            lemmas: Vec::<IRLemma>::new(),
            scenes: Vec::<IRScene>::new(),
        }
    }

    fn ir_with_system_entity() -> IRProgram {
        IRProgram {
            entities: vec![IREntity {
                name: "Task".to_owned(),
                fields: vec![],
                transitions: vec![],
                derived_fields: vec![],
                invariants: vec![],
                fsm_decls: vec![],
            }],
            systems: vec![IRSystem {
                name: "Workflow".to_owned(),
                store_params: vec![],
                fields: vec![],
                entities: vec!["Task".to_owned()],
                commands: vec![],
                actions: vec![],
                fsm_decls: vec![],
                derived_fields: vec![],
                invariants: vec![],
                queries: vec![],
                preds: vec![],
                let_bindings: vec![],
                procs: vec![],
            }],
            ..empty_ir()
        }
    }

    fn lemma(name: &str, body: Vec<IRExpr>) -> IRLemma {
        IRLemma {
            name: name.to_owned(),
            assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
            body,
            span: None,
            file: None,
        }
    }

    fn theorem(name: &str, shows: Vec<IRExpr>, by_file: Option<&str>) -> IRTheorem {
        IRTheorem {
            name: name.to_owned(),
            systems: vec![],
            assumption_set: IRAssumptionSet::default_for_theorem_or_lemma(),
            invariants: vec![],
            shows,
            by_file: by_file.map(str::to_owned),
            by_lemmas: vec![],
            span: None,
            file: None,
        }
    }

    fn scoped_theorem(name: &str, shows: Vec<IRExpr>) -> IRTheorem {
        IRTheorem {
            systems: vec!["Workflow".to_owned()],
            ..theorem(name, shows, None)
        }
    }

    fn assert_needs(expr: IRExpr) {
        assert!(needs_property_encoder(&expr), "expected property encoder");
    }

    fn assert_pure(expr: IRExpr) {
        assert!(
            !needs_property_encoder(&expr),
            "expected pure expression encoder"
        );
    }

    #[test]
    fn needs_property_encoder_distinguishes_direct_property_only_forms() {
        assert_pure(bool_lit(true));
        assert_pure(var("x", IRType::Bool));
        assert_pure(IRExpr::Sorry { span: None });
        assert_pure(IRExpr::Todo { span: None });
        assert_pure(IRExpr::Prime {
            expr: Box::new(var("x", IRType::Bool)),
            span: None,
        });

        assert_needs(IRExpr::Choose {
            var: "x".to_owned(),
            domain: IRType::Int,
            predicate: Some(Box::new(bool_lit(true))),
            ty: IRType::Int,
            span: None,
        });
        assert_needs(IRExpr::Assert {
            expr: Box::new(bool_lit(true)),
            span: None,
        });
        assert_needs(IRExpr::Assume {
            expr: Box::new(bool_lit(true)),
            span: None,
        });
    }

    #[test]
    fn needs_property_encoder_walks_recursive_expression_shapes() {
        let choose = IRExpr::Choose {
            var: "x".to_owned(),
            domain: IRType::Int,
            predicate: None,
            ty: IRType::Int,
            span: None,
        };

        assert_needs(IRExpr::Lam {
            param: "x".to_owned(),
            param_type: IRType::Int,
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Always {
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Eventually {
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Historically {
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Once {
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Previously {
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Card {
            expr: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::UnOp {
            op: "!".to_owned(),
            operand: Box::new(choose.clone()),
            ty: IRType::Bool,
            span: None,
        });
        assert_needs(IRExpr::Let {
            bindings: vec![LetBinding {
                name: "w".to_owned(),
                ty: IRType::Int,
                expr: choose.clone(),
            }],
            body: Box::new(bool_lit(true)),
            span: None,
        });
        assert_needs(IRExpr::VarDecl {
            name: "w".to_owned(),
            ty: IRType::Int,
            init: Box::new(int_lit(0)),
            rest: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::IfElse {
            cond: Box::new(bool_lit(true)),
            then_body: Box::new(bool_lit(true)),
            else_body: Some(Box::new(choose.clone())),
            span: None,
        });
        assert_needs(IRExpr::BinOp {
            op: "&&".to_owned(),
            left: Box::new(bool_lit(true)),
            right: Box::new(choose.clone()),
            ty: IRType::Bool,
            span: None,
        });
        assert_needs(IRExpr::Until {
            left: Box::new(bool_lit(true)),
            right: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Since {
            left: Box::new(bool_lit(true)),
            right: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::App {
            func: Box::new(var("f", IRType::Bool)),
            arg: Box::new(choose.clone()),
            ty: IRType::Bool,
            span: None,
        });
    }

    #[test]
    fn needs_property_encoder_walks_collection_match_and_imperative_shapes() {
        let choose = IRExpr::Choose {
            var: "x".to_owned(),
            domain: IRType::Int,
            predicate: None,
            ty: IRType::Int,
            span: None,
        };

        assert_needs(IRExpr::Forall {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Exists {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::One {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Lone {
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(choose.clone()),
            span: None,
        });
        assert_needs(IRExpr::Aggregate {
            kind: IRAggKind::Sum,
            var: "x".to_owned(),
            domain: IRType::Int,
            body: Box::new(int_lit(1)),
            in_filter: Some(Box::new(choose.clone())),
            span: None,
        });
        assert_needs(IRExpr::Field {
            expr: Box::new(choose.clone()),
            field: "status".to_owned(),
            ty: IRType::Bool,
            span: None,
        });
        assert_needs(IRExpr::SetLit {
            elements: vec![choose.clone()],
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        });
        assert_needs(IRExpr::SeqLit {
            elements: vec![choose.clone()],
            ty: IRType::Seq {
                element: Box::new(IRType::Int),
            },
            span: None,
        });
        assert_needs(IRExpr::MapLit {
            entries: vec![(int_lit(0), choose.clone())],
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Int),
            },
            span: None,
        });
        assert_needs(IRExpr::MapUpdate {
            map: Box::new(var(
                "m",
                IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
            )),
            key: Box::new(int_lit(0)),
            value: Box::new(choose.clone()),
            ty: IRType::Map {
                key: Box::new(IRType::Int),
                value: Box::new(IRType::Int),
            },
            span: None,
        });
        assert_needs(IRExpr::Index {
            map: Box::new(var(
                "m",
                IRType::Map {
                    key: Box::new(IRType::Int),
                    value: Box::new(IRType::Int),
                },
            )),
            key: Box::new(choose.clone()),
            ty: IRType::Int,
            span: None,
        });
        assert_needs(IRExpr::Match {
            scrutinee: Box::new(var("flag", IRType::Bool)),
            arms: vec![IRMatchArm {
                pattern: IRPattern::PWild,
                guard: Some(choose.clone()),
                body: bool_lit(true),
            }],
            span: None,
        });
        assert_needs(IRExpr::Block {
            exprs: vec![bool_lit(true), choose.clone()],
            span: None,
        });
        assert_needs(IRExpr::While {
            cond: Box::new(bool_lit(true)),
            invariants: vec![choose.clone()],
            decreases: None,
            body: Box::new(bool_lit(true)),
            span: None,
        });
    }

    #[test]
    fn needs_property_encoder_walks_constructor_saw_and_comprehension_shapes() {
        let choose = IRExpr::Choose {
            var: "x".to_owned(),
            domain: IRType::Int,
            predicate: None,
            ty: IRType::Int,
            span: None,
        };

        assert_needs(IRExpr::Ctor {
            enum_name: "Result".to_owned(),
            ctor: "Ok".to_owned(),
            args: vec![("value".to_owned(), choose.clone())],
            span: None,
        });
        assert_needs(IRExpr::Saw {
            system_name: "Orders".to_owned(),
            event_name: "submit".to_owned(),
            args: vec![None, Some(Box::new(choose.clone()))],
            span: None,
        });
        assert_needs(IRExpr::SetComp {
            var: "x".to_owned(),
            domain: IRType::Int,
            filter: Box::new(bool_lit(true)),
            projection: Some(Box::new(choose)),
            ty: IRType::Set {
                element: Box::new(IRType::Int),
            },
            span: None,
        });
    }

    #[test]
    fn encode_pure_property_expr_uses_pure_and_property_encoder_paths() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = DefEnv::from_ir(&ir);

        let pure = encode_pure_property_expr(&vctx, &defs, &bool_lit(true))
            .expect("pure bool should encode");
        assert_eq!(pure.as_bool(), Some(true));

        encode_pure_property_expr(
            &vctx,
            &defs,
            &IRExpr::Forall {
                var: "x".to_owned(),
                domain: IRType::Bool,
                body: Box::new(var("x", IRType::Bool)),
                span: None,
            },
        )
        .expect("finite property quantifier should encode");
    }

    #[test]
    fn check_lemma_block_covers_empty_true_false_and_encoding_error_results() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let empty = check_lemma_block(&vctx, &defs, &lemma("empty", vec![]), &config);
        assert!(
            matches!(empty, VerificationResult::Proved { method, .. } if method == "lemma (empty body)")
        );

        let tautology =
            check_lemma_block(&vctx, &defs, &lemma("truth", vec![bool_lit(true)]), &config);
        assert!(
            matches!(tautology, VerificationResult::Proved { method, .. } if method == "lemma")
        );

        let counterexample = check_lemma_block(
            &vctx,
            &defs,
            &lemma("falsehood", vec![bool_lit(false)]),
            &config,
        );
        assert!(matches!(
            counterexample,
            VerificationResult::Counterexample { name, .. } if name == "falsehood"
        ));

        let encoding_error = check_lemma_block(
            &vctx,
            &defs,
            &lemma("unbound", vec![var("missing", IRType::Bool)]),
            &config,
        );
        assert!(matches!(
            encoding_error,
            VerificationResult::Unprovable { name, .. } if name == "unbound"
        ));
    }

    #[test]
    fn check_lemma_block_rejects_temporal_body_with_specific_hint() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let result = check_lemma_block(
            &vctx,
            &defs,
            &lemma(
                "temporal",
                vec![IRExpr::Always {
                    body: Box::new(bool_lit(true)),
                    span: None,
                }],
            ),
            &config,
        );
        assert!(matches!(
            result,
            VerificationResult::Unprovable { hint, .. }
                if hint.contains(crate::messages::LEMMA_TEMPORAL_UNSUPPORTED)
        ));
    }

    #[test]
    fn check_theorem_block_covers_by_file_admission_and_empty_scope_failure() {
        let ir = empty_ir();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let admitted = check_theorem_block(
            &ir,
            &vctx,
            &defs,
            &theorem(
                "external",
                vec![bool_lit(true)],
                Some("proofs/external.agda"),
            ),
            &config,
            None,
        );
        assert!(matches!(
            admitted,
            VerificationResult::Admitted { name, reason, evidence: Some(_), .. }
                if name == "external" && reason.contains("external proof artifact reference")
        ));

        let empty_scope = check_theorem_block(
            &ir,
            &vctx,
            &defs,
            &theorem("empty_scope", vec![bool_lit(true)], None),
            &config,
            None,
        );
        assert!(matches!(
            empty_scope,
            VerificationResult::Unprovable { name, hint, .. }
                if name == "empty_scope" && hint == crate::messages::VERIFY_EMPTY_SCOPE
        ));
    }

    #[test]
    fn check_theorem_block_covers_nonempty_scope_diagnostics_before_solver_paths() {
        let ir = ir_with_system_entity();
        let vctx = VerifyContext::from_ir(&ir);
        let defs = DefEnv::from_ir(&ir);
        let config = VerifyConfig::default();

        let past_time = check_theorem_block(
            &ir,
            &vctx,
            &defs,
            &scoped_theorem(
                "past_time",
                vec![IRExpr::Previously {
                    body: Box::new(bool_lit(true)),
                    span: None,
                }],
            ),
            &config,
            None,
        );
        assert!(matches!(
            past_time,
            VerificationResult::Unprovable { hint, .. }
                if hint.contains(crate::messages::THEOREM_PAST_TIME_UNSUPPORTED)
        ));

        let unsupported = check_theorem_block(
            &ir,
            &vctx,
            &defs,
            &scoped_theorem(
                "unsupported",
                vec![IRExpr::Block {
                    exprs: vec![bool_lit(true)],
                    span: None,
                }],
            ),
            &config,
            None,
        );
        assert!(matches!(
            unsupported,
            VerificationResult::Unprovable { hint, .. }
                if hint.contains("unsupported expression kind in theorem show: Block")
        ));

        let mut bounded_only_config = VerifyConfig::default();
        bounded_only_config.bounded_only = true;
        let bounded_only = check_theorem_block(
            &ir,
            &vctx,
            &defs,
            &scoped_theorem("bounded_only", vec![bool_lit(true)]),
            &bounded_only_config,
            None,
        );
        assert!(matches!(
            bounded_only,
            VerificationResult::Unprovable { hint, .. } if hint.contains("--bounded-only")
        ));
    }
}
