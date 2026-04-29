//! Assumption set population and lemma subset containment checking.

use super::super::env::Env;
use super::super::error::{ElabError, ErrorKind};
use std::collections::HashMap;

// ── Assumption set population () ──────────────────────────────

/// Walk every verify/theorem/lemma's parsed `assume_block` and populate
/// its `assumption_set` with normalized fairness/stutter data per Item
/// 51. Runs after all systems are collected so event paths can be
/// resolved.
///
/// Resolution rules:
/// * `Sys::event` (2-segment path) is looked up in `env.systems[Sys]`.
///   The event must be present in that system.
/// * `event` (1-segment path) is searched across the verification
///   site's target systems. Resolved if exactly one match; rejected
///   as ambiguous on multiple matches; rejected as unknown on zero.
/// * Unknown event paths emit `UNKNOWN_FAIR_EVENT` (or
///   `AMBIGUOUS_FAIR_EVENT`) and the item is dropped from the set.
///
/// Construct defaults are already installed by `collect`; this pass
/// only flips `stutter` when the assume block contains an explicit
/// `Stutter` or `NoStutter` item.
pub(super) fn resolve_assumption_sets(env: &mut Env) {
    // Snapshot the system → executable action index. The inner map is action-name →
    // `is_parameterized`. The flag is used to populate `per_tuple` per
    // parameterized fair actions default to per-tuple fairness.
    let system_events: HashMap<String, HashMap<String, bool>> = env
        .systems
        .iter()
        .map(|(sys_name, sys)| {
            let actions: HashMap<String, bool> = sys
                .actions
                .iter()
                .map(|c| (c.name.clone(), !c.params.is_empty()))
                .collect();
            (sys_name.clone(), actions)
        })
        .collect();

    // Lemma fallback scope, computed once outside the mutable lemma
    // iteration. Lemmas have no `for SystemList` header, so they
    // resolve unqualified event names against ALL systems.
    let lemma_default_scope: Vec<String> = env.systems.keys().cloned().collect();

    // Collect all errors first, then push to env at the end (avoids
    // double mutable borrow on env).
    let mut new_errors: Vec<ElabError> = Vec::new();

    // resolve every `under { }` block exactly
    // once with its shared scope. The result is the canonical
    // `resolved_set` that every member theorem/lemma inherits as its
    // floor. Resolving once (instead of re-resolving the raw items
    // per member) is what makes `under` a real shared environment:
    // siblings cannot diverge on what an unqualified `fair tick`
    // means, and downstream checks can compare canonical
    // `EventRef`s instead of fragile path strings.
    // Empty let-bindings map for under blocks (they don't have let bindings).
    let empty_let_bindings: HashMap<String, String> = HashMap::new();

    for ub in &mut env.under_blocks {
        // Empty shared scope (under contains only lemmas) falls back
        // to the full system list, the same scope a standalone lemma
        // would use.
        let effective_scope: &[String] = if ub.scope.is_empty() {
            &lemma_default_scope
        } else {
            &ub.scope
        };
        populate_assumption_set_from_items(
            &mut ub.resolved_set,
            &ub.items,
            effective_scope,
            &system_events,
            &empty_let_bindings,
            &mut new_errors,
        );
    }
    // Snapshot the canonical resolved sets so we can index them while
    // iterating env.theorems / env.lemmas with mutable borrows.
    let under_resolved: Vec<crate::elab::types::AssumptionSet> = env
        .under_blocks
        .iter()
        .map(|ub| ub.resolved_set.clone())
        .collect();

    for verify in &mut env.verifies {
        // derive scope from let bindings.
        let scope: Vec<String> = verify
            .let_bindings
            .iter()
            .map(|lb| lb.system_type.clone())
            .collect();
        // Build instance-name → system-type map for dot-path resolution.
        let lb_map: HashMap<String, String> = verify
            .let_bindings
            .iter()
            .map(|lb| (lb.name.clone(), lb.system_type.clone()))
            .collect();
        populate_assumption_set(
            &mut verify.assumption_set,
            verify.assume_block.as_ref(),
            &scope,
            &system_events,
            &lb_map,
            &mut new_errors,
        );
    }
    for theorem in &mut env.theorems {
        let scope: Vec<String> = theorem.targets.clone();
        if let Some(idx) = theorem.enclosing_under_idx {
            // floor = the canonical resolved set
            // from the shared `EUnderBlock`. We DO NOT re-resolve the
            // under's raw items here.
            theorem.assumption_set = under_resolved[idx].clone();

            // Build the inner per-construct assume_block as a delta of
            // RESOLVED items, then run the add-only check against
            // the under's resolved set. The check uses canonical
            // `EventRef`s, so alias / qualification differences (e.g.
            // outer `strong fair S::tick` and inner `fair tick` for
            // `for S`) are correctly recognized as the same event.
            if let Some(inner) = theorem.assume_block.as_ref() {
                let mut delta = build_assume_delta(inner, &scope, &system_events, &mut new_errors);
                // review fix: normalize the delta within itself
                // before checking, so an inner `fair X; strong fair X`
                // is recognized as effectively just `strong fair X` and
                // not flagged as a downgrade against an outer `strong fair X`.
                delta.normalize();
                check_under_add_only_resolved(&under_resolved[idx], &delta, &mut new_errors);
                merge_delta_into(&delta, &mut theorem.assumption_set);
                theorem.assumption_set.normalize();
            }
        } else {
            populate_assumption_set(
                &mut theorem.assumption_set,
                theorem.assume_block.as_ref(),
                &scope,
                &system_events,
                &empty_let_bindings,
                &mut new_errors,
            );
        }
    }
    for lemma in &mut env.lemmas {
        let scope: Vec<String> = lemma_default_scope.clone();
        if let Some(idx) = lemma.enclosing_under_idx {
            lemma.assumption_set = under_resolved[idx].clone();
            if let Some(inner) = lemma.assume_block.as_ref() {
                let mut delta = build_assume_delta(inner, &scope, &system_events, &mut new_errors);
                delta.normalize();
                check_under_add_only_resolved(&under_resolved[idx], &delta, &mut new_errors);
                merge_delta_into(&delta, &mut lemma.assumption_set);
                lemma.assumption_set.normalize();
            }
        } else {
            populate_assumption_set(
                &mut lemma.assumption_set,
                lemma.assume_block.as_ref(),
                &scope,
                &system_events,
                &empty_let_bindings,
                &mut new_errors,
            );
        }
    }

    for err in new_errors {
        env.errors.push(err);
    }
}

/// a normalized "delta" view of an `assume { }`
/// block — its items resolved into canonical `EventRef`s, with the
/// stutter explicit-flag preserved. Used for the add-only check
/// (`check_under_add_only_resolved`) and for merging the inner items
/// into a member's effective assumption set.
pub(super) struct AssumeDelta {
    /// `Some(true)` if the block contains `stutter`, `Some(false)` if
    /// it contains `no stutter`, `None` if neither was specified.
    /// Spans point at the originating item for diagnostics.
    explicit_stutter: Option<(bool, crate::span::Span)>,
    /// Resolved weak-fair events with their item spans.
    weak_fair: Vec<(crate::elab::types::EventRef, crate::span::Span)>,
    /// Resolved strong-fair events with their item spans.
    strong_fair: Vec<(crate::elab::types::EventRef, crate::span::Span)>,
    /// Subset of `weak_fair ∪ strong_fair` whose events are
    /// parameterized. See `AssumptionSet::per_tuple`.
    per_tuple: std::collections::BTreeSet<crate::elab::types::EventRef>,
}

impl AssumeDelta {
    /// Apply the AssumptionSet normalization rule () within
    /// this delta only: if an event appears in both `weak_fair` and
    /// `strong_fair`, drop the weak entry. Strong fairness implies
    /// weak fairness, so the delta's effective contribution for that
    /// event is "strong" — the user redundantly listed both.
    ///
    /// **Run BEFORE the add-only check.** Without this normalization
    /// step, an inner `assume { fair X; strong fair X }` inside an
    /// `under { strong fair X... }` would be wrongly flagged as a
    /// downgrade attempt — the raw `weak_fair` bucket would still
    /// contain `X`, even though the delta's effective contribution is
    /// just `strong fair X`, which is identical to the outer.
    fn normalize(&mut self) {
        let strong_evs: std::collections::BTreeSet<crate::elab::types::EventRef> =
            self.strong_fair.iter().map(|(e, _)| e.clone()).collect();
        self.weak_fair.retain(|(e, _)| !strong_evs.contains(e));
    }
}

/// Resolve every item in an `AssumeBlock` into canonical `EventRef`s
/// and return the resulting `AssumeDelta`. Emits diagnostics for
/// unknown / ambiguous event paths via `populate_assumption_set`'s
/// helpers, and silently drops items that fail to resolve.
pub(super) fn build_assume_delta(
    block: &crate::ast::AssumeBlock,
    scope: &[String],
    system_events: &HashMap<String, HashMap<String, bool>>,
    errors: &mut Vec<ElabError>,
) -> AssumeDelta {
    let empty_lb: HashMap<String, String> = HashMap::new();
    build_assume_delta_with_bindings(block, scope, system_events, &empty_lb, errors)
}

pub(super) fn build_assume_delta_with_bindings(
    block: &crate::ast::AssumeBlock,
    scope: &[String],
    system_events: &HashMap<String, HashMap<String, bool>>,
    let_bindings: &HashMap<String, String>,
    errors: &mut Vec<ElabError>,
) -> AssumeDelta {
    use crate::ast::AssumeItem;
    let mut delta = AssumeDelta {
        explicit_stutter: None,
        weak_fair: Vec::new(),
        strong_fair: Vec::new(),
        per_tuple: std::collections::BTreeSet::new(),
    };
    for item in &block.items {
        match item {
            AssumeItem::Stutter { span } => {
                delta.explicit_stutter = Some((true, *span));
            }
            AssumeItem::NoStutter { span } => {
                delta.explicit_stutter = Some((false, *span));
            }
            AssumeItem::Fair { path, span } => {
                if let Some((ev_ref, is_param)) = super::resolve_event_path(
                    path,
                    scope,
                    system_events,
                    let_bindings,
                    errors,
                    *span,
                ) {
                    if is_param {
                        delta.per_tuple.insert(ev_ref.clone());
                    }
                    delta.weak_fair.push((ev_ref, *span));
                }
            }
            AssumeItem::StrongFair { path, span } => {
                if let Some((ev_ref, is_param)) = super::resolve_event_path(
                    path,
                    scope,
                    system_events,
                    let_bindings,
                    errors,
                    *span,
                ) {
                    if is_param {
                        delta.per_tuple.insert(ev_ref.clone());
                    }
                    delta.strong_fair.push((ev_ref, *span));
                }
            }
            // Store, Let, and Proc items are handled during
            // collection, not during assumption set resolution.
            AssumeItem::Store(_) | AssumeItem::Let(_) | AssumeItem::Proc(_) => {}
        }
    }
    delta
}

/// Merge an `AssumeDelta` into an existing `AssumptionSet` (e.g. the
/// floor inherited from an enclosing `under` block). Stutter is
/// overwritten when the delta has an explicit value; fair events are
/// unioned. The caller is expected to call `set.normalize()` after
/// merging.
pub(super) fn merge_delta_into(delta: &AssumeDelta, set: &mut crate::elab::types::AssumptionSet) {
    if let Some((stut, _)) = delta.explicit_stutter {
        set.stutter = stut;
    }
    for (ev, _) in &delta.weak_fair {
        set.weak_fair.insert(ev.clone());
    }
    for (ev, _) in &delta.strong_fair {
        set.strong_fair.insert(ev.clone());
    }
    for ev in &delta.per_tuple {
        set.per_tuple.insert(ev.clone());
    }
}

/// enforce add-only inheritance between an
/// enclosing `under` block (already resolved into a canonical
/// `AssumptionSet`) and a member's per-construct `assume { }` block
/// (resolved into an `AssumeDelta`).
///
/// The inner delta can only **add** to the outer environment. It is
/// forbidden to:
///
/// - Toggle stutter against the outer (silent `under` inherits the
///   construct default `stutter: true` per, so an inner `no stutter`
///   is rejected even when the outer is silent on stutter).
/// - Downgrade strong fairness to weak fairness on the same event,
///   compared on canonical `EventRef`s — so outer `strong fair S::tick`
///   plus inner `fair tick` (in scope `[S]`) is a downgrade, not just
///   when both spellings happen to match syntactically.
///
/// Removing fairness is impossible by construction (the merge takes
/// the union, never the difference), so this check polices only the
/// two cases above.
pub(super) fn check_under_add_only_resolved(
    under_resolved: &crate::elab::types::AssumptionSet,
    delta: &AssumeDelta,
    errors: &mut Vec<ElabError>,
) {
    if let Some((inner_stutter, span)) = delta.explicit_stutter {
        if inner_stutter != under_resolved.stutter {
            let (inner_label, outer_label) = if inner_stutter {
                ("stutter", "no stutter")
            } else {
                ("no stutter", "stutter")
            };
            errors.push(
                ElabError::with_span(
                    ErrorKind::InvalidScope,
                    format!(
                        "{}: inner `{inner_label}` would toggle the enclosing `under` block's `{outer_label}`",
                        crate::messages::UNDER_ADD_ONLY_VIOLATION
                    ),
                    "under block",
                    span,
                )
                .with_help(crate::messages::HINT_UNDER_ADD_ONLY_VIOLATION),
            );
        }
    }
    for (ev, span) in &delta.weak_fair {
        if under_resolved.strong_fair.contains(ev) {
            errors.push(
                ElabError::with_span(
                    ErrorKind::InvalidScope,
                    format!(
                        "{}: inner `fair {ev}` would downgrade the enclosing `under` block's `strong fair {ev}`",
                        crate::messages::UNDER_ADD_ONLY_VIOLATION
                    ),
                    "under block",
                    *span,
                )
                .with_help(crate::messages::HINT_UNDER_ADD_ONLY_VIOLATION),
            );
        }
    }
}

pub(super) fn resolve_by_lemmas_subset_containment(env: &mut Env) {
    use crate::elab::env::DeclKind;
    use crate::elab::types::AssumptionSet;

    // Snapshot lemma assumption sets indexed by bare name so the
    // theorem loop can borrow `env.theorems` mutably (well, immutably
    // here) without conflicting with `env.lemmas` access. The bare
    // key is safe because `env.lemmas` is the post-`build_working_namespace`
    // module-filtered view and bare names are unique within a module.
    let lemma_sets: HashMap<String, AssumptionSet> = env
        .lemmas
        .iter()
        .map(|l| (l.name.clone(), l.assumption_set.clone()))
        .collect();

    let current_module = env.module_name.clone();

    let mut new_errors: Vec<ElabError> = Vec::new();
    for theorem in &env.theorems {
        for by_ref in &theorem.by_lemmas {
            let display = by_ref.segments.join("::");

            // Path-arity validation: a lemma path is `name` or
            // `Mod::name`. Anything else is a parse-time well-formedness
            // failure that the parser cannot enforce on its own.
            if by_ref.segments.is_empty() || by_ref.segments.len() > 2 {
                new_errors.push(
                    ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "{}: lemma path `{display}` must be `name` or `Mod::name`",
                            crate::messages::LEMMA_ASSUMPTION_NOT_SUBSET
                        ),
                        "by lemma",
                        by_ref.span,
                    )
                    .with_help(crate::messages::HINT_LEMMA_ASSUMPTION_NOT_SUBSET),
                );
                continue;
            }

            // Resolve the path through the canonical decl registry.
            // For bare `name`, default the target module to the
            // current one — same convention as elsewhere in the elab.
            let (target_module, lemma_name): (Option<&str>, &str) = if by_ref.segments.len() == 2 {
                (
                    Some(by_ref.segments[0].as_str()),
                    by_ref.segments[1].as_str(),
                )
            } else {
                (current_module.as_deref(), by_ref.segments[0].as_str())
            };
            let decl_key = crate::elab::env::Env::qualified_key(target_module, lemma_name);
            let Some(decl) = env.decls.get(&decl_key) else {
                new_errors.push(
                    ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "{}: `{display}` is not a declared lemma",
                            crate::messages::LEMMA_ASSUMPTION_NOT_SUBSET
                        ),
                        "by lemma",
                        by_ref.span,
                    )
                    .with_help(crate::messages::HINT_LEMMA_ASSUMPTION_NOT_SUBSET),
                );
                continue;
            };

            // Kind validation: the canonical decl must actually be a
            // lemma. Reject everything else with a clean diagnostic
            // instead of silently no-op'ing.
            if decl.kind != DeclKind::Lemma {
                new_errors.push(
                    ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "{}: `{display}` is a {kind:?}, not a lemma",
                            crate::messages::LEMMA_ASSUMPTION_NOT_SUBSET,
                            kind = decl.kind
                        ),
                        "by lemma",
                        by_ref.span,
                    )
                    .with_help(crate::messages::HINT_LEMMA_ASSUMPTION_NOT_SUBSET),
                );
                continue;
            }

            // Cross-module references: the resolved decl must live in
            // the current module. Lemma reuse across module boundaries
            // currently requires explicit support in the working
            // namespace import flow, so reject it clearly here.
            if decl.module.as_deref() != current_module.as_deref() {
                let decl_mod = decl.module.as_deref().unwrap_or("<unmoduled>");
                let cur_mod = current_module.as_deref().unwrap_or("<unmoduled>");
                new_errors.push(
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: lemma `{display}` is declared in module `{decl_mod}` but the theorem is in module `{cur_mod}` — cross-module `by` references are not yet supported",
                            crate::messages::LEMMA_ASSUMPTION_NOT_SUBSET
                        ),
                        "by lemma",
                        by_ref.span,
                    )
                    .with_help(crate::messages::HINT_LEMMA_ASSUMPTION_NOT_SUBSET),
                );
                continue;
            }

            // The decl-system lookup has already disambiguated `(module,
            // name)`, so the bare-name access into the module-filtered
            // `env.lemmas` is safe.
            let Some(lemma_set) = lemma_sets.get(lemma_name) else {
                // Should not happen — if `env.decls` agrees the lemma
                // exists in the current module, `env.lemmas` must have
                // it after `build_working_namespace`. Defensive only.
                continue;
            };

            if !AssumptionSet::lemma_usable(lemma_set, &theorem.assumption_set) {
                let lemma_str = format_assumption_set(lemma_set);
                let theorem_str = format_assumption_set(&theorem.assumption_set);
                let missing = compute_missing(lemma_set, &theorem.assumption_set);
                new_errors.push(
                    ElabError::with_span(
                        ErrorKind::InvalidScope,
                        format!(
                            "{}: theorem `{}` cannot use lemma `{display}`\n\
                             \tLemma assumes: {{ {lemma_str} }}\n\
                             \tTheorem provides: {{ {theorem_str} }}\n\
                             \tMissing: {missing}",
                            crate::messages::LEMMA_ASSUMPTION_NOT_SUBSET,
                            theorem.name,
                        ),
                        "by lemma",
                        by_ref.span,
                    )
                    .with_help(crate::messages::HINT_LEMMA_ASSUMPTION_NOT_SUBSET),
                );
            }
        }
    }
    for err in new_errors {
        env.errors.push(err);
    }
}

/// Render an `AssumptionSet` in the canonical diagnostic
/// format: `stutter`/`no stutter` first (when present), then weak
/// fair items, then strong fair items, separated by `, `.
pub(super) fn format_assumption_set(set: &crate::elab::types::AssumptionSet) -> String {
    let mut parts: Vec<String> = Vec::new();
    if set.stutter {
        parts.push("stutter".to_owned());
    } else {
        parts.push("no stutter".to_owned());
    }
    for ev in &set.weak_fair {
        parts.push(format!("fair {ev}"));
    }
    for ev in &set.strong_fair {
        parts.push(format!("strong fair {ev}"));
    }
    parts.join(", ")
}

/// Compute the comma-separated list of items in `lemma` that are not
/// covered by `theorem`, used as the `Missing:` clause in the /// diagnostic format.
pub(super) fn compute_missing(
    lemma: &crate::elab::types::AssumptionSet,
    theorem: &crate::elab::types::AssumptionSet,
) -> String {
    let mut missing: Vec<String> = Vec::new();
    if !lemma.stutter && theorem.stutter {
        // The lemma was proved without stutter; the theorem admits
        // stuttering traces — the lemma's claim is too narrow.
        missing.push("no stutter".to_owned());
    }
    for ev in &lemma.strong_fair {
        if !theorem.strong_fair.contains(ev) {
            missing.push(format!("strong fair {ev}"));
        }
    }
    for ev in &lemma.weak_fair {
        if !theorem.weak_fair.contains(ev) && !theorem.strong_fair.contains(ev) {
            missing.push(format!("fair {ev}"));
        }
    }
    if missing.is_empty() {
        "<none>".to_owned()
    } else {
        missing.join(", ")
    }
}

/// Populate a single `AssumptionSet` from a parsed `AssumeBlock`.
/// `scope` is the list of system names visible at the verification site
/// (used to resolve unqualified event names and to enforce that
/// qualified `Sys::event` paths reference systems in scope).
pub(super) fn populate_assumption_set(
    set: &mut crate::elab::types::AssumptionSet,
    block: Option<&crate::ast::AssumeBlock>,
    scope: &[String],
    system_events: &HashMap<String, HashMap<String, bool>>,
    let_bindings: &HashMap<String, String>,
    errors: &mut Vec<ElabError>,
) {
    let Some(block) = block else {
        // No assume block — keep the construct default already installed
        // by collect. Nothing to do.
        return;
    };
    populate_assumption_set_from_items(
        set,
        &block.items,
        scope,
        system_events,
        let_bindings,
        errors,
    );
}

/// Same as `populate_assumption_set` but takes an items slice directly.
/// Used by the under-block resolver, which carries items
/// without the surrounding `AssumeBlock` wrapper.
pub(super) fn populate_assumption_set_from_items(
    set: &mut crate::elab::types::AssumptionSet,
    items: &[crate::ast::AssumeItem],
    scope: &[String],
    system_events: &HashMap<String, HashMap<String, bool>>,
    let_bindings: &HashMap<String, String>,
    errors: &mut Vec<ElabError>,
) {
    use crate::ast::AssumeItem;
    for item in items {
        match item {
            AssumeItem::Stutter { .. } => {
                set.stutter = true;
            }
            AssumeItem::NoStutter { .. } => {
                set.stutter = false;
            }
            AssumeItem::Fair { path, span } => {
                if let Some((ev_ref, is_param)) = super::resolve_event_path(
                    path,
                    scope,
                    system_events,
                    let_bindings,
                    errors,
                    *span,
                ) {
                    if is_param {
                        set.per_tuple.insert(ev_ref.clone());
                    }
                    set.weak_fair.insert(ev_ref);
                }
            }
            AssumeItem::StrongFair { path, span } => {
                if let Some((ev_ref, is_param)) = super::resolve_event_path(
                    path,
                    scope,
                    system_events,
                    let_bindings,
                    errors,
                    *span,
                ) {
                    if is_param {
                        set.per_tuple.insert(ev_ref.clone());
                    }
                    set.strong_fair.insert(ev_ref);
                }
            }
            // Store, Let, and Proc items handled during collection.
            AssumeItem::Store(_) | AssumeItem::Let(_) | AssumeItem::Proc(_) => {}
        }
    }
    set.normalize();
}
