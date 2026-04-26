//! Centralized user-facing error messages for the Abide compiler.
//!
//! All static message strings are defined here so they can be reviewed and
//! edited in one place. Dynamic messages (format strings with interpolated
//! names/types) remain at their call sites but reference these constants
//! where possible.

// ── Parser hints ─────────────────────────────────────────────────────

/// Hint when `import` is used (not a valid keyword).
pub const HINT_IMPORT_KEYWORD: &str =
    "use 'module' to declare membership and 'include' for file contents";

/// Hint when `proof` is used (not a valid keyword).
pub const HINT_PROOF_KEYWORD: &str =
    "use 'theorem name for System { show ... }' for unbounded proofs";

/// Hint when `field` is used at the top level (not a valid keyword).
pub const HINT_FIELD_KEYWORD_TOP: &str = "declare fields directly inside entity: 'name: Type'";

/// Hint when `field` is used inside an entity body (not a valid keyword).
pub const HINT_FIELD_KEYWORD_ENTITY: &str =
    "write fields directly: 'name: Type' or 'name: Type = default'";

/// `use Entity` removed from system bodies.
pub const USE_ENTITY_REMOVED: &str =
    "`use Entity` has been replaced by `Store<T>` constructor parameters on systems \
     — write `system S(es: Store<E>) { ... }` instead";

/// `for System[0..N]` removed from verify/scene blocks.
pub const FOR_SYSTEM_REMOVED: &str =
    "`for System[0..N]` has been replaced by `store` declarations and `let` bindings \
     in `assume { }` blocks — write `verify v { assume { store es: E[0..3]; \
     let s = S { es: es } } ... }` instead";

/// Hint when `assert` appears inside an event body.
pub const HINT_ASSERT_IN_EVENT: &str =
    "'assert' belongs in verify blocks, not event bodies. Did you mean 'requires'?";

/// Hint for valid event body contents.
pub const HINT_EVENT_BODY: &str =
    "event bodies contain: 'choose', 'for', 'create', or expressions like 'entity.action()'";

/// Hint for valid verify body contents.
pub const HINT_VERIFY_BODY: &str = "verify blocks contain 'assert' statements";

/// Hint for valid theorem body contents (when `assert` is used instead of `show`).
pub const HINT_THEOREM_BODY: &str =
    "theorem blocks use 'show' for goals and 'invariant' for assumptions, not 'assert'";

/// Hint for valid theorem body contents (when an unexpected token is found).
pub const HINT_THEOREM_BODY_SHOW: &str = "theorem blocks contain 'show <expression>' statements";

/// Hint for valid scene body contents (when `assert` is used).
pub const HINT_SCENE_BODY: &str = "scene blocks use 'given', 'when', and 'then', not 'assert'";

/// Hint for valid scene body contents (when an unexpected token is found).
pub const HINT_SCENE_BODY_STRUCTURE: &str =
    "scene blocks contain: given { ... }, when { ... }, then { ... }";

/// Diagnostic for the legacy `fair event` / `strong fair event` modifier
/// syntax on system command declarations. Fairness is no longer a
/// declaration modifier.
/// It now lives in `assume { fair X }` blocks on the verification site.
pub const LEGACY_FAIR_EVENT_REJECTED: &str =
    "`fair`/`strong fair` are no longer event-declaration modifiers";

/// Hint accompanying `LEGACY_FAIR_EVENT_REJECTED` — points the user at the
/// new position for fairness annotations.
pub const HINT_LEGACY_FAIR_EVENT: &str =
    "move fairness to an `assume { fair Sys::name }` block on the relevant verify/theorem/lemma";

/// Diagnostic when an `assume { }` block contains both `stutter` and
/// `no stutter`. The block must choose one or the other, not both.
pub const ASSUME_STUTTER_CONFLICT: &str =
    "`assume { }` block contains both `stutter` and `no stutter`";

/// Hint accompanying `ASSUME_STUTTER_CONFLICT`.
pub const HINT_ASSUME_STUTTER_CONFLICT: &str =
    "remove one — `stutter` opts in, `no stutter` opts out";

/// Diagnostic when an event path inside `assume { fair PATH }` does not
/// resolve to a known event in scope.
pub const UNKNOWN_FAIR_EVENT: &str = "fairness annotation references an unknown event";

/// Hint accompanying `UNKNOWN_FAIR_EVENT`.
pub const HINT_UNKNOWN_FAIR_EVENT: &str =
    "use `Sys::event` qualified form, and ensure the event is declared in a system in scope";

/// Diagnostic when an unqualified event name in `assume { fair NAME }`
/// matches more than one system in the verification site's scope.
pub const AMBIGUOUS_FAIR_EVENT: &str =
    "fairness annotation is ambiguous — multiple systems define this event";

/// an `under` block may not contain a `verify`
/// declaration. `verify` blocks are bounded model checks; `under` blocks
/// group unbounded theorems and lemmas. The two are independent.
pub const UNDER_VERIFY_NOT_ALLOWED: &str =
    "`under` blocks may only contain theorems and lemmas, not `verify` blocks";

/// Hint accompanying `UNDER_VERIFY_NOT_ALLOWED`.
pub const HINT_UNDER_VERIFY_NOT_ALLOWED: &str =
    "move the verify block out of the `under` block — verify blocks have their own `assume { }` blocks";

/// an inner `assume { }` block on a theorem or
/// lemma cannot weaken the enclosing `under` block. The `under` block
/// is the *floor* of the environment for every construct inside it;
/// per-construct `assume` raises the floor and never lowers it.
pub const UNDER_ADD_ONLY_VIOLATION: &str =
    "inner `assume { }` block weakens the enclosing `under` block";

/// Hint accompanying `UNDER_ADD_ONLY_VIOLATION`.
pub const HINT_UNDER_ADD_ONLY_VIOLATION: &str =
    "to use a weaker environment, move the construct out of the `under` block";

/// a theorem references a lemma via `by L`, but
/// the lemma was proved under stronger assumptions than the theorem
/// provides. The lemma's claim does not cover the theorem's trace set.
pub const LEMMA_ASSUMPTION_NOT_SUBSET: &str =
    "lemma was proved under stronger assumptions than the theorem provides";

/// Hint accompanying `LEMMA_ASSUMPTION_NOT_SUBSET`.
pub const HINT_LEMMA_ASSUMPTION_NOT_SUBSET: &str =
    "either add the missing assumptions to the theorem, or move the lemma to a weaker `under` block";

/// a past-time liveness operator (`previously`,
/// `since`) appears in an invariant body. Invariants are state-only
/// (safety) and cannot reference liveness operators that reason
/// about state transitions or trace shape.
pub const INVARIANT_LIVENESS_NOT_ALLOWED: &str =
    "liveness temporal operators are not allowed in invariant bodies";

/// Hint accompanying `INVARIANT_LIVENESS_NOT_ALLOWED`.
pub const HINT_INVARIANT_LIVENESS_NOT_ALLOWED: &str =
    "invariants are safety properties — for liveness, use a `prop` and verify it explicitly";

/// past-time temporal operators (`historically`,
/// `once`, `previously`, `since`) appear in a theorem show or in a
/// merged entity/system invariant on the theorem path. The 1-induction
/// and IC3 backends instantiate the property at two adjacent symbolic
/// states (step 0 and step 1) without an explicit history state, so
/// past-time semantics — which reference the trace prefix `[0, n]` —
/// cannot be encoded soundly there. Bounded model checking (verify
/// blocks) handles past-time operators correctly because each step in
/// the BMC unrolling is a real trace position.
pub const THEOREM_PAST_TIME_UNSUPPORTED: &str =
    "past-time temporal operators are not yet supported on the unbounded theorem path";

/// Hint accompanying `THEOREM_PAST_TIME_UNSUPPORTED`.
pub const HINT_THEOREM_PAST_TIME_UNSUPPORTED: &str =
    "use a `verify` block with bounded model checking — past-time semantics in induction/IC3 require explicit history variables, which are not yet implemented";

/// a temporal operator (`always`,
/// `eventually`, `until`, `historically`, `once`, `previously`,
/// `since`) appears in a lemma body. Lemmas are state-level proof
/// building blocks: their bodies are encoded by the pure-expression
/// encoder (the same encoder that handles fn pre/postconditions),
/// which has no notion of trace steps or history. Without that, no
/// temporal operator can be encoded soundly inside a lemma body.
pub const LEMMA_TEMPORAL_UNSUPPORTED: &str =
    "temporal operators are not yet supported in lemma bodies";

/// Hint accompanying `LEMMA_TEMPORAL_UNSUPPORTED`. Points the user
/// at the two construct kinds that DO handle temporal:
///
/// - `verify` blocks: bounded model checking handles every temporal
///   operator (past-time, future-time safety, future-time liveness).
/// - `theorem` blocks: 1-induction / IC3 handle future-time safety,
///   and the liveness-to-safety reduction (`try_liveness_reduction`)
///   handles future-time liveness shapes such as
///   `always (P implies eventually Q)`. Past-time is currently
///   rejected on the theorem path (see `THEOREM_PAST_TIME_UNSUPPORTED`).
pub const HINT_LEMMA_TEMPORAL_UNSUPPORTED: &str =
    "lemmas are state-level building blocks — for trace properties use a `verify` block (bounded model checking handles every temporal operator) or a `theorem` block (1-induction/IC3 for future-time safety, liveness-to-safety reduction for future-time liveness)";

// ── Elaboration messages ─────────────────────────────────────────────

/// Help for duplicate declaration errors.
pub const HELP_DUPLICATE_DECL: &str = "rename one of the declarations";

/// Help when an unresolved uppercase name might be a constructor.
pub const HELP_CONSTRUCTOR_PREFIX: &str = "state constructors use the '@' prefix";

/// Help for primed variable outside action body.
pub const HELP_PRIME_FIELDS_ONLY: &str = "only entity fields can be primed";

/// Help for requires clause type.
pub const MSG_REQUIRES_SHOULD_BE_BOOL: &str = "requires expression should be bool";

/// Error when an imperative or higher-order expression appears in a verifier
/// property position (`verify`, `theorem`, `scene`).
pub const VERIFIER_EXPR_NOT_ALLOWED: &str =
    "expression form is not allowed in verify/theorem/scene property positions";

/// Help accompanying `VERIFIER_EXPR_NOT_ALLOWED`.
pub const HINT_VERIFIER_EXPR_NOT_ALLOWED: &str =
    "verifier property expressions must stay pure and first-order — use let, match, if/else, quantifiers, choose, assert/assume wrappers, and pure helper functions instead of lambdas or var/while/block sequencing";

// ── Contract messages ───────────────────────────────────────────────

/// Warning when `decreases *` is used (skips termination checking).
pub const DECREASES_STAR_WARNING: &str =
    "decreases * skips termination checking — ensure termination manually";

/// Error when a decreases measure is not int.
pub const DECREASES_MEASURE_NOT_INT: &str = "decreases measure must have type int";

/// Error when ensures clause is not bool.
pub const ENSURES_NOT_BOOL: &str = "ensures clause must have type bool";

/// Error when requires clause is not bool.
pub const REQUIRES_NOT_BOOL: &str = "requires clause must have type bool";

/// Help for requires clause type mismatch.
pub const HELP_REQUIRES_BOOL: &str = "requires clauses must evaluate to bool";

/// Help for ensures clause type mismatch.
pub const HELP_ENSURES_BOOL: &str = "ensures clauses must evaluate to bool";

/// Help for decreases measure type mismatch.
pub const HELP_DECREASES_INT: &str = "decreases measures must be int expressions";

/// Error when while loop has multiple decreases clauses.
pub const WHILE_MULTIPLE_DECREASES: &str =
    "while loop has multiple decreases clauses; only one is allowed";

/// Error when if/else branches have different types.
pub const IF_ELSE_TYPE_MISMATCH: &str = "if/else branches have different types";

/// Error when refinement predicate is not bool.
pub const REFINEMENT_PREDICATE_NOT_BOOL: &str = "refinement predicate must have type bool";

/// Help for refinement predicate type mismatch.
pub const HELP_REFINEMENT_BOOL: &str = "refinement predicates must evaluate to bool (e.g., $ > 0)";

/// Help for self-recursive functions missing decreases.
pub const HELP_SELF_RECURSION_DECREASES: &str =
    "add a 'decreases' clause to prove termination for recursive functions";

/// Help for mutual fn-fn cycles — all participants need decreases.
pub const HELP_MUTUAL_FN_DECREASES: &str = "add 'decreases' clauses to all functions in the cycle";

/// Help for circular definitions involving preds/props (decreases not applicable).
pub const HELP_CIRCULAR_DEFINITION: &str =
    "preds and props cannot be recursive — break the cycle by inlining or restructuring";

/// Help for ambiguous constructor records.
pub const HELP_AMBIGUOUS_CTOR: &str =
    "use a qualified form like @Enum::Ctor { ... } to disambiguate";

// ── Verification messages ────────────────────────────────────────────

/// Scene check: unsatisfiable scenario.
pub const SCENE_UNSATISFIABLE: &str =
    "scenario is unsatisfiable — no execution matches given+when+then";

/// Scene check: Z3 returned unknown.
pub const SCENE_UNKNOWN: &str = "Z3 returned unknown";

/// Scene check: no systems or entities found.
pub const SCENE_EMPTY_SCOPE: &str = "no systems or entities found";

/// Theorem: liveness properties require bounded checking, not unbounded proof.
pub const THEOREM_LIVENESS_UNSUPPORTED: &str = "theorem contains 'eventually' — \
     liveness properties require a verify block with fair event declarations";

/// Liveness violation diagnostic label.
pub fn label_liveness_violation(name: &str) -> String {
    format!("liveness violation found for '{name}' (infinite counterexample)")
}

/// Deadlock diagnostic label.
pub fn label_deadlock(name: &str, step: usize) -> String {
    format!("deadlock for '{name}' at step {step} (no events enabled, stutter is opted out)")
}

/// BMC: Z3 returned unknown without timeout.
pub const BMC_UNKNOWN: &str = "Z3 returned unknown — try reducing bound or simplifying property";

/// Theorem/verify: no systems or entities in scope.
pub const VERIFY_EMPTY_SCOPE: &str = "no systems or entities found for theorem";

/// Pre-check: unresolved function call after def expansion.
pub const PRECHECK_UNRESOLVED_FN: &str =
    "unresolved function call (not found in pred/fn definitions)";

/// Tiered dispatch: induction not applicable due to liveness.
pub const TIERED_LIVENESS_SKIP: &str = "induction not applicable (liveness)";

/// Tiered dispatch: induction failed with IC3 skipped.
pub const TIERED_NO_IC3: &str = "induction failed (IC3 skipped via --no-ic3)";

/// Tiered dispatch: both induction and IC3 failed.
pub const TIERED_BOTH_FAILED: &str = "induction and IC3 failed";

/// Theorem proving: invariant base case Z3 unknown.
pub const THEOREM_INV_BASE_UNKNOWN: &str = "Z3 returned unknown when checking invariant base case";

/// Theorem proving: invariant step case Z3 unknown.
pub const THEOREM_INV_STEP_UNKNOWN: &str = "Z3 returned unknown when checking invariant step case";

/// Theorem proving: base case failed.
pub const THEOREM_BASE_FAILED: &str = "base case failed — property does not hold at initial state";

/// Theorem proving: base case Z3 unknown.
pub const THEOREM_BASE_UNKNOWN: &str = "Z3 returned unknown when checking base case";

/// Theorem proving: inductive step Z3 unknown.
pub const THEOREM_STEP_UNKNOWN: &str = "Z3 returned unknown when checking inductive step";

/// Theorem proving: trace cannot extend under `assume { no stutter }`,
/// so the inductive step would be vacuously discharged from a
/// contradictory transition relation.
pub const THEOREM_VACUOUS_UNDER_NO_STUTTER: &str =
    "trace cannot extend under `assume { no stutter }` — no event is enabled at the \
     current step and stutter is opted out, so the induction step would be vacuously \
     discharged. Add `assume { stutter }` to allow stutter steps, or fix the \
     precondition that traps the system.";

// ── Derived field messages ──────────────────────────────────────────

/// Derived field declared outside an entity or system body.
pub const DERIVED_INVALID_SCOPE: &str =
    "`derived` declarations can only appear inside entity or system bodies";

/// Two derived fields (or a derived field and a regular field/action)
/// share the same name within a single entity or system.
pub const DERIVED_DUPLICATE_NAME: &str =
    "duplicate `derived` name in this entity or system — names must be \
     unique across fields, derived fields, and actions";

/// Format the cycle path for `DERIVED_CYCLE` diagnostics, reporting the
/// full reference chain, e.g.
/// `derived field cycle: a -> b -> c -> a`.
pub fn derived_cycle(path: &[String]) -> String {
    format!("derived field cycle: {}", path.join(" -> "))
}

// ── Entity/system invariant messages ────────────────────────────────

/// An entity or system invariant declaration includes a parameter
/// list. Invariants are unconditional facts about the
/// system and cannot be parameterized.
pub const INVARIANT_PARAM_REJECTED: &str = "invariants cannot take parameters — define a `pred` \
     for the parameterized form and reference it from the invariant body";

/// Two invariants on the same entity or system share the same name,
/// or an invariant name collides with a field, derived field, action,
/// or event in the same scope.
pub const INVARIANT_DUPLICATE_NAME: &str =
    "duplicate invariant name in this entity or system — invariant \
     names must be unique within their containing scope and must not \
     collide with fields, derived fields, actions, or events";

/// Format an invariant violation diagnostic with the failing invariant
/// name. Used by the verifier when an event boundary fails to preserve
/// a named invariant on an entity in scope.
pub fn invariant_violated(name: &str) -> String {
    format!("invariant `{name}` is not preserved by every event")
}

// ── fsm declaration messages ( / ) ─────────────────────

/// `fsm` declaration appears outside an entity body. Per fsm
/// declarations live only on entity fields; there is no system-level
/// or top-level form.
pub const FSM_INVALID_SCOPE: &str = "`fsm` declarations can only appear inside entity bodies";

/// The field name after `fsm` does not match any field on the
/// containing entity.
pub fn fsm_unknown_field(entity: &str, field: &str) -> String {
    format!("`fsm` declaration references unknown field `{field}` on entity `{entity}`")
}

/// The field named in an `fsm` declaration is not enum-typed. Per Item
/// 50.2 fsm declarations only apply to fields whose static type is an
/// enum (so the transition table can be checked against the variant
/// list).
pub fn fsm_field_not_enum(entity: &str, field: &str) -> String {
    format!(
        "`fsm` declaration on `{entity}::{field}` is invalid — fsm \
         requires the field to have an enum type"
    )
}

/// An atom in an fsm transition row is not a variant of the field's
/// enum type. Caught at elab time before any verification runs.
pub fn fsm_unknown_variant(entity: &str, field: &str, atom: &str, enum_name: &str) -> String {
    format!(
        "`fsm` for `{entity}::{field}` references unknown variant \
         `@{atom}` — `{atom}` is not a variant of enum `{enum_name}`"
    )
}

/// Two `fsm` declarations on the same entity name the same field. Per
/// each field has at most one fsm.
pub fn fsm_duplicate(entity: &str, field: &str) -> String {
    format!("duplicate `fsm` declaration for field `{entity}::{field}` — only one fsm per field is allowed")
}

/// A non-terminal state in an fsm cannot reach any terminal state via
/// the declared transitions. emit at *declaration time* as
/// a warning (not an error) — some specs deliberately have looping
/// monitor states.
pub fn fsm_unreachable_state(entity: &str, field: &str, state: &str) -> String {
    format!(
        "fsm state `@{state}` in `{entity}::{field}` is unreachable from \
         the field's initial state — likely a typo or dead state"
    )
}

/// A non-terminal state in an fsm has no path to any terminal state.
/// Per "every non-terminal state must have a path to at
/// least one terminal state in the fsm graph." A trap is reported as
/// a warning because some specs deliberately use sink-loop monitor
/// states; the warning catches accidental dead-ends.
pub fn fsm_trap_state(entity: &str, field: &str, state: &str) -> String {
    format!(
        "fsm state `@{state}` in `{entity}::{field}` is non-terminal but \
         has no path to any terminal state — possible trap or sink loop"
    )
}

/// Format a fsm transition violation diagnostic. Used by the verifier
/// when an event boundary moves an entity field along an edge that
/// the fsm transition table does not allow.
pub fn fsm_invalid_transition(entity: &str, field: &str, from: &str, to: &str) -> String {
    format!(
        "fsm `{entity}::{field}` does not allow transition `@{from}` \
         -> `@{to}`"
    )
}

/// review: an entity action's body contains a primed
/// assignment (`field' =...`) inside a nested expression (an `if`,
/// `while`, `match`, or block) instead of as a top-level statement.
/// The IR lowering's `extract_updates()` only walks top-level
/// `Assign(Prime, _)` nodes, so nested primes would silently
/// disappear from the verifier and bypass the fsm checks.
/// This is rejected with a clear error so users either flatten the
/// body or split the action into multiple guarded actions.
pub const ACTION_NESTED_PRIME: &str =
    "primed assignments (`field' = ...`) in entity action bodies \
     must appear as top-level statements; nested forms (inside `if`, \
     `while`, `match`, blocks, etc.) are not supported and would be \
     silently dropped by the verifier — split the action into \
     separate guarded actions instead";

/// an entity action statically prime-assigns the
/// fsm field to a state that is not a legal target from the source
/// state implied by the action's `requires` clause. Detected at elab
/// time so the user gets a clear diagnostic instead of silently having
/// the verifier filter the action out.
pub fn fsm_action_violation(
    entity: &str,
    field: &str,
    action: &str,
    from: &str,
    to: &str,
    valid_targets: &[String],
) -> String {
    let valid_str = if valid_targets.is_empty() {
        "(none — `@{from}` is terminal in the fsm)".to_owned()
    } else {
        valid_targets
            .iter()
            .map(|t| format!("@{t}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "action `{entity}::{action}` violates fsm `{entity}::{field}`: \
         transition `@{from}` -> `@{to}` is not in the table; valid \
         targets from `@{from}`: {valid_str}"
    )
}

// ── Function contract verification messages ─────────────────────────

/// Loop invariant does not hold on entry.
pub const FN_LOOP_INIT_FAILED: &str = "loop invariant does not hold on entry";

/// Loop invariant is not preserved by iteration.
pub const FN_LOOP_PRESERVATION_FAILED: &str = "loop invariant is not preserved by iteration";

/// Loop termination could not be proved.
pub const FN_LOOP_TERMINATION_FAILED: &str =
    "loop termination could not be proved: decreases measure may \
     not strictly decrease or may be negative";

/// While loop requires at least one invariant.
pub const FN_LOOP_NO_INVARIANT: &str =
    "while loop in function with ensures requires at least one loop invariant — \
     add 'invariant <expr>' to the while loop";

/// Function call precondition not satisfied at call site.
pub const FN_CALL_PRECONDITION_FAILED: &str =
    "precondition of called function may not hold at this call site";

/// Recursive function termination could not be proved.
pub const FN_TERMINATION_FAILED: &str =
    "recursive call does not provably decrease the termination measure";

/// Assertion in fn body failed — could not prove it holds at that point.
pub const FN_ASSERT_FAILED: &str = "assertion may not hold at this point in the function body";

/// Assume warning — condition not verified, user takes responsibility.
pub const FN_ASSUME_WARNING: &str =
    "assume: condition not verified — user asserts this holds without proof";

/// Constructor field destructuring not supported.
pub const FN_CTOR_FIELDS_UNSUPPORTED: &str =
    "constructor field destructuring is not yet supported in fn contract verification — \
     enums with data fields require algebraic datatype encoding";

// ── Loader messages ─────────────────────────────────────────────────

/// Help for circular include errors.
pub const HELP_CIRCULAR_INCLUDE: &str =
    "break the cycle by removing one of the include directives or restructuring into separate modules";

/// Help for circular use dependency errors.
pub const HELP_CIRCULAR_USE: &str =
    "break the cycle by removing one of the use declarations or merging the modules";

// ── CLI diagnostic labels ──────────────────────────────────────────

/// Diagnostic label for counterexample results.
pub fn label_counterexample(name: &str) -> String {
    format!("counterexample found for '{name}'")
}

/// Diagnostic label for scene failure results.
pub fn label_scene_fail(name: &str, reason: &str) -> String {
    format!("scene '{name}' failed: {reason}")
}

/// Diagnostic label for unprovable results.
pub fn label_unprovable(name: &str, hint: &str) -> String {
    format!("could not prove '{name}': {hint}")
}

/// Diagnostic label for fn contract violation results.
pub fn label_fn_contract_failed(name: &str) -> String {
    format!("fn contract violated for '{name}'")
}

// ── Match exhaustiveness ────────────────────────────────────────────

/// Error for non-exhaustive match expression.
pub fn non_exhaustive_match(missing: &[&str]) -> String {
    match missing.len() {
        1 => format!("non-exhaustive match: missing constructor {}", missing[0]),
        _ => format!(
            "non-exhaustive match: missing constructors {}",
            missing.join(", ")
        ),
    }
}

/// Help text for non-exhaustive match.
pub const HELP_NON_EXHAUSTIVE_MATCH: &str =
    "add the missing patterns or use a wildcard `_` to cover all remaining cases";

// ── Scene cardinality and composition ───────────────────────────────

/// Error: ^| used with multi-instance event.
pub fn scene_xor_multi_instance(scene: &str, var: &str, n: usize) -> String {
    format!(
        "scene '{scene}': event '{var}' in `^|` has {n} instances; \
         exclusive choice requires single-instance cardinality ({{one}} or {{lone}})"
    )
}

/// Error: ^| event lacks fire tracking.
pub fn scene_xor_no_fire_tracking(scene: &str, var: &str) -> String {
    format!(
        "scene '{scene}': event '{var}' in `^|` requires \
         {{lone}} cardinality (has no fire tracking)"
    )
}

/// Error: same-step & with multi-instance event.
pub fn scene_same_step_multi_instance(
    scene: &str,
    var_a: &str,
    n_a: usize,
    var_b: &str,
    n_b: usize,
) -> String {
    format!(
        "scene '{scene}': same-step composition `&` requires {{one}} or {{lone}} cardinality; \
         event '{var_a}' has {n_a} instances, event '{var_b}' has {n_b} instances"
    )
}

/// Error: same-step & events touch the same entity type.
pub fn scene_same_step_entity_conflict(scene: &str, entity: &str) -> String {
    format!(
        "scene '{scene}': same-step composition `&` is not supported for events that touch \
         the same entity type '{entity}'. Use events on different entity types or separate steps."
    )
}

// ── Liveness-to-safety reduction ─────────────────────────────────────

/// Method name for liveness proofs via reduction.
pub const LIVENESS_REDUCTION_METHOD: &str = "liveness-to-safety (1-induction)";

/// Method name for quantified liveness proofs via symmetry reduction.
pub const SYMMETRY_REDUCTION_METHOD: &str = "symmetry reduction + IC3";

/// Hint when liveness reduction fails.
pub const LIVENESS_REDUCTION_FAILED: &str =
    "liveness-to-safety reduction could not prove the property; \
     try a verify block with bounded lasso BMC for counterexample search";

/// Hint when symmetry reduction fails (asymmetric system or IC3 timeout).
pub const SYMMETRY_REDUCTION_FAILED: &str =
    "symmetry reduction could not prove quantified liveness \
     (asymmetric entity interactions or IC3 timeout); \
     lasso BMC provides bounded checking";

/// Error: unknown event variable in scene ordering.
pub fn scene_ordering_unknown_var(scene: &str, var: &str, declared: &str) -> String {
    format!(
        "scene '{scene}': ordering references unknown event variable '{var}'; \
         declared event variables: {declared}"
    )
}

// ── Nondeterministic field default validation ───────────────────────

pub fn where_predicate_not_bool(ty_name: &str) -> String {
    format!("`where` predicate must be a boolean expression, got type {ty_name}")
}

pub fn in_value_not_constructor(enum_name: &str) -> String {
    format!("`in` values for {enum_name} field must be constructors (@Name), not expressions")
}

pub fn enum_default_not_constructor(enum_name: &str, ctors: &str) -> String {
    format!(
        "{enum_name} field default must be a constructor (@Name), not an expression; \
         valid constructors: {ctors}"
    )
}

// ── Collection operations ───────────────────────────────────────────

pub fn collection_op_unsupported_arity(type_name: &str, func_name: &str, n: usize) -> String {
    format!("{type_name}::{func_name} takes {n} arguments, which is not supported")
}

// ── `saw` operator messages ─────────────────────────────────────────

/// Parser-level rejection: `saw E::f(args) ->...` or `saw E::f(args) =>...`.
/// `saw` matches the call only; return-value matching is forbidden.
pub const SAW_RETURN_VALUE_FORBIDDEN: &str =
    "`saw` matches the event call, not the return value — \
     arrow forms (`->`, `=>`) after `saw` are not allowed";

/// Hint accompanying `SAW_RETURN_VALUE_FORBIDDEN`.
pub const HINT_SAW_RETURN_VALUE_FORBIDDEN: &str =
    "pattern-match the return value at the call site if needed; \
     `saw` only observes which event was called with which arguments";

/// `saw` is not valid in invariant bodies. Invariants
/// are pure state predicates; `saw` reasons about trace history.
pub const SAW_NOT_ALLOWED_IN_INVARIANT: &str =
    "`saw` is not allowed in invariant bodies — invariants are state-only \
     predicates; use a `verify` or `theorem` block for trace-history properties";

/// `saw` is not valid in fn bodies or contracts. Pure
/// functions have no trace context.
pub const SAW_NOT_ALLOWED_IN_FN_BODY: &str =
    "`saw` is not allowed in function bodies or contracts — pure functions \
     have no trace context; use a `verify` block for trace-history properties";

/// `saw` on the unbounded theorem path. Like past-time operators, `saw`
/// reasons over the trace prefix `[0, n]`, which cannot be encoded in
/// 1-induction or IC3 (two adjacent symbolic states, no history).
pub const THEOREM_SAW_UNSUPPORTED: &str =
    "`saw` is not yet supported on the unbounded theorem path";

/// Hint accompanying `THEOREM_SAW_UNSUPPORTED`.
pub const HINT_THEOREM_SAW_UNSUPPORTED: &str =
    "use a `verify` block with bounded model checking — \
     `saw` semantics in induction/IC3 require event-history \
     variables, which are not yet implemented";

/// `saw` is currently restricted to explicit extern-boundary commands.
pub const SAW_EXTERN_QUALIFIED_ONLY: &str =
    "`saw` is currently restricted to extern boundary commands — use the explicit form `Extern::command(...)`";

/// `saw` event path does not resolve to a known extern command.
pub const SAW_UNKNOWN_EVENT: &str =
    "`saw` references an unknown extern command — use `Extern::command(...)`";

/// `saw` argument count does not match the event's parameter count.
pub fn saw_arity_mismatch(sys: &str, evt: &str, expected: usize, got: usize) -> String {
    format!("`saw {sys}::{evt}` expects {expected} arguments but got {got}")
}

// ── command / step / query ─────────────────────────────────

/// `event` keyword is no longer valid in system bodies.
pub const EVENT_KEYWORD_REMOVED: &str = "`event` has been replaced by `command` — \
     declare a `command` directly, optionally with a guarded body; \
     legacy `step` declarations remain available for compatibility";

/// `ensures` is not valid on step declarations.
pub const STEP_ENSURES_NOT_ALLOWED: &str = "`ensures` is not valid on `step` declarations — \
     the step body is the postcondition; use `requires` for guards";

/// A legacy `step` name does not match any declared `command` in the same system.
pub fn step_no_matching_command(step_name: &str, system_name: &str) -> String {
    format!(
        "legacy `step {step_name}` does not match any `command` declared in system `{system_name}`"
    )
}

/// Label for a legacy step that has no matching command.
pub fn label_step_no_matching_command(step_name: &str) -> String {
    format!("no `command {step_name}` found in this system")
}

/// A legacy `step` clause and its matching `command` have different parameter counts.
pub fn step_command_param_mismatch(step_name: &str, cmd_arity: usize, step_arity: usize) -> String {
    format!(
        "legacy `step {step_name}` has {step_arity} parameters but `command {step_name}` declares {cmd_arity}"
    )
}

/// A legacy `step` parameter type does not match the corresponding `command` parameter type.
pub fn step_command_type_mismatch(
    step_name: &str,
    param_pos: usize,
    cmd_ty: &str,
    step_ty: &str,
) -> String {
    format!(
        "legacy `step {step_name}` parameter {param_pos} has type `{step_ty}` but `command {step_name}` declares `{cmd_ty}`"
    )
}

// ── Generic enum diagnostics ──────────────────────────────

/// Wrong number of type arguments for a generic enum.
pub fn generic_arity_mismatch(name: &str, expected: usize, got: usize) -> String {
    format!("`{name}` expects {expected} type argument(s), but {got} were provided")
}

/// A non-generic type used with type arguments.
pub fn not_a_generic_type(name: &str) -> String {
    format!("`{name}` is not a generic type and cannot take type arguments")
}

/// Constructor is ambiguous across multiple monomorphized instances.
pub fn ambiguous_generic_constructor(ctor_name: &str, candidates: &[String]) -> String {
    format!(
        "constructor `{ctor_name}` is ambiguous — found in {}; qualify with the enum type",
        candidates.join(", ")
    )
}
