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

/// Hint when `uses` is used inside a system body (not a valid keyword).
pub const HINT_USES_KEYWORD: &str = "write 'use EntityName'";

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

// ── Elaboration messages ─────────────────────────────────────────────

/// Help for duplicate declaration errors.
pub const HELP_DUPLICATE_DECL: &str = "rename one of the declarations";

/// Help when an unresolved uppercase name might be a constructor.
pub const HELP_CONSTRUCTOR_PREFIX: &str = "state constructors use the '@' prefix";

/// Help for primed variable outside action body.
pub const HELP_PRIME_FIELDS_ONLY: &str = "only entity fields can be primed";

/// Help for requires clause type.
pub const MSG_REQUIRES_SHOULD_BE_BOOL: &str = "requires expression should be Bool";

// ── Contract messages ───────────────────────────────────────────────

/// Warning when `decreases *` is used (skips termination checking).
pub const DECREASES_STAR_WARNING: &str =
    "decreases * skips termination checking — ensure termination manually";

/// Error when a decreases measure is not Int.
pub const DECREASES_MEASURE_NOT_INT: &str = "decreases measure must have type Int";

/// Error when ensures clause is not Bool.
pub const ENSURES_NOT_BOOL: &str = "ensures clause must have type Bool";

/// Error when requires clause is not Bool.
pub const REQUIRES_NOT_BOOL: &str = "requires clause must have type Bool";

/// Help for requires clause type mismatch.
pub const HELP_REQUIRES_BOOL: &str = "requires clauses must evaluate to Bool";

/// Help for ensures clause type mismatch.
pub const HELP_ENSURES_BOOL: &str = "ensures clauses must evaluate to Bool";

/// Help for decreases measure type mismatch.
pub const HELP_DECREASES_INT: &str = "decreases measures must be Int expressions";

/// Error when while loop has multiple decreases clauses.
pub const WHILE_MULTIPLE_DECREASES: &str =
    "while loop has multiple decreases clauses; only one is allowed";

/// Error when if/else branches have different types.
pub const IF_ELSE_TYPE_MISMATCH: &str = "if/else branches have different types";

/// Error when refinement predicate is not Bool.
pub const REFINEMENT_PREDICATE_NOT_BOOL: &str = "refinement predicate must have type Bool";

/// Help for refinement predicate type mismatch.
pub const HELP_REFINEMENT_BOOL: &str = "refinement predicates must evaluate to Bool (e.g., $ > 0)";

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
pub const THEOREM_LIVENESS_UNSUPPORTED: &str =
    "theorem contains 'eventually' — \
     liveness properties require a verify block with fair event declarations";

/// Liveness violation diagnostic label.
pub fn label_liveness_violation(name: &str) -> String {
    format!("liveness violation found for '{name}' (infinite counterexample)")
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
pub fn scene_same_step_multi_instance(scene: &str, var_a: &str, n_a: usize, var_b: &str, n_b: usize) -> String {
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
