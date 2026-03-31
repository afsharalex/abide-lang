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

// ── Verification messages ────────────────────────────────────────────

/// Scene check: unsatisfiable scenario.
pub const SCENE_UNSATISFIABLE: &str =
    "scenario is unsatisfiable — no execution matches given+when+then";

/// Scene check: Z3 returned unknown.
pub const SCENE_UNKNOWN: &str = "Z3 returned unknown";

/// Scene check: no systems or entities found.
pub const SCENE_EMPTY_SCOPE: &str = "no systems or entities found";

/// Theorem: liveness properties cannot be proved by induction.
pub const THEOREM_LIVENESS_UNSUPPORTED: &str =
    "theorem contains 'eventually' (possibly in a referenced pred/prop) — \
     liveness properties cannot be proved by induction; \
     use bounded model checking (verify block) instead";

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
