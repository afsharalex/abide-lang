//! Semantic AST types for the Abide elaborator.
//!
//! These types represent the elaborated (resolved, type-checked) form of
//! Abide declarations. The parsed AST (`crate::ast`) is the parse
//! representation; these types carry semantic information.

use std::collections::HashMap;

pub type VariantRecordFields = Vec<(String, Ty)>;
pub type EnumVariantFields = Vec<(String, VariantRecordFields)>;
pub type VariantFieldsMap = HashMap<String, EnumVariantFields>;

#[derive(Clone, Debug)]
pub struct ERelCompBinding {
    pub var: String,
    pub domain: Ty,
    pub source: Option<Box<EExpr>>,
}

/// Semantic type representation (resolved from parse-level `TypeRef`/`Name`).
#[derive(Debug, Clone)]
pub enum Ty {
    /// Sum type: name + constructor names
    Enum(String, Vec<String>),
    /// Record type: name + fields (name, type)
    Record(String, Vec<(String, Ty)>),
    /// Type alias: name + underlying type
    Alias(String, Box<Ty>),
    /// Built-in type
    Builtin(BuiltinTy),
    /// Parameterized type: name + args
    Param(String, Vec<Ty>),
    /// Function type: param -> result
    Fn(Box<Ty>, Box<Ty>),
    /// Entity used as type (e.g. in quantifier domains)
    Entity(String),
    /// Name reference awaiting semantic resolution.
    Named(String),
    /// Poison type used after resolution/type-check failure.
    Error,
    /// Set<T>
    Set(Box<Ty>),
    /// Seq<T>
    Seq(Box<Ty>),
    /// Map<K, V>
    Map(Box<Ty>, Box<Ty>),
    /// Store<E> — finite store of entity instances.
    Store(String),
    /// Rel<A, B, ...> — finite n-ary tuple relation.
    Relation(Vec<Ty>),
    /// (A, B,...)
    Tuple(Vec<Ty>),
    /// Refinement type: base type + predicate (Int { $ > 0 })
    Refinement(Box<Ty>, Box<EExpr>),
    /// Newtype wrapper: distinct type wrapping an inner type.
    /// `type UserId(string)` creates Newtype("UserId", Box(Builtin(String))).
    Newtype(String, Box<Ty>),
}

impl Ty {
    /// Get the name of a type (for error messages).
    pub fn name(&self) -> &str {
        match self {
            Self::Enum(n, _)
            | Self::Record(n, _)
            | Self::Alias(n, _)
            | Self::Newtype(n, _)
            | Self::Param(n, _)
            | Self::Entity(n)
            | Self::Named(n) => n,
            Self::Builtin(b) => b.name(),
            Self::Error => "<error>",
            Self::Fn(_, _) => "->",
            Self::Set(_) => "Set",
            Self::Seq(_) => "Seq",
            Self::Map(_, _) => "Map",
            Self::Store(_) => "Store",
            Self::Relation(_) => "Rel",
            Self::Tuple(_) => "Tuple",
            Self::Refinement(base, _) => base.name(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinTy {
    Int,
    Bool,
    String,
    Identity,
    Real,
    Float,
}

impl BuiltinTy {
    pub fn name(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::Bool => "bool",
            Self::String => "string",
            Self::Identity => "identity",
            Self::Real => "real",
            Self::Float => "float",
        }
    }
}

// ── Elaborated declarations ──────────────────────────────────────────

/// Elaborated type declaration.
#[derive(Debug, Clone)]
pub struct EType {
    pub name: String,
    pub variants: Vec<EVariant>,
    pub ty: Ty,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub enum EVariant {
    Simple(String),
    Record(String, VariantRecordFields),
    Param(String, Vec<Ty>),
}

/// A generic enum definition that can be monomorphized on demand.
/// Stored in `Env::generic_types`, NOT in `Env::types`.
#[derive(Debug, Clone)]
pub struct GenericTypeDef {
    pub name: String,
    pub type_params: Vec<String>,
    /// Constructor names
    pub variant_names: Vec<String>,
    /// Per-variant field info with `Ty::Named("T")` for type parameters
    pub variant_fields: EnumVariantFields,
    pub visibility: crate::ast::Visibility,
    pub span: crate::span::Span,
}

/// Elaborated entity.
#[derive(Debug, Clone)]
pub struct EEntity {
    pub name: String,
    pub fields: Vec<EField>,
    pub actions: Vec<EAction>,
    /// derived fields declared on this entity.
    /// Each is a zero-argument pure expression that closes over the
    /// entity instance state.
    pub derived_fields: Vec<EDerived>,
    /// invariants declared on this entity. Each
    /// invariant is a Boolean expression that must hold in every
    /// reachable state for every instance of the entity. Per  /// entity invariants travel with the entity type into any system
    /// that pools it.
    pub invariants: Vec<EInvariant>,
    /// fsm declarations on this entity. Each fsm
    /// names one enum-typed field plus a transition table whose atoms
    /// have already been resolved to enum variant names.
    pub fsm_decls: Vec<EFsm>,
    pub span: Option<crate::span::Span>,
}

/// an elaborated fsm declaration. The `field` and
/// `enum_name` are resolved (the field exists on the entity and is
/// enum-typed); each row's `from` and `targets` are validated as
/// variants of `enum_name`. The `initial` state is the field's default
/// value (if statically determinable) and is used by the structural
/// reachability check.
#[derive(Debug, Clone)]
pub struct EFsm {
    pub field: String,
    pub enum_name: String,
    pub rows: Vec<EFsmRow>,
    pub initial: Option<String>,
    pub span: Option<crate::span::Span>,
}

/// one elaborated transition row. `from` and
/// `targets` are bare variant names of the enum the parent fsm
/// references; the `@` prefix is stripped at parse time.
#[derive(Debug, Clone)]
pub struct EFsmRow {
    pub from: String,
    pub targets: Vec<String>,
    pub span: Option<crate::span::Span>,
}

/// an elaborated invariant declaration. Lives on
/// `EEntity::invariants` (entity-level) or `ESystem::invariants`
/// (system-level). The body is a Boolean expression in the same
/// expression language as derived fields and theorem bodies.
#[derive(Debug, Clone)]
pub struct EInvariant {
    pub name: String,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
}

/// an elaborated `derived` field declaration.
/// Lives on `EEntity::derived_fields` (entity-level) or
/// `ESystem::derived_fields` (system-level). The body's type is
/// inferred from the elaborated expression — `body.ty()` is the
/// derived field's type.
#[derive(Debug, Clone)]
pub struct EDerived {
    pub name: String,
    pub body: EExpr,
    pub ty: Ty,
    pub span: Option<crate::span::Span>,
}

/// How a field's initial value is specified at the elaboration level.
#[derive(Debug, Clone)]
pub enum EFieldDefault {
    /// `= expr` — deterministic default
    Value(EExpr),
    /// `in { expr, expr,... }` — nondeterministic choice from a finite set
    In(Vec<EExpr>),
    /// `where expr` — predicate constraint on the initial value ($ = field value)
    Where(EExpr),
}

#[derive(Debug, Clone)]
pub struct EField {
    pub name: String,
    pub ty: Ty,
    pub default: Option<EFieldDefault>,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub struct EAction {
    pub name: String,
    pub refs: Vec<(String, Ty)>,
    pub params: Vec<(String, Ty)>,
    pub requires: Vec<EExpr>,
    pub ensures: Vec<EExpr>,
    pub body: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
}

/// Elaborated system.
#[derive(Debug, Clone)]
pub struct ESystem {
    pub name: String,
    /// Optional interface contract this system claims to satisfy.
    pub implements: Option<String>,
    /// Declared extern dependencies used by this system.
    pub deps: Vec<String>,
    /// flat state fields declared directly on the system.
    pub fields: Vec<EField>,
    /// store params from `system S(x: Store<E>)`.
    pub store_params: Vec<EStoreParam>,
    pub scopes: Vec<EScope>,
    pub commands: Vec<ECommand>,
    pub actions: Vec<ESystemAction>,
    pub queries: Vec<EQuery>,
    /// fsm declarations on direct system fields.
    /// This remains a narrow lifecycle table over enum-typed flat
    /// state fields, not a workflow construct.
    pub fsm_decls: Vec<EFsm>,
    /// derived fields declared on this system.
    /// Each is a zero-argument pure expression that closes over the
    /// system's flat state and pooled entities.
    pub derived_fields: Vec<EDerived>,
    /// invariants declared on this system. Each
    /// invariant is a Boolean expression that must hold in every
    /// reachable state. System invariants are scoped to the declaring
    /// system per — they do not travel with `dep` references.
    pub invariants: Vec<EInvariant>,
    /// /: system-internal predicates.
    pub preds: Vec<EPred>,
    /// let bindings from program declarations.
    /// Programs define their composition topology via let bindings that
    /// instantiate systems with store bindings. Non-program systems have
    /// this field empty.
    pub let_bindings: Vec<ELetBinding>,
    /// proc declarations (only on programs).
    pub procs: Vec<EProc>,
    /// reusable proc applications expanded into this program's procs
    /// during elaboration. Non-program systems keep this empty.
    pub proc_uses: Vec<EProcUse>,
    pub span: Option<crate::span::Span>,
}

/// elaborated store constructor parameter.
#[derive(Debug, Clone)]
pub struct EStoreParam {
    pub name: String,
    pub entity_type: String,
    pub lo: Option<i64>,
    pub hi: Option<i64>,
}

#[derive(Debug, Clone)]
pub struct EProcUse {
    pub proc_name: String,
    pub args: Vec<String>,
    pub alias: Option<String>,
    pub span: Option<crate::span::Span>,
}

/// Elaborated abstract capability contract.
#[derive(Debug, Clone)]
pub struct EInterface {
    pub name: String,
    pub commands: Vec<ECommand>,
    pub queries: Vec<EQuerySig>,
    pub span: Option<crate::span::Span>,
}

/// Elaborated executable boundary declaration.
#[derive(Debug, Clone)]
pub struct EExtern {
    pub name: String,
    pub commands: Vec<ECommand>,
    pub mays: Vec<EMay>,
    pub assumes: Vec<EExternAssume>,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub struct EMay {
    pub command: String,
    pub returns: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub enum EExternAssume {
    Fair(Vec<String>, Option<crate::span::Span>),
    StrongFair(Vec<String>, Option<crate::span::Span>),
    Expr(EExpr, Option<crate::span::Span>),
}

/// Abstract query signature on an interface.
#[derive(Debug, Clone)]
pub struct EQuerySig {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub return_type: Ty,
    pub span: Option<crate::span::Span>,
}

/// elaborated proc declaration.
#[derive(Debug, Clone)]
pub struct EProc {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub requires: Option<EExpr>,
    pub nodes: Vec<EProcNode>,
    pub edges: Vec<EProcEdge>,
    pub proc_uses: Vec<EProcUse>,
    pub span: Option<crate::span::Span>,
}

/// proc node — a named command invocation.
#[derive(Debug, Clone)]
pub struct EProcNode {
    pub name: String,
    pub instance: String,
    pub command: String,
    pub args: Vec<EExpr>,
}

/// proc dependency edge.
#[derive(Debug, Clone)]
pub struct EProcEdge {
    pub target: String,
    pub condition: EProcDepCond,
}

#[derive(Debug, Clone)]
pub enum EProcDepCond {
    Fact {
        node: String,
        qualifier: Option<String>,
    },
    Not(Box<EProcDepCond>),
    And(Box<EProcDepCond>, Box<EProcDepCond>),
    Or(Box<EProcDepCond>, Box<EProcDepCond>),
}

#[derive(Debug, Clone)]
pub struct EScope {
    pub entity: String,
    pub lo: i64,
    pub hi: i64,
}

/// public API declaration on a system. Commands declare the
/// externally callable surface; actions are private executable behavior with guarded bodies.
#[derive(Debug, Clone)]
pub struct ECommand {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    /// Optional return/outcome type: `command charge(o: Order) -> ChargeOutcome`
    pub return_type: Option<Ty>,
    pub span: Option<crate::span::Span>,
}

/// Private executable system behavior. Command bodies lower to actions with
/// the command name; explicit `action` declarations remain private.
#[derive(Debug, Clone)]
pub struct ESystemAction {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub requires: Vec<EExpr>,
    pub body: Vec<EEventAction>,
    /// Optional return expression: `return @ok(Receipt {... })`
    pub return_expr: Option<EExpr>,
    pub span: Option<crate::span::Span>,
}

/// public read-only observation on a system.
#[derive(Debug, Clone)]
pub struct EQuery {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
}

#[derive(Debug, Clone)]
pub struct EEvent {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub requires: Vec<EExpr>,
    pub ensures: Vec<EExpr>,
    pub body: Vec<EEventAction>,
    pub span: Option<crate::span::Span>,
}

/// Structured event body actions.
#[derive(Debug, Clone)]
pub enum EEventAction {
    /// choose var: entity where guard { body }
    Choose(String, Ty, EExpr, Vec<EEventAction>),
    /// for var: entity { body }
    ForAll(String, Ty, Vec<EEventAction>),
    /// create `EntityName` [in `store_name`] { field = expr,... }
    Create(String, Option<String>, Vec<(String, EExpr)>),
    /// `let r = Sys::command(args)`
    LetCrossCall(String, String, String, Vec<EExpr>),
    /// `System::event(args)`
    CrossCall(String, String, Vec<EExpr>),
    /// `match r { ... }` or `match Sys::command(args) { ... }`
    Match(EMatchScrutinee, Vec<EMatchArm>),
    /// target.action[refs](args)
    Apply(EExpr, String, Vec<EExpr>, Vec<EExpr>),
    /// Bare expression
    Expr(EExpr),
}

#[derive(Debug, Clone)]
pub enum EMatchScrutinee {
    Var(String),
    CrossCall(String, String, Vec<EExpr>),
}

#[derive(Debug, Clone)]
pub struct EMatchArm {
    pub pattern: EPattern,
    pub guard: Option<EExpr>,
    pub body: Vec<EEventAction>,
}

/// Elaborated predicate.
#[derive(Debug, Clone)]
pub struct EPred {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated property.
#[derive(Debug, Clone)]
pub struct EProp {
    pub name: String,
    pub target: Option<String>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

// ── Assumption sets ────────────────────────────────────────
//
// Every verify/theorem/lemma site carries an `AssumptionSet` summarizing
// the fairness and stutter assumptions in its `assume {... }` block,
// after construct defaults are applied and normalization is run.
//
// Defaults:
// * verify → stutter = false (closed-system, deadlock-detecting)
// * theorem → stutter = true (refinement-friendly, TLA+-style)
// * lemma → stutter = true
//
// Normalization:
// * sets are sorted alphabetically and deduplicated (BTreeSet)
// * if an event is in `strong_fair`, it is removed from `weak_fair`
// (strong fairness implies weak fairness)
//
// The stub `assume_block: Option<ast::AssumeBlock>` field on
// `EVerify`/`ETheorem`/`ELemma` is the parser source of truth and is
// preserved for diagnostic spans. The `assumption_set` field below is
// populated in the resolve pass once all systems are known.

/// A resolved reference to a command by its (system, command) name pair.
/// Sortable so that `BTreeSet<EventRef>` gives canonical alphabetical
/// ordering for `AssumptionSet` normalization.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EventRef {
    pub system: String,
    pub command: String,
}

impl EventRef {
    pub fn new(system: impl Into<String>, command: impl Into<String>) -> Self {
        Self {
            system: system.into(),
            command: command.into(),
        }
    }
}

impl std::fmt::Display for EventRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::{}", self.system, self.command)
    }
}

/// Normalized assumption set for a verification site (verify/theorem/lemma).
/// See the module-level comment above for defaults and normalization rules.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct AssumptionSet {
    /// Whether stutter steps are admitted at this verification site.
    pub stutter: bool,
    /// Events with weak fairness. After normalization, none of these are
    /// also in `strong_fair`.
    pub weak_fair: std::collections::BTreeSet<EventRef>,
    /// Events with strong fairness.
    pub strong_fair: std::collections::BTreeSet<EventRef>,
    /// Subset of `weak_fair ∪ strong_fair` whose events are parameterized.
    /// Parameterized fair events default to per-tuple fairness: the fairness
    /// obligation is asserted for each `(event, args)` tuple over the reachable
    /// state space, not for the event as a whole. The verifier uses this to
    /// choose the correct lasso-BMC encoding.
    pub per_tuple: std::collections::BTreeSet<EventRef>,
}

impl AssumptionSet {
    /// Construct the default `AssumptionSet` for a verify block:
    /// stutter off, no fairness.
    #[must_use]
    pub fn default_for_verify() -> Self {
        Self {
            stutter: false,
            weak_fair: std::collections::BTreeSet::new(),
            strong_fair: std::collections::BTreeSet::new(),
            per_tuple: std::collections::BTreeSet::new(),
        }
    }

    /// Construct the default `AssumptionSet` for a theorem or lemma:
    /// stutter on, no fairness.
    #[must_use]
    pub fn default_for_theorem_or_lemma() -> Self {
        Self {
            stutter: true,
            weak_fair: std::collections::BTreeSet::new(),
            strong_fair: std::collections::BTreeSet::new(),
            per_tuple: std::collections::BTreeSet::new(),
        }
    }

    /// Apply the normalization rule from any event in
    /// `strong_fair` is removed from `weak_fair`. Sort/dedup are
    /// already maintained by the `BTreeSet` storage.
    ///
    /// `per_tuple` is preserved across normalization (an event remains
    /// per-tuple regardless of which strength bucket it occupies).
    pub fn normalize(&mut self) {
        for ev in &self.strong_fair {
            self.weak_fair.remove(ev);
        }
    }

    /// `lemma_usable(L, T)`: returns true iff lemma `L` can be used inside
    /// theorem `T`'s proof environment. Required:
    /// * every weak-fair event in `L` is weak-fair *or* strong-fair in `T`
    /// * every strong-fair event in `L` is strong-fair in `T`
    /// * if `T.stutter` and `!L.stutter`, reject — `T` admits stuttering
    ///   traces that `L` was never proven over, so `L`'s claim does not
    ///   cover `T`'s trace set. The converse (`L.stutter && !T.stutter`)
    ///   is fine: a lemma proven over the larger trace set still holds
    ///   on the smaller one.
    #[must_use]
    pub fn lemma_usable(lemma: &Self, theorem: &Self) -> bool {
        // T allows stuttering but L was proven without it, so T's traces
        // include stutter steps L never saw and L's claim is too narrow.
        if theorem.stutter && !lemma.stutter {
            return false;
        }
        // Strong fairness must be present at strong strength.
        for ev in &lemma.strong_fair {
            if !theorem.strong_fair.contains(ev) {
                return false;
            }
        }
        // Weak fairness can be satisfied by either weak or strong fairness.
        for ev in &lemma.weak_fair {
            if !theorem.weak_fair.contains(ev) && !theorem.strong_fair.contains(ev) {
                return false;
            }
        }
        true
    }
}

/// elaborated store declaration.
#[derive(Debug, Clone)]
pub struct EStoreDecl {
    pub name: String,
    pub entity_type: String,
    pub lo: i64,
    pub hi: i64,
}

/// elaborated proc pool bound declaration for verify blocks.
#[derive(Debug, Clone)]
pub struct EProcBoundDecl {
    pub system_type: String,
    pub proc: String,
    pub lo: i64,
    pub hi: i64,
}

/// elaborated let binding (system instantiation).
#[derive(Debug, Clone)]
pub struct ELetBinding {
    pub name: String,
    pub system_type: String,
    pub store_bindings: Vec<(String, String)>,
}

/// Elaborated verify block.
#[derive(Debug, Clone)]
pub struct EVerify {
    pub name: String,
    /// optional BMC depth override from `verify name [depth: N]`.
    pub depth: Option<usize>,
    /// store declarations from assume block.
    pub stores: Vec<EStoreDecl>,
    /// proc pool bounds from assume block.
    pub proc_bounds: Vec<EProcBoundDecl>,
    /// let bindings from assume block.
    pub let_bindings: Vec<ELetBinding>,
    /// Parsed `assume {... }` block, retained from the AST so the resolve
    /// pass can populate `assumption_set` and so diagnostics can recover
    /// item spans.
    pub assume_block: Option<crate::ast::AssumeBlock>,
    /// Normalized assumption set populated by the resolve pass from
    /// `assume_block` plus the verify-block construct default.
    pub assumption_set: AssumptionSet,
    pub asserts: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated scene.
#[derive(Debug, Clone)]
pub struct EScene {
    pub name: String,
    /// store declarations from given blocks.
    pub stores: Vec<EStoreDecl>,
    /// let bindings from given blocks.
    pub let_bindings: Vec<ELetBinding>,
    pub givens: Vec<ESceneGiven>,
    pub whens: Vec<ESceneWhen>,
    pub thens: Vec<EExpr>,
    /// Constraint expressions from given blocks. These are asserted at
    /// step 0 as initial-state assumptions (not end-state assertions).
    pub given_constraints: Vec<EExpr>,
    /// Activate declarations from given blocks. Each activation
    /// pre-configures named entity instances in a store at step 0.
    pub activations: Vec<EActivation>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Activation declaration: pre-activate named entity instances in a store.
#[derive(Debug, Clone)]
pub struct EActivation {
    pub instances: Vec<String>,
    pub store_name: String,
}

#[derive(Debug, Clone)]
pub struct ESceneGiven {
    pub var: String,
    pub entity_type: String,
    /// optional store name from `in store_name` in
    /// entity bindings. When present, the entity slot should be
    /// allocated within the named store's slot range.
    pub store_name: Option<String>,
    pub condition: Option<EExpr>,
}

#[derive(Debug, Clone)]
pub enum ESceneWhen {
    Action {
        var: String,
        system: String,
        event: String,
        args: Vec<EExpr>,
        card: Option<String>,
    },
    Assume(EExpr),
}

/// canonical proof-environment object
/// representing an `under { ITEMS }` block. Each member theorem/lemma
/// references one of these by index — the same `EUnderBlock` is shared
/// across all siblings, so its `resolved_set` is computed exactly
/// once with a fixed scope and reused. This is the durable
/// representation: the under block is a *single object*, not raw syntax
/// recopied per member.
#[derive(Debug, Clone)]
pub struct EUnderBlock {
    /// Raw assumption items from the parsed under block, retained so
    /// the resolve pass can re-resolve event paths and so diagnostics
    /// can recover per-item spans.
    pub items: Vec<crate::ast::AssumeItem>,
    /// Shared resolution scope. Computed at collect time as the union
    /// of all member theorem target systems. Empty when the under
    /// block contains only lemmas (which have no `for SystemList`
    /// header) — in that case the resolve pass falls back to the full
    /// system set, the same scope a standalone lemma would use.
    pub scope: Vec<String>,
    /// Span of the `under` keyword + body, for diagnostics.
    pub span: crate::span::Span,
    /// Module that owns this `under` block, captured at collect time
    /// from `env.module_name`. Drives the same module filtering that
    /// `build_working_namespace` applies to theorems/lemmas, so a
    /// foreign-module under block does NOT leak into another module's
    /// resolved env in a multi-module load.
    pub module: Option<String>,
    /// Source file containing this `under` block, captured at collect
    /// time from `env.current_file`. Used for diagnostics and to keep
    /// provenance parallel with `ETheorem::file` / `ELemma::file`.
    pub file: Option<String>,
    /// Canonical resolved assumption set, populated by
    /// `resolve_assumption_sets`. Built from `items` resolved against
    /// `scope`, with the construct default (`stutter: true` for
    /// theorems/lemmas) as the floor. Members use this as their
    /// inherited assumption set; the resolve pass never re-resolves
    /// the raw items per member.
    pub resolved_set: AssumptionSet,
}

/// Elaborated theorem block.
#[derive(Debug, Clone)]
pub struct ETheorem {
    pub name: String,
    pub targets: Vec<String>,
    /// Parsed `assume {... }` block. See `EVerify::assume_block`.
    pub assume_block: Option<crate::ast::AssumeBlock>,
    /// index into the env's / `ElabResult`'s
    /// `under_blocks` vec, if this theorem was declared inside an
    /// `under` block. The resolve pass uses the indexed `EUnderBlock`'s
    /// `resolved_set` as the floor of this theorem's assumption set and runs
    /// the add-only check on the inner `assume_block` against that resolved
    /// floor.
    pub enclosing_under_idx: Option<usize>,
    /// Normalized assumption set populated by the resolve pass.
    pub assumption_set: AssumptionSet,
    pub invariants: Vec<EExpr>,
    pub shows: Vec<EExpr>,
    /// External proof artifact reference from `by "file"`, when present.
    pub by_file: Option<String>,
    /// lemma references from `by L1, L2,...`
    /// body items. The resolve pass enforces subset containment
    /// (`AssumptionSet::lemma_usable`) for each entry.
    pub by_lemmas: Vec<crate::ast::ByLemmaRef>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated axiom declaration.
#[derive(Debug, Clone)]
pub struct EAxiom {
    pub name: String,
    pub body: EExpr,
    /// External proof artifact reference from `by "file"`, when present.
    pub by_file: Option<String>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated lemma block.
#[derive(Debug, Clone)]
pub struct ELemma {
    pub name: String,
    /// Parsed `assume {... }` block. See `EVerify::assume_block`.
    pub assume_block: Option<crate::ast::AssumeBlock>,
    /// index into the env's / `ElabResult`'s
    /// `under_blocks` vec. See `ETheorem::enclosing_under_idx`.
    pub enclosing_under_idx: Option<usize>,
    /// Normalized assumption set populated by the resolve pass.
    pub assumption_set: AssumptionSet,
    pub body: Vec<EExpr>,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Elaborated const declaration.
#[derive(Debug, Clone)]
pub struct EConst {
    pub name: String,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
}

/// Elaborated fn declaration.
#[derive(Debug, Clone)]
pub struct EFn {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub ret_ty: Ty,
    pub contracts: Vec<EContract>,
    pub body: EExpr,
    pub span: Option<crate::span::Span>,
    pub file: Option<String>,
}

/// Contract clause on fn declarations and while loops.
#[derive(Debug, Clone)]
pub enum EContract {
    Requires(EExpr),
    Ensures(EExpr),
    Decreases { measures: Vec<EExpr>, star: bool },
    Invariant(EExpr),
}

// ── Elaborated expressions ───────────────────────────────────────────

/// Type-annotated expression.
#[derive(Debug, Clone)]
pub enum EExpr {
    Lit(Ty, Literal, Option<crate::span::Span>),
    Var(Ty, String, Option<crate::span::Span>),
    Field(Ty, Box<EExpr>, String, Option<crate::span::Span>),
    Prime(Ty, Box<EExpr>, Option<crate::span::Span>),
    BinOp(Ty, BinOp, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    UnOp(Ty, UnOp, Box<EExpr>, Option<crate::span::Span>),
    Call(Ty, Box<EExpr>, Vec<EExpr>, Option<crate::span::Span>),
    CallR(
        Ty,
        Box<EExpr>,
        Vec<EExpr>,
        Vec<EExpr>,
        Option<crate::span::Span>,
    ),
    Qual(Ty, String, String, Option<crate::span::Span>),
    Quant(
        Ty,
        Quantifier,
        String,
        Ty,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Always(Ty, Box<EExpr>, Option<crate::span::Span>),
    Eventually(Ty, Box<EExpr>, Option<crate::span::Span>),
    Until(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    /// `historically P` — past-time dual of `always`.
    Historically(Ty, Box<EExpr>, Option<crate::span::Span>),
    /// `once P` — past-time dual of `eventually`.
    Once(Ty, Box<EExpr>, Option<crate::span::Span>),
    /// `previously P` — past-time dual of `next`.
    /// False at trace position 0.
    Previously(Ty, Box<EExpr>, Option<crate::span::Span>),
    /// `P since Q` — past-time dual of `until`.
    Since(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Assert(Ty, Box<EExpr>, Option<crate::span::Span>),
    Assume(Ty, Box<EExpr>, Option<crate::span::Span>),
    Assign(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    NamedPair(Ty, String, Box<EExpr>, Option<crate::span::Span>),
    Seq(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    SameStep(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Let(
        Vec<(String, Option<Ty>, EExpr)>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Lam(
        Vec<(String, Ty)>,
        Option<Ty>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Unresolved(String, Option<crate::span::Span>),
    TupleLit(Ty, Vec<EExpr>, Option<crate::span::Span>),
    In(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Card(Ty, Box<EExpr>, Option<crate::span::Span>),
    Pipe(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    Match(
        Box<EExpr>,
        Vec<(EPattern, Option<EExpr>, EExpr)>,
        Option<crate::span::Span>,
    ),
    Choose(
        Ty,
        String,
        Ty,
        Option<Box<EExpr>>,
        Option<crate::span::Span>,
    ),
    MapUpdate(
        Ty,
        Box<EExpr>,
        Box<EExpr>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    Index(Ty, Box<EExpr>, Box<EExpr>, Option<crate::span::Span>),
    SetComp(
        Ty,
        Option<Box<EExpr>>,
        String,
        Ty,
        Option<Box<EExpr>>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    RelComp(
        Ty,
        Box<EExpr>,
        Vec<ERelCompBinding>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    SetLit(Ty, Vec<EExpr>, Option<crate::span::Span>),
    SeqLit(Ty, Vec<EExpr>, Option<crate::span::Span>),
    MapLit(Ty, Vec<(EExpr, EExpr)>, Option<crate::span::Span>),
    /// Built-in qualified call: `Set::union(s1`, s2), `Map::domain(m)`, etc.
    /// `QualCall(result_ty`, `type_name`, `func_name`, args, span)
    QualCall(Ty, String, String, Vec<EExpr>, Option<crate::span::Span>),
    Sorry(Option<crate::span::Span>),
    Todo(Option<crate::span::Span>),
    // Imperative constructs
    Block(Vec<EExpr>, Option<crate::span::Span>),
    /// VarDecl(name, type, init, rest, span)
    VarDecl(
        String,
        Option<Ty>,
        Box<EExpr>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    /// While(cond, contracts, body, span)
    While(
        Box<EExpr>,
        Vec<EContract>,
        Box<EExpr>,
        Option<crate::span::Span>,
    ),
    /// IfElse(cond, then, else, span)
    IfElse(
        Box<EExpr>,
        Box<EExpr>,
        Option<Box<EExpr>>,
        Option<crate::span::Span>,
    ),
    /// arithmetic aggregator.
    /// Aggregate(ty, kind, var, domain_ty, body, in_filter, span)
    /// `in_filter` is the optional `in coll` membership expression:
    /// `EExpr::In(bool_ty, Var(x), coll, sp)`.
    Aggregate(
        Ty,
        crate::ast::AggKind,
        String,
        Ty,
        Box<EExpr>,
        Option<Box<EExpr>>,
        Option<crate::span::Span>,
    ),
    /// `saw Sys::event(args)` — past-time event observation.
    /// Saw(ty, system_name, event_name, args, span)
    /// Each arg is Some(expr) for value match or None for wildcard.
    Saw(
        Ty,
        String,
        String,
        Vec<Option<Box<EExpr>>>,
        Option<crate::span::Span>,
    ),
    /// Record constructor: @Some { value: 1 }
    /// CtorRecord(ty, qualifier, `ctor_name`, fields, span)
    CtorRecord(
        Ty,
        Option<String>,
        String,
        Vec<(String, EExpr)>,
        Option<crate::span::Span>,
    ),
    /// Struct constructor: UiState { screen: @home, mode: @normal }
    /// StructCtor(ty, struct_name, fields, span)
    StructCtor(Ty, String, Vec<(String, EExpr)>, Option<crate::span::Span>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum EPattern {
    Var(String),
    Ctor(String, Vec<(String, EPattern)>),
    Wild,
    Or(Box<EPattern>, Box<EPattern>),
}

impl EExpr {
    /// Get the type annotation of an expression.
    pub fn ty(&self) -> Ty {
        match self {
            Self::Lit(ty, _, _)
            | Self::Var(ty, _, _)
            | Self::Field(ty, _, _, _)
            | Self::Prime(ty, _, _)
            | Self::BinOp(ty, _, _, _, _)
            | Self::UnOp(ty, _, _, _)
            | Self::Call(ty, _, _, _)
            | Self::CallR(ty, _, _, _, _)
            | Self::QualCall(ty, _, _, _, _)
            | Self::Qual(ty, _, _, _)
            | Self::Quant(ty, _, _, _, _, _)
            | Self::Always(ty, _, _)
            | Self::Eventually(ty, _, _)
            | Self::Until(ty, _, _, _)
            | Self::Historically(ty, _, _)
            | Self::Once(ty, _, _)
            | Self::Previously(ty, _, _)
            | Self::Since(ty, _, _, _)
            | Self::Assert(ty, _, _)
            | Self::Assume(ty, _, _)
            | Self::Assign(ty, _, _, _)
            | Self::NamedPair(ty, _, _, _)
            | Self::Seq(ty, _, _, _)
            | Self::SameStep(ty, _, _, _)
            | Self::TupleLit(ty, _, _)
            | Self::In(ty, _, _, _)
            | Self::Card(ty, _, _)
            | Self::Pipe(ty, _, _, _)
            | Self::MapUpdate(ty, _, _, _, _)
            | Self::Index(ty, _, _, _)
            | Self::SetComp(ty, _, _, _, _, _, _)
            | Self::RelComp(ty, _, _, _, _)
            | Self::SetLit(ty, _, _)
            | Self::SeqLit(ty, _, _)
            | Self::MapLit(ty, _, _)
            | Self::Saw(ty, _, _, _, _)
            | Self::Aggregate(ty, _, _, _, _, _, _)
            | Self::Choose(ty, _, _, _, _)
            | Self::StructCtor(ty, _, _, _) => ty.clone(),
            Self::Let(_, body, _) => body.ty(),
            Self::Match(scrut, _, _) => scrut.ty(),
            Self::Block(items, _) => items.last().map_or(Ty::Error, EExpr::ty),
            Self::VarDecl(_, _, _, rest, _) => rest.ty(),
            Self::While(_, _, _, _) => Ty::Error,
            Self::IfElse(_, then_body, _, _) => then_body.ty(),
            Self::CtorRecord(ty, _, _, _, _) => ty.clone(),
            Self::Sorry(_) | Self::Todo(_) | Self::Lam(_, _, _, _) | Self::Unresolved(_, _) => {
                Ty::Error
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Real(f64),
    Float(f64),
    Str(String),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    NEq,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    Implies,
    Unord,
    Conc,
    Xor,
    /// `<>` — set union, seq concat, map merge (type-directed)
    Diamond,
    /// `!*` — set disjointness
    Disjoint,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    All,
    Exists,
    Some,
    No,
    One,
    Lone,
}

// ── Elaboration result ───────────────────────────────────────────────

/// Full elaboration result containing all elaborated declarations.
#[derive(Debug, Clone)]
pub struct ElabResult {
    pub module_name: Option<String>,
    pub includes: Vec<String>,
    pub use_decls: Vec<crate::ast::UseDecl>,
    /// Alias → canonical name map from use declarations (e.g., `WSlot` → `Slot`).
    /// Used by IR lowering to canonicalize entity/system references.
    pub aliases: std::collections::HashMap<String, String>,
    pub types: Vec<EType>,
    pub entities: Vec<EEntity>,
    pub interfaces: Vec<EInterface>,
    pub externs: Vec<EExtern>,
    pub systems: Vec<ESystem>,
    pub preds: Vec<EPred>,
    pub props: Vec<EProp>,
    pub verifies: Vec<EVerify>,
    pub scenes: Vec<EScene>,
    pub theorems: Vec<ETheorem>,
    pub axioms: Vec<EAxiom>,
    pub lemmas: Vec<ELemma>,
    pub consts: Vec<EConst>,
    pub fns: Vec<EFn>,
    /// canonical proof-environment objects
    /// (`under { }` blocks). Each member theorem/lemma references
    /// one of these by `enclosing_under_idx`. Indices are stable
    /// across `Env` → `ElabResult` cloning.
    pub under_blocks: Vec<EUnderBlock>,
}

#[cfg(test)]
mod assumption_set_tests {
    use super::*;

    fn ev(sys: &str, name: &str) -> EventRef {
        EventRef::new(sys, name)
    }

    #[test]
    fn defaults_distinguish_verify_from_theorem() {
        assert!(!AssumptionSet::default_for_verify().stutter);
        assert!(AssumptionSet::default_for_theorem_or_lemma().stutter);
    }

    #[test]
    fn normalize_drops_weak_when_strong_present() {
        let mut a = AssumptionSet::default_for_verify();
        a.weak_fair.insert(ev("S", "tick"));
        a.strong_fair.insert(ev("S", "tick"));
        a.normalize();
        assert!(a.weak_fair.is_empty());
        assert!(a.strong_fair.contains(&ev("S", "tick")));
    }

    #[test]
    fn normalize_keeps_weak_when_no_strong() {
        let mut a = AssumptionSet::default_for_verify();
        a.weak_fair.insert(ev("S", "tick"));
        a.weak_fair.insert(ev("S", "tock"));
        a.normalize();
        assert_eq!(a.weak_fair.len(), 2);
    }

    #[test]
    fn btreeset_provides_alphabetical_order_and_dedup() {
        let mut a = AssumptionSet::default_for_verify();
        a.weak_fair.insert(ev("S", "z"));
        a.weak_fair.insert(ev("S", "a"));
        a.weak_fair.insert(ev("S", "a")); // duplicate
        let names: Vec<&str> = a.weak_fair.iter().map(|e| e.command.as_str()).collect();
        assert_eq!(names, vec!["a", "z"]);
    }

    #[test]
    fn lemma_usable_subset_accepted() {
        let mut t = AssumptionSet::default_for_theorem_or_lemma();
        t.weak_fair.insert(ev("S", "a"));
        t.weak_fair.insert(ev("S", "b"));

        let mut l = AssumptionSet::default_for_theorem_or_lemma();
        l.weak_fair.insert(ev("S", "a"));

        assert!(AssumptionSet::lemma_usable(&l, &t));
    }

    #[test]
    fn lemma_usable_extra_event_rejected() {
        let mut t = AssumptionSet::default_for_theorem_or_lemma();
        t.weak_fair.insert(ev("S", "a"));

        let mut l = AssumptionSet::default_for_theorem_or_lemma();
        l.weak_fair.insert(ev("S", "a"));
        l.weak_fair.insert(ev("S", "b")); // not in T

        assert!(!AssumptionSet::lemma_usable(&l, &t));
    }

    #[test]
    fn lemma_usable_strong_satisfies_weak() {
        // Lemma needs weak fairness on `tick`; theorem provides strong.
        // Strong implies weak, so this is fine.
        let mut t = AssumptionSet::default_for_theorem_or_lemma();
        t.strong_fair.insert(ev("S", "tick"));

        let mut l = AssumptionSet::default_for_theorem_or_lemma();
        l.weak_fair.insert(ev("S", "tick"));

        assert!(AssumptionSet::lemma_usable(&l, &t));
    }

    #[test]
    fn lemma_usable_weak_does_not_satisfy_strong() {
        let mut t = AssumptionSet::default_for_theorem_or_lemma();
        t.weak_fair.insert(ev("S", "tick"));

        let mut l = AssumptionSet::default_for_theorem_or_lemma();
        l.strong_fair.insert(ev("S", "tick"));

        assert!(!AssumptionSet::lemma_usable(&l, &t));
    }

    #[test]
    fn lemma_usable_stutter_rule() {
        // T allows stutter, L was proven without it — REJECT.
        // L's claim only covers no-stutter traces; T's trace set is
        // strictly bigger, so L's promise doesn't reach all of T.
        let l_no_stutter = AssumptionSet {
            stutter: false,
            ..Default::default()
        };
        let t_with_stutter = AssumptionSet {
            stutter: true,
            ..Default::default()
        };
        assert!(!AssumptionSet::lemma_usable(&l_no_stutter, &t_with_stutter));

        // L allows stutter, T does not — ACCEPT.
        // L was proven over the bigger trace set, so it still holds on
        // T's smaller (no-stutter) trace set.
        let l_with_stutter = AssumptionSet {
            stutter: true,
            ..Default::default()
        };
        let t_no_stutter = AssumptionSet {
            stutter: false,
            ..Default::default()
        };
        assert!(AssumptionSet::lemma_usable(&l_with_stutter, &t_no_stutter));

        // Both stutter — fine.
        let l_with = AssumptionSet {
            stutter: true,
            ..Default::default()
        };
        let t_with = AssumptionSet {
            stutter: true,
            ..Default::default()
        };
        assert!(AssumptionSet::lemma_usable(&l_with, &t_with));

        // Neither stutter — fine.
        let l_no = AssumptionSet {
            stutter: false,
            ..Default::default()
        };
        let t_no = AssumptionSet {
            stutter: false,
            ..Default::default()
        };
        assert!(AssumptionSet::lemma_usable(&l_no, &t_no));
    }

    #[test]
    fn event_ref_display() {
        assert_eq!(
            format!("{}", ev("Commerce", "mark_paid")),
            "Commerce::mark_paid"
        );
    }
}
