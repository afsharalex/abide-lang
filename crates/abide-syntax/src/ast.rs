use crate::span::Span;

// ── Program ──────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: Vec<TopDecl>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ErrorNode {
    pub skipped_tokens: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TopDecl {
    Module(ModuleDecl),
    Include(IncludeDecl),
    Use(UseDecl),
    Const(ConstDecl),
    Fn(FnDecl),
    Type(TypeDecl),
    Record(RecordDecl),
    Alias(AliasDecl),
    Newtype(NewtypeDecl),
    Entity(EntityDecl),
    Interface(InterfaceDecl),
    Extern(ExternDecl),
    System(SystemDecl),
    Proc(ProcDecl),
    Program(ProgramDecl),
    Pred(PredDecl),
    Prop(PropDecl),
    Verify(VerifyDecl),
    Theorem(TheoremDecl),
    Lemma(LemmaDecl),
    Scene(SceneDecl),
    Axiom(AxiomDecl),
    Under(UnderBlock),
    Error(ErrorNode),
}

// ── Module / Include / Use ────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct ModuleDecl {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IncludeDecl {
    pub path: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Debug, Clone)]
pub enum UseDecl {
    All {
        module: String,
        span: Span,
    },
    Items {
        module: String,
        items: Vec<UseItem>,
        span: Span,
    },
    Single {
        module: String,
        name: String,
        span: Span,
    },
    Alias {
        module: String,
        name: String,
        alias: String,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub enum UseItem {
    Name {
        name: String,
        span: Span,
    },
    Alias {
        name: String,
        alias: String,
        span: Span,
    },
}

// ── Constants and Pure Functions ─────────────────────────────────────

#[derive(Debug, Clone)]
pub struct ConstDecl {
    pub name: String,
    pub visibility: Visibility,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FnDecl {
    pub name: String,
    pub visibility: Visibility,
    pub params: Vec<TypedParam>,
    pub ret_type: TypeRef,
    pub contracts: Vec<Contract>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TypedParam {
    pub name: String,
    pub ty: TypeRef,
    pub span: Span,
}

// ── Type Declarations ────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct TypeDecl {
    pub name: String,
    pub visibility: Visibility,
    /// Type parameters: `["T"]` for `Option<T>`, `["T", "E"]` for `Result<T, E>`.
    pub type_params: Vec<String>,
    pub variants: Vec<TypeVariant>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypeVariant {
    Simple {
        name: String,
        span: Span,
    },
    /// Tuple payload variant: `ok(Int)`, `ok(Int, String)`
    Tuple {
        name: String,
        fields: Vec<TypeRef>,
        span: Span,
    },
    Record {
        name: String,
        fields: Vec<RecField>,
        span: Span,
    },
    Param {
        name: String,
        types: Vec<TypeRef>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct RecordDecl {
    pub name: String,
    pub visibility: Visibility,
    pub fields: Vec<RecField>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct RecField {
    pub name: String,
    pub ty: TypeRef,
    pub span: Span,
}

/// Type alias declaration: `type Name = TypeRef`
#[derive(Debug, Clone)]
pub struct AliasDecl {
    pub name: String,
    pub visibility: Visibility,
    pub target: TypeRef,
    pub span: Span,
}

/// Newtype wrapper: `type UserId(string)`.
/// Creates a distinct type wrapping an inner type with a constructor.
#[derive(Debug, Clone)]
pub struct NewtypeDecl {
    pub name: String,
    pub visibility: Visibility,
    pub inner: TypeRef,
    pub span: Span,
}

// ── Type References ──────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct TypeRef {
    pub kind: TypeRefKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypeRefKind {
    /// `A -> B` (right-associative function type)
    Fn(Box<TypeRef>, Box<TypeRef>),
    /// `Name`
    Simple(String),
    /// `Name[A, B]`
    Param(String, Vec<TypeRef>),
    /// `(A, B,...)` — 2+ elements
    Tuple(Vec<TypeRef>),
    /// `(A)` — grouping
    Paren(Box<TypeRef>),
    /// `T { pred }` — refinement type (uses `$` placeholder)
    Refine(Box<TypeRef>, Box<Expr>),
    /// `T<A> { pred }` — refined parameterized type
    RefineParam(Box<TypeRef>, Box<Expr>),
    /// `name: T { pred }` — named refinement (name bound in pred)
    NamedRefine(String, Box<TypeRef>, Box<Expr>),
}

// ── Entity Declarations ──────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct EntityDecl {
    pub name: String,
    pub visibility: Visibility,
    pub items: Vec<EntityItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum EntityItem {
    Field(FieldDecl),
    Action(EntityAction),
    /// a `derived NAME = EXPR` declaration on an
    /// entity. The body is an arbitrary pure expression that closes
    /// over the entity instance state.
    Derived(DerivedDecl),
    /// an `invariant NAME { EXPR }` declaration
    /// on an entity. The body is a Boolean expression that must hold
    /// in every reachable state for every instance of the entity.
    Invariant(InvariantDecl),
    /// an `fsm FIELD { ROWS }` declaration on an
    /// entity. The field name picks an existing enum-typed field on
    /// the entity; rows declare the legal transition table. Per Item
    /// 50, fsm declarations are entity-only — there is no system-level
    /// counterpart.
    Fsm(FsmDecl),
    Error(ErrorNode),
}

/// a finite-state-machine declaration attached to
/// an entity field. The `field` name resolves (in elab) to a field of
/// the containing entity; the field's type must be an enum. Each row
/// names one source state and zero or more target states; a row with
/// zero targets denotes a terminal state ().
#[derive(Debug, Clone)]
pub struct FsmDecl {
    pub field: String,
    pub rows: Vec<FsmRow>,
    pub span: Span,
}

/// one row of an fsm transition table. `from` is a
/// single source-state atom name (the bare variant identifier without
/// the `@` prefix). `targets` is the right-hand-side list — possibly
/// empty for terminal rows like `@delivered ->`.
#[derive(Debug, Clone)]
pub struct FsmRow {
    pub from: String,
    pub targets: Vec<String>,
    pub span: Span,
}

/// a named invariant declaration. Used inside
/// `EntityItem::Invariant` and `SystemItem::Invariant`. Per /// invariants take no parameters; the parser rejects parameterized
/// forms with `INVARIANT_PARAM_REJECTED`.
#[derive(Debug, Clone)]
pub struct InvariantDecl {
    pub name: String,
    pub body: Expr,
    pub span: Span,
}

/// a `derived` field declaration. Used inside
/// `EntityItem::Derived` and `SystemItem::Derived`. The body is an
/// arbitrary expression — single form (`= expr`) and block form
/// (`= { let x =...;... }`) both produce a single `Expr` since the
/// existing expression parser already handles both.
#[derive(Debug, Clone)]
pub struct DerivedDecl {
    pub name: String,
    pub body: Expr,
    pub span: Span,
}

/// How a field's initial value is specified.
#[derive(Debug, Clone)]
pub enum FieldDefault {
    /// `= expr` — deterministic default
    Value(Expr),
    /// `in { expr, expr,... }` — nondeterministic choice from a finite set
    In(Vec<Expr>),
    /// `where expr` — predicate constraint on the initial value
    Where(Expr),
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeRef,
    pub default: Option<FieldDefault>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EntityAction {
    pub name: String,
    pub ref_params: Vec<Param>,
    pub params: Vec<Param>,
    pub contracts: Vec<Contract>,
    pub body: Vec<Expr>,
    pub span: Span,
}

/// Parameter with a full type reference: `name: Type` (supports generics, refinements, etc.).
#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: TypeRef,
    pub mutable: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Contract {
    Requires {
        expr: Expr,
        span: Span,
    },
    Ensures {
        expr: Expr,
        span: Span,
    },
    Decreases {
        measures: Vec<Expr>,
        star: bool,
        span: Span,
    },
    Invariant {
        expr: Expr,
        span: Span,
    },
}

// ── System Declarations ──────────────────────────────────────────────

/// a `Store<T>` constructor parameter on a system.
/// `system Billing(orders: Store<Order>)` declares that the system
/// depends on a store of Order entities.
#[derive(Debug, Clone)]
pub struct StoreParam {
    pub name: String,
    pub entity_type: String,
    pub span: Span,
}

/// a `store` declaration in an assume or given block.
/// `store orders: Order[0..3]` creates a named entity pool with bounded size.
#[derive(Debug, Clone)]
pub struct StoreDecl {
    pub name: String,
    pub entity_type: String,
    pub lo: i64,
    pub hi: i64,
    pub span: Span,
}

/// a proc pool bound declaration in a verify assume block.
/// `proc shop.fulfill[0..3]` bounds the hidden proc-instance pool used
/// when verifying `shop.fulfill`.
#[derive(Debug, Clone)]
pub struct ProcBoundDecl {
    pub path: EventPath,
    pub lo: i64,
    pub hi: i64,
    pub span: Span,
}

/// a `let` binding in an assume or given block.
/// `let billing = Billing { orders: orders }` instantiates a system
/// with store bindings.
#[derive(Debug, Clone)]
pub struct LetBindingDecl {
    pub name: String,
    pub system_type: String,
    pub fields: Vec<(String, String)>,
    pub span: Span,
}

/// an `activate` declaration in a scene given block.
/// `activate {o1} in orders` pre-configures named entity instances
/// in a store.
#[derive(Debug, Clone)]
pub struct ActivateDecl {
    pub instances: Vec<String>,
    pub store_name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct SystemDecl {
    pub name: String,
    /// constructor parameters — `system S(x: Store<E>)`.
    /// Empty for flat-state systems with no entity dependencies.
    pub params: Vec<StoreParam>,
    /// Optional abstract capability contract implemented by this system.
    pub implements: Option<String>,
    pub items: Vec<SystemItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct InterfaceDecl {
    pub name: String,
    pub items: Vec<InterfaceItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExternDecl {
    pub name: String,
    pub items: Vec<ExternItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum InterfaceItem {
    Command(CommandDecl),
    QuerySig(QuerySigDecl),
    Error(ErrorNode),
}

#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum ExternItem {
    Command(CommandDecl),
    May(MayDecl),
    Assume(ExternAssumeBlock),
    Error(ErrorNode),
}

#[derive(Debug, Clone)]
pub struct MayDecl {
    pub command: String,
    pub returns: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExternAssumeBlock {
    pub items: Vec<ExternAssumeItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExternAssumeItem {
    Fair { path: EventPath, span: Span },
    StrongFair { path: EventPath, span: Span },
    Expr { expr: Expr, span: Span },
}

/// Abstract read-only observation signature on an interface.
#[derive(Debug, Clone)]
pub struct QuerySigDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: TypeRef,
    pub span: Span,
}

/// R4: a `program` is the composition root. It has Store<T> params,
/// `let` bindings for system instantiation, and invariants.
/// Programs have no commands/steps/queries. They serve as the top-level
/// coordination point and can be targeted by `theorem t for MyProgram`.
#[derive(Debug, Clone)]
pub struct ProgramDecl {
    pub name: String,
    /// Constructor parameters — `program P(x: Store<E>)`.
    pub params: Vec<StoreParam>,
    pub items: Vec<ProgramItem>,
    pub span: Span,
}

/// Items legal inside a `program` block: let bindings, invariants, and procs.
#[derive(Debug, Clone)]
pub enum ProgramItem {
    Let(LetBindingDecl),
    UseProc(ProcUseDecl),
    Invariant(InvariantDecl),
    Proc(ProcDecl),
    Error(ErrorNode),
}

#[derive(Debug, Clone)]
pub struct ProcUseDecl {
    pub proc_name: String,
    pub args: Vec<String>,
    pub alias: Option<String>,
    pub span: Span,
}

/// Proc declaration: a named DAG of command invocations with dependency edges.
#[derive(Debug, Clone)]
pub struct ProcDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub requires: Option<Expr>,
    pub items: Vec<ProcItem>,
    pub span: Span,
}

/// Items inside a proc body.
#[derive(Debug, Clone)]
pub enum ProcItem {
    /// Node declaration: `charge = billing.charge(order)`
    Node {
        name: String,
        instance: String,
        command: String,
        args: Vec<Expr>,
        span: Span,
    },
    /// Dependency condition: `reserve needs charge.ok and pack.ok`
    NeedsEdge {
        target: String,
        condition: ProcDepCond,
        span: Span,
    },
    /// Static proc composition: `use child(order) as flow`
    UseProc(ProcUseDecl),
    Error(ErrorNode),
}

/// Restricted proc dependency condition syntax accepted after `needs`.
#[derive(Debug, Clone)]
pub enum ProcDepCond {
    Fact {
        node: String,
        qualifier: Option<String>,
    },
    Not(Box<ProcDepCond>),
    And(Box<ProcDepCond>, Box<ProcDepCond>),
    Or(Box<ProcDepCond>, Box<ProcDepCond>),
}

#[derive(Debug, Clone)]
pub enum SystemItem {
    Field(FieldDecl),
    Dep(DepDecl),
    Command(CommandDecl),
    Step(StepDecl),
    Query(QueryDecl),
    /// System-internal predicate (). Not cross-system callable.
    Pred(PredDecl),
    /// an `fsm FIELD { ROWS }` declaration on a
    /// direct system field. This remains a narrow field-lifecycle
    /// contract, not a workflow/process construct.
    Fsm(FsmDecl),
    Derived(DerivedDecl),
    Invariant(InvariantDecl),
    Error(ErrorNode),
}

#[derive(Debug, Clone)]
pub struct DepDecl {
    pub name: String,
    pub span: Span,
}

/// Public API declaration on a system. The cross-system callable surface.
/// Commands are what `saw` references and what procs/scenes invoke.
#[derive(Debug, Clone)]
pub struct CommandDecl {
    pub name: String,
    pub params: Vec<Param>,
    /// Optional return/outcome type: `command charge(o: Order) -> ChargeOutcome`
    pub return_type: Option<TypeRef>,
    /// Optional executable clause body for system commands. Interface and
    /// extern commands remain declaration-only.
    pub body: Option<CommandBodyDecl>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CommandBodyDecl {
    pub contracts: Vec<Contract>,
    pub items: Vec<EventItem>,
    /// Optional return expression: `return @ok(...)`
    pub return_expr: Option<Expr>,
    pub span: Span,
}

/// Internal guarded transition clause that realizes a command.
/// Multiple steps with different `requires` guards can implement
/// the same command (multi-clause dispatch).
#[derive(Debug, Clone)]
pub struct StepDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub contracts: Vec<Contract>,
    pub items: Vec<EventItem>,
    /// Optional return expression: `return @ok(Receipt {... })`
    pub return_expr: Option<Expr>,
    pub span: Span,
}

/// Public read-only observation on a system. The public counterpart
/// to `pred` (which stays internal).
#[derive(Debug, Clone)]
pub struct QueryDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum EventItem {
    Choose(ChooseBlock),
    For(ForBlock),
    Create(CreateBlock),
    LetCall(EventLetCall),
    Match(EventMatchBlock),
    Expr(Expr),
    Error(ErrorNode),
}

#[derive(Debug, Clone)]
pub struct EventLetCall {
    pub name: String,
    pub system: String,
    pub command: String,
    pub args: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EventMatchBlock {
    pub scrutinee: EventMatchScrutinee,
    pub arms: Vec<EventMatchArm>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum EventMatchScrutinee {
    Var(String, Span),
    Call {
        system: String,
        command: String,
        args: Vec<Expr>,
        span: Span,
    },
}

impl EventMatchScrutinee {
    pub fn span(&self) -> Span {
        match self {
            Self::Var(_, span) => *span,
            Self::Call { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct EventMatchArm {
    pub pattern: Pattern,
    pub guard: Option<Box<Expr>>,
    pub items: Vec<EventItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ChooseBlock {
    pub var: String,
    pub ty: String,
    pub condition: Expr,
    pub body: Vec<EventItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ForBlock {
    pub var: String,
    pub ty: String,
    pub body: Vec<EventItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CreateBlock {
    pub ty: String,
    /// Optional store target: `create User in users {... }`.
    /// When present, indicates which store the entity is created in.
    pub store: Option<String>,
    pub fields: Vec<CreateField>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CreateField {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

// ── Predicates and Properties ────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct PredDecl {
    pub name: String,
    pub visibility: Visibility,
    pub params: Vec<Param>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct PropDecl {
    pub name: String,
    pub visibility: Visibility,
    pub systems: Vec<String>,
    pub body: Expr,
    pub span: Span,
}

// ── Verification ─────────────────────────────────────────────────────

/// `assume {... }` block on a verify/theorem/lemma construct
/// ( REPLACED, unified `assume` contract). Carries
/// fairness annotations and the stutter opt-in/out flag.
///
/// only parses this; normalizes it into an `AssumptionSet`
/// and wires it into the verifier.
#[derive(Debug, Clone)]
pub struct AssumeBlock {
    pub items: Vec<AssumeItem>,
    pub span: Span,
}

/// Individual item inside an `assume { }` block.
#[derive(Debug, Clone)]
pub enum AssumeItem {
    /// `fair Sys::event` — weak fairness on the named event.
    Fair { path: EventPath, span: Span },
    /// `strong fair Sys::event` — strong fairness on the named event.
    StrongFair { path: EventPath, span: Span },
    /// `stutter` — opt-in to stutter steps for this verification site.
    Stutter { span: Span },
    /// `no stutter` — opt-out of stutter steps for this verification site.
    NoStutter { span: Span },
    /// `store name: Type[lo..hi]` — named store
    /// declaration inside assume/given blocks.
    Store(StoreDecl),
    /// `proc path[lo..hi]` — hidden proc-instance pool bound.
    Proc(ProcBoundDecl),
    /// `let name = SystemType { field: store,... }`
    /// — system instantiation via let binding in assume/given blocks.
    Let(LetBindingDecl),
}

/// A reference to an event in an `assume { }` block. stores the
/// raw segments; resolves these to actual events.
#[derive(Debug, Clone)]
pub struct EventPath {
    /// Path segments, e.g. `["Commerce", "mark_paid"]` or `["mark_paid"]`.
    pub segments: Vec<String>,
    pub span: Span,
}

/// verify blocks no longer use `for System[0..N]`.
/// Stores and let bindings live inside the assume block.
#[derive(Debug, Clone)]
pub struct VerifyDecl {
    pub name: String,
    /// Optional BMC depth override: `verify name [depth: N] {... }`
    pub depth: Option<usize>,
    /// `assume { store...; let...; fair X; stutter;... }` block.
    pub assume_block: Option<AssumeBlock>,
    pub asserts: Vec<Expr>,
    pub span: Span,
}

// ── Theorem Blocks () ─────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct TheoremDecl {
    pub name: String,
    pub systems: Vec<String>,
    /// `assume { fair X;... }` block. See `VerifyDecl::assume_block`.
    pub assume_block: Option<AssumeBlock>,
    pub invariants: Vec<Expr>,
    pub shows: Vec<Expr>,
    pub by_file: Option<String>,
    /// lemma references introduced by a `by L1, L2,...`
    /// body item in block-form theorems. The compiler enforces subset
    /// containment between the theorem's effective `AssumptionSet` and
    /// each referenced lemma's effective `AssumptionSet` ().
    pub by_lemmas: Vec<ByLemmaRef>,
    pub span: Span,
}

/// a single lemma reference in a `by L1, L2,...`
/// body item. Carries a multi-segment path (`Mod::name` qualified or
/// bare `name`) parallel to `EventPath`, so resolution can route
/// through the canonical declaration registry rather than a hand-rolled
/// bare-name table. The span covers the entire path for diagnostics.
#[derive(Debug, Clone)]
pub struct ByLemmaRef {
    pub segments: Vec<String>,
    pub span: Span,
}

/// an `under { ITEMS }` block grouping theorems
/// and lemmas that share the same proof environment. The body items
/// reuse `AssumeItem` (Variant A: same shape as an `assume { }` block,
/// but at the top level without the `assume` keyword).
///
/// Theorems and lemmas inside the under block inherit its assumption
/// set as the *floor* of their environment (add-only inheritance).
/// Per-construct `assume { }` blocks may extend the floor but never
/// weaken it.
#[derive(Debug, Clone)]
pub struct UnderBlock {
    pub items: Vec<AssumeItem>,
    pub theorems: Vec<TheoremDecl>,
    pub lemmas: Vec<LemmaDecl>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LemmaDecl {
    pub name: String,
    /// `assume { fair X;... }` block. See `VerifyDecl::assume_block`.
    pub assume_block: Option<AssumeBlock>,
    pub body: Vec<Expr>,
    pub span: Span,
}

// ── Axiom Declarations () ─────────────────────────────────────

#[derive(Debug, Clone)]
pub struct AxiomDecl {
    pub name: String,
    pub body: Expr,
    pub by_file: Option<String>,
    pub span: Span,
}

// ── Scene Blocks ─────────────────────────────────────────────────────

/// scene blocks no longer use `for System`.
/// Stores and let bindings live inside given blocks.
#[derive(Debug, Clone)]
pub struct SceneDecl {
    pub name: String,
    pub items: Vec<SceneItem>,
    pub span: Span,
}

/// scene items simplified. Old inline Given/WhenAction
/// removed; everything goes through block forms.
#[derive(Debug, Clone)]
pub enum SceneItem {
    WhenAssume { expr: Expr, span: Span },
    ThenAssert { expr: Expr, span: Span },
    GivenBlock { items: Vec<GivenItem>, span: Span },
    WhenBlock { items: Vec<WhenItem>, span: Span },
    ThenBlock { items: Vec<ThenItem>, span: Span },
    Error(ErrorNode),
}

/// extended given item supporting store, let,
/// activate, and entity bindings.
#[derive(Debug, Clone)]
pub enum GivenItem {
    /// `let x = one Entity [in store] [where cond]` — entity binding
    EntityBinding {
        name: String,
        entity_type: String,
        store_name: Option<String>,
        condition: Option<Expr>,
        span: Span,
    },
    /// `store name: Type[lo..hi]` — store declaration in given block
    Store(StoreDecl),
    /// `let name = System { field: store,... }` — system instantiation
    Let(LetBindingDecl),
    /// `activate {instances} in store` — entity pre-configuration
    Activate(ActivateDecl),
    /// `expr` — constraint expression (e.g., `o1.status = 0`)
    Constraint {
        expr: Expr,
        span: Span,
    },
    Error(ErrorNode),
}

/// scene when items use instance-qualified calls.
/// `billing.charge(o)` instead of `action a = Billing::charge(o){one}`.
#[derive(Debug, Clone)]
pub enum WhenItem {
    /// `instance.command(args)` — instance-qualified call
    InstanceCall {
        instance: String,
        command: String,
        args: Vec<InvocArg>,
        card: Option<String>,
        span: Span,
    },
    /// `let name = instance.command(args){card}` — bind a scene event family
    LetCall {
        name: String,
        instance: String,
        command: String,
        args: Vec<InvocArg>,
        card: Option<String>,
        span: Span,
    },
    Assume {
        expr: Expr,
        span: Span,
    },
    Error(ErrorNode),
}

#[derive(Debug, Clone)]
pub struct ActionInvoc {
    pub qualifier: Option<String>,
    pub name: String,
    pub args: Vec<InvocArg>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum InvocArg {
    Field {
        obj: String,
        field: String,
        span: Span,
    },
    Simple {
        name: String,
        span: Span,
    },
    Int {
        value: i64,
        span: Span,
    },
    Real {
        value: f64,
        span: Span,
    },
    Float {
        value: String,
        span: Span,
    },
    Str {
        value: String,
        span: Span,
    },
    State {
        name: String,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub enum CardValue {
    One,
    Lone,
    Some,
    No,
    Num(i64),
}

#[derive(Debug, Clone)]
pub struct ThenItem {
    pub expr: Expr,
    pub span: Span,
}

// ── Expressions ──────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// Kind of arithmetic aggregator (, ).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AggKind {
    Sum,
    Product,
    Min,
    Max,
    Count,
}

/// Argument in a `saw E::f(arg,...)` expression.
/// `Wild` matches any value; `Expr(e)` matches the value of `e`.
#[derive(Debug, Clone)]
pub enum SawArg {
    Wild(Span),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Error(ErrorNode),
    // Level 0: composition, pipe
    Pipe(Box<Expr>, Box<Expr>),
    Unord(Box<Expr>, Box<Expr>),
    Conc(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    NamedPair(String, Box<Expr>),

    // Level 1: sequence
    Seq(Box<Expr>, Box<Expr>),

    // Level 2: same-step
    SameStep(Box<Expr>, Box<Expr>),

    // Level 3: implies, temporal, quantifiers, let, lambda
    Impl(Box<Expr>, Box<Expr>),
    Always(Box<Expr>),
    Eventually(Box<Expr>),
    Until(Box<Expr>, Box<Expr>),
    /// `historically P` — P held at every past state
    /// (including the current one). Past-time dual of `always`.
    Historically(Box<Expr>),
    /// `once P` — P held at some past state (including the
    /// current one). Past-time dual of `eventually`.
    Once(Box<Expr>),
    /// `previously P` — P held in the immediately previous
    /// state. False at trace position 0. Past-time dual of `next`.
    Previously(Box<Expr>),
    /// `P since Q` — Q held at some past state and P held
    /// continuously from that point to now. Past-time dual of `until`.
    Since(Box<Expr>, Box<Expr>),
    /// `sum x: T | expr` or `sum x in coll | expr` —.
    /// Aggregate(kind, var, domain, in_expr, body)
    /// `in_expr` is Some when `in collection` restricts the domain.
    Aggregate(AggKind, String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    /// `saw E::f(args)` — past-time event firing observation.
    /// True at step n iff E::f was fired with matching args at some step ≤ n.
    /// First field: scoped event path segments (e.g., `["Shop", "charge"]`).
    /// Second field: argument expressions (wildcard or value match).
    Saw(Vec<String>, Vec<SawArg>),
    AssertExpr(Box<Expr>),
    AssumeExpr(Box<Expr>),
    /// Quantifiers: `all x: T | body` or `all x: T in coll | body`
    /// or `all x in coll | body` (shorthand, Type inferred).
    /// The optional in_expr restricts the domain to a collection.
    All(String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    Exists(String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    SomeQ(String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    NoQ(String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    OneQ(String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    LoneQ(String, TypeRef, Option<Box<Expr>>, Box<Expr>),
    Let(Vec<LetBind>, Box<Expr>),
    Lambda(Vec<TypedParam>, Box<Expr>),
    LambdaT(Vec<TypedParam>, TypeRef, Box<Expr>),
    Match(Box<Expr>, Vec<MatchArm>),
    Choose(String, TypeRef, Option<Box<Expr>>),

    // Level 4: assignment
    Assign(Box<Expr>, Box<Expr>),

    // Level 5–6: boolean
    Or(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),

    // Level 7: not
    Not(Box<Expr>),

    // Level 8: equality, membership
    Eq(Box<Expr>, Box<Expr>),
    NEq(Box<Expr>, Box<Expr>),
    In(Box<Expr>, Box<Expr>),

    // Level 9: comparison
    Lt(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),

    // Level 10: additive
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),

    // Level 11: multiplicative
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    /// `a <> b` — set union, seq concat, map merge (type-directed)
    Diamond(Box<Expr>, Box<Expr>),
    /// `a !* b` — set disjointness
    Disjoint(Box<Expr>, Box<Expr>),

    // Level 12: unary
    Neg(Box<Expr>),
    Card(Box<Expr>),

    // Level 13: postfix
    Prime(Box<Expr>),
    Field(Box<Expr>, String),
    CallR(Box<Expr>, Vec<Expr>, Vec<Expr>),
    Call(Box<Expr>, Vec<Expr>),

    // Map/collection operations
    /// Map update: m[k:= v] — produces new map
    MapUpdate(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Index access: m[k] — reads from map/seq
    Index(Box<Expr>, Box<Expr>),
    /// Set comprehension: { expr | var: Type where filter } or { var: Type where filter }
    SetComp {
        projection: Option<Box<Expr>>,
        var: String,
        domain: TypeRef,
        filter: Box<Expr>,
    },

    // Imperative constructs (fn body)
    Block(Vec<Expr>),
    VarDecl {
        name: String,
        ty: Option<TypeRef>,
        init: Box<Expr>,
    },
    While {
        cond: Box<Expr>,
        contracts: Vec<Contract>,
        body: Box<Expr>,
    },
    IfElse {
        cond: Box<Expr>,
        then_body: Box<Expr>,
        else_body: Option<Box<Expr>>,
    },

    // Struct constructor: Name { field: expr,... }
    StructCtor(String, Vec<(String, Expr)>),

    // Level 14: atoms
    State1(String),
    /// @Name { field: expr,... } — constructor with fields
    State1Record(String, Vec<(String, Expr)>),
    State2(String, String),
    /// @`Enum::Name` { field: expr,... } — qualified constructor with fields
    State2Record(String, String, Vec<(String, Expr)>),
    State3(String, String, String),
    Qual2(String, String),
    Qual3(String, String, String),
    TupleLit(Vec<Expr>),
    Var(String),
    Int(i64),
    Real(f64),
    Float(String),
    Str(String),
    True,
    False,
    Sorry,
    Todo,
}

#[derive(Debug, Clone)]
pub struct LetBind {
    pub name: String,
    pub ty: Option<TypeRef>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Box<Expr>>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    /// Variable or simple constructor name (disambiguated during elaboration)
    Var(String, Span),
    /// Record constructor: `Name { field: pat,... }` with optional `..`
    Ctor(String, Vec<FieldPat>, bool, Span),
    /// Wildcard: `_`
    Wild(Span),
    /// Or-pattern: `P1 | P2`
    Or(Box<Pattern>, Box<Pattern>, Span),
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Var(_, s)
            | Pattern::Wild(s)
            | Pattern::Ctor(_, _, _, s)
            | Pattern::Or(_, _, s) => *s,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FieldPat {
    pub name: String,
    pub pattern: Pattern,
    pub span: Span,
}
