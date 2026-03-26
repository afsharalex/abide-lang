use crate::span::Span;

// ── Program ──────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: Vec<TopDecl>,
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
    Entity(EntityDecl),
    System(SystemDecl),
    Pred(PredDecl),
    Prop(PropDecl),
    Verify(VerifyDecl),
    Theorem(TheoremDecl),
    Lemma(LemmaDecl),
    Scene(SceneDecl),
    Axiom(AxiomDecl),
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
    pub variants: Vec<TypeVariant>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypeVariant {
    Simple {
        name: String,
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
    /// `(A, B, ...)` — 2+ elements
    Tuple(Vec<TypeRef>),
    /// `(A)` — grouping
    Paren(Box<TypeRef>),
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
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeRef,
    pub default: Option<Expr>,
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

/// Simple parameter: `name: TypeName` (name-only types, not full `TypeRef`).
#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Contract {
    Requires { expr: Expr, span: Span },
    Ensures { expr: Expr, span: Span },
}

// ── System Declarations ──────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct SystemDecl {
    pub name: String,
    pub items: Vec<SystemItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum SystemItem {
    Uses(String, Span),
    Event(EventDecl),
    Next(NextBlock),
}

#[derive(Debug, Clone)]
pub struct EventDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub contracts: Vec<Contract>,
    pub items: Vec<EventItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum EventItem {
    Choose(ChooseBlock),
    For(ForBlock),
    Create(CreateBlock),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct ChooseBlock {
    pub var: String,
    pub ty: String,
    pub condition: Expr,
    pub body: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ForBlock {
    pub var: String,
    pub ty: String,
    pub body: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CreateBlock {
    pub ty: String,
    pub fields: Vec<CreateField>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CreateField {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct NextBlock {
    pub items: Vec<NextItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum NextItem {
    When {
        condition: Expr,
        event: Expr,
        span: Span,
    },
    Else(Span),
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

#[derive(Debug, Clone)]
pub struct VerifyDecl {
    pub name: String,
    pub targets: Vec<VerifyTarget>,
    pub asserts: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct VerifyTarget {
    pub system: String,
    pub min: i64,
    pub max: i64,
    pub span: Span,
}

// ── Theorem Blocks (DDR-032) ─────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct TheoremDecl {
    pub name: String,
    pub systems: Vec<String>,
    pub invariants: Vec<Expr>,
    pub shows: Vec<Expr>,
    pub by_file: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LemmaDecl {
    pub name: String,
    pub body: Vec<Expr>,
    pub span: Span,
}

// ── Axiom Declarations (DDR-032) ─────────────────────────────────────

#[derive(Debug, Clone)]
pub struct AxiomDecl {
    pub name: String,
    pub body: Expr,
    pub by_file: Option<String>,
    pub span: Span,
}

// ── Scene Blocks ─────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct SceneDecl {
    pub name: String,
    pub systems: Vec<String>,
    pub items: Vec<SceneItem>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum SceneItem {
    Given {
        name: String,
        qual_type: QualType,
        condition: Option<Expr>,
        span: Span,
    },
    WhenAction {
        name: String,
        invoc: ActionInvoc,
        card: Option<CardValue>,
        span: Span,
    },
    WhenAssume {
        expr: Expr,
        span: Span,
    },
    ThenAssert {
        expr: Expr,
        span: Span,
    },
    GivenBlock {
        items: Vec<GivenItem>,
        span: Span,
    },
    WhenBlock {
        items: Vec<WhenItem>,
        span: Span,
    },
    ThenBlock {
        items: Vec<ThenItem>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct GivenItem {
    pub name: String,
    pub qual_type: QualType,
    pub condition: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum QualType {
    Qualified {
        module: String,
        name: String,
        span: Span,
    },
    Simple {
        name: String,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub enum WhenItem {
    Action {
        name: String,
        invoc: ActionInvoc,
        card: Option<CardValue>,
        span: Span,
    },
    Assume {
        expr: Expr,
        span: Span,
    },
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

#[derive(Debug, Clone)]
pub enum ExprKind {
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
    AssertExpr(Box<Expr>),
    All(String, TypeRef, Box<Expr>),
    Exists(String, TypeRef, Box<Expr>),
    SomeQ(String, TypeRef, Box<Expr>),
    NoQ(String, TypeRef, Box<Expr>),
    OneQ(String, TypeRef, Box<Expr>),
    LoneQ(String, TypeRef, Box<Expr>),
    Let(Vec<LetBind>, Box<Expr>),
    Lambda(Vec<TypedParam>, Box<Expr>),
    LambdaT(Vec<TypedParam>, TypeRef, Box<Expr>),
    Match(Box<Expr>, Vec<MatchArm>),

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

    // Level 12: unary
    Neg(Box<Expr>),
    Card(Box<Expr>),

    // Level 13: postfix
    Prime(Box<Expr>),
    Field(Box<Expr>, String),
    CallR(Box<Expr>, Vec<Expr>, Vec<Expr>),
    Call(Box<Expr>, Vec<Expr>),

    // Level 14: atoms
    State1(String),
    State2(String, String),
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
    /// Record constructor: `Name { field: pat, ... }` with optional `..`
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
