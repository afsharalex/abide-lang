//! QA language AST — statements and queries for structural analysis.

/// A top-level QA statement.
#[derive(Debug, Clone, PartialEq)]
pub enum QAStatement {
    /// `ask <query>` — query, print result
    Ask(Query),
    /// `explain <query>` — query with reasoning trace
    Explain(Query),
    /// `assert <query>` — query, fail if false (CI gate)
    Assert(Query),
    /// `load "path"` — load specs from file or directory
    Load(String),
    /// `abide { ... }` — inline Abide code block (hypothetical extension)
    AbideBlock(String),
}

/// A QA query.
#[derive(Debug, Clone, PartialEq)]
pub enum Query {
    // ── Structural queries (entity state machines) ──────────────
    /// `reachable E.field -> @State`
    Reachable {
        entity: String,
        field: String,
        state: String,
    },
    /// `path E.field @From -> @To`
    Path {
        entity: String,
        field: String,
        from: String,
        to: String,
    },
    /// `terminal E.field`
    Terminal { entity: String, field: String },
    /// `initial E.field`
    Initial { entity: String, field: String },
    /// `cycles E.field`
    Cycles { entity: String, field: String },
    /// `transitions from E.field == @State`
    Transitions {
        entity: String,
        field: String,
        state: String,
    },
    /// `updates on E.field @From -> @To`
    Updates {
        entity: String,
        field: String,
        from: String,
        to: String,
    },

    // ── Discovery queries ───────────────────────────────────────
    /// `entities`
    Entities,
    /// `systems`
    Systems,
    /// `types`
    Types,
    /// `invariants on E`
    Invariants { entity: String },
    /// `contracts on E.action`
    Contracts { entity: String, action: String },
    /// `events on E.field`
    Events { entity: String, field: String },
    /// `match-coverage E.field`
    MatchCoverage { entity: String, field: String },
    /// `cross-calls from System`
    CrossCalls { system: String },
    /// `deadlock System`
    Deadlock { system: String },

    // ── Modifiers ───────────────────────────────────────────────
    /// `not <query>` — negation
    Not(Box<Query>),
    /// `always (expr)` / `eventually (expr)` — temporal assertions
    /// Delegates to Abide expression parsing
    AlwaysExpr(String),
    /// `eventually (expr)`
    EventuallyExpr(String),

    // ── Block-form queries ──────────────────────────────────────
    /// `{ for e, f, s where pred(e, f, s) [not pred(...)] select e, f, s }`
    Block {
        bindings: Vec<String>,
        predicates: Vec<BlockPredicate>,
        select: Vec<String>,
    },
}

/// A relational predicate in a block-form query.
#[derive(Debug, Clone, PartialEq)]
pub struct BlockPredicate {
    /// Whether this predicate is negated (`not`).
    pub negated: bool,
    /// The predicate name: `state`, `transition`, `initial`, `terminal`,
    /// `invariant`, `event`, `cross_call`.
    pub name: String,
    /// Arguments (variable names or named args like `from: s1`).
    pub args: Vec<BlockArg>,
}

/// An argument in a block predicate.
#[derive(Debug, Clone, PartialEq)]
pub enum BlockArg {
    /// Positional: just a variable name
    Positional(String),
    /// Named: `from: s1`, `to: s2`
    Named(String, String),
}

impl std::fmt::Display for QAStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ask(q) => write!(f, "ask {q}"),
            Self::Explain(q) => write!(f, "explain {q}"),
            Self::Assert(q) => write!(f, "assert {q}"),
            Self::Load(path) => write!(f, "load \"{path}\""),
            Self::AbideBlock(_) => write!(f, "abide {{ ... }}"),
        }
    }
}

impl std::fmt::Display for Query {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Reachable {
                entity,
                field,
                state,
            } => {
                write!(f, "reachable {entity}.{field} -> @{state}")
            }
            Self::Path {
                entity,
                field,
                from,
                to,
            } => {
                write!(f, "path {entity}.{field} @{from} -> @{to}")
            }
            Self::Terminal { entity, field } => write!(f, "terminal {entity}.{field}"),
            Self::Initial { entity, field } => write!(f, "initial {entity}.{field}"),
            Self::Cycles { entity, field } => write!(f, "cycles {entity}.{field}"),
            Self::Transitions {
                entity,
                field,
                state,
            } => {
                write!(f, "transitions from {entity}.{field} == @{state}")
            }
            Self::Updates {
                entity,
                field,
                from,
                to,
            } => {
                write!(f, "updates on {entity}.{field} @{from} -> @{to}")
            }
            Self::Entities => write!(f, "entities"),
            Self::Systems => write!(f, "systems"),
            Self::Types => write!(f, "types"),
            Self::Invariants { entity } => write!(f, "invariants on {entity}"),
            Self::Contracts { entity, action } => write!(f, "contracts on {entity}.{action}"),
            Self::Events { entity, field } => write!(f, "events on {entity}.{field}"),
            Self::MatchCoverage { entity, field } => write!(f, "match-coverage {entity}.{field}"),
            Self::CrossCalls { system } => write!(f, "cross-calls from {system}"),
            Self::Deadlock { system } => write!(f, "deadlock {system}"),
            Self::Not(inner) => write!(f, "not {inner}"),
            Self::AlwaysExpr(expr) => write!(f, "always {expr}"),
            Self::EventuallyExpr(expr) => write!(f, "eventually {expr}"),
            Self::Block { .. } => write!(f, "block query"),
        }
    }
}
