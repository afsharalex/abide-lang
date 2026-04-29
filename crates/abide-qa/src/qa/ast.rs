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
    /// `abide {... }` — inline Abide code block (hypothetical extension)
    AbideBlock(String),
    /// `verify` — run verification and store evidence-bearing artifacts
    Verify,
    /// `simulate [options]` — run one seeded forward simulation and store it as an artifact
    Simulate(SimulationRequest),
    /// `explore [options]` — build a bounded composite state-space artifact
    Explore(StateSpaceRequest),
    /// `artifacts` — list stored artifacts from earlier `verify` statements
    Artifacts,
    /// `show artifact <selector>` — show artifact summary
    ShowArtifact(String),
    /// `draw artifact <selector>` — draw artifact timeline
    DrawArtifact(String),
    /// `state artifact <selector> <index>` — inspect one artifact state
    StateArtifact { selector: String, index: usize },
    /// `diff artifact <selector> <from> <to>` — compare two artifact states
    DiffArtifact {
        selector: String,
        from: usize,
        to: usize,
    },
    /// `export artifact <selector> <format>` — export one artifact
    ExportArtifact { selector: String, format: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimulationRequest {
    pub steps: usize,
    pub seed: u64,
    pub slots: usize,
    pub scopes: Vec<(String, usize)>,
    pub system: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateSpaceRequest {
    pub depth: Option<usize>,
    pub slots: usize,
    pub scopes: Vec<(String, usize)>,
    pub system: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TemporalBounds {
    pub slots: Option<usize>,
    pub scopes: Vec<(String, usize)>,
}

impl TemporalBounds {
    pub fn is_empty(&self) -> bool {
        self.slots.is_none() && self.scopes.is_empty()
    }
}

impl Default for SimulationRequest {
    fn default() -> Self {
        Self {
            steps: 25,
            seed: 0,
            slots: 4,
            scopes: Vec::new(),
            system: None,
        }
    }
}

impl Default for StateSpaceRequest {
    fn default() -> Self {
        Self {
            depth: None,
            slots: 4,
            scopes: Vec::new(),
            system: None,
        }
    }
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
    /// `fsms on E` — list every fsm field on
    /// the named owner (entity or system). Reads lowered fsm metadata directly.
    Fsms { entity: String },
    /// `transitions of E::field` — list the
    /// declared transition table for one fsm. Distinct from the
    /// existing `Transitions` query, which filters action-extracted
    /// transitions by source state; this one returns the full
    /// declared table for the fsm.
    FsmTransitions { entity: String, field: String },
    /// `terminal states of E::field` — list the
    /// inferred terminal states from the declared fsm table.
    FsmTerminalStates { entity: String, field: String },
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
    /// `always [on Target] (expr)` / `eventually [on Target] (expr)` —
    /// temporal assertions over an explicit or inferred scope target.
    Temporal {
        op: TemporalOp,
        bounds: TemporalBounds,
        target: Option<TemporalTarget>,
        expr: String,
    },

    // ── Block-form queries ──────────────────────────────────────
    /// `{ for e, f, s where pred(e, f, s) [not pred(...)] select e, f, s }`
    Block {
        bindings: Vec<String>,
        predicates: Vec<BlockPredicate>,
        select: Vec<String>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemporalOp {
    Always,
    Eventually,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalTarget {
    pub owner: String,
    pub field: Option<String>,
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
            Self::Verify => write!(f, "verify"),
            Self::Simulate(request) => write!(f, "{request}"),
            Self::Explore(request) => write!(f, "{request}"),
            Self::Artifacts => write!(f, "artifacts"),
            Self::ShowArtifact(selector) => write!(f, "show artifact {selector}"),
            Self::DrawArtifact(selector) => write!(f, "draw artifact {selector}"),
            Self::StateArtifact { selector, index } => {
                write!(f, "state artifact {selector} {index}")
            }
            Self::DiffArtifact { selector, from, to } => {
                write!(f, "diff artifact {selector} {from} {to}")
            }
            Self::ExportArtifact { selector, format } => {
                write!(f, "export artifact {selector} {format}")
            }
        }
    }
}

impl std::fmt::Display for SimulationRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "simulate --steps {} --seed {} --slots {}",
            self.steps, self.seed, self.slots
        )?;
        for (entity, slots) in &self.scopes {
            write!(f, " --scope {entity}={slots}")?;
        }
        if let Some(system) = &self.system {
            write!(f, " --system {system}")?;
        }
        Ok(())
    }
}

impl std::fmt::Display for StateSpaceRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "explore")?;
        if let Some(depth) = self.depth {
            write!(f, " --depth {depth}")?;
        }
        write!(f, " --slots {}", self.slots)?;
        for (entity, slots) in &self.scopes {
            write!(f, " --scope {entity}={slots}")?;
        }
        if let Some(system) = &self.system {
            write!(f, " --system {system}")?;
        }
        Ok(())
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
            Self::Fsms { entity } => write!(f, "fsms on {entity}"),
            Self::FsmTransitions { entity, field } => {
                write!(f, "transitions of {entity}::{field}")
            }
            Self::FsmTerminalStates { entity, field } => {
                write!(f, "terminal states of {entity}::{field}")
            }
            Self::Events { entity, field } => write!(f, "events on {entity}.{field}"),
            Self::MatchCoverage { entity, field } => write!(f, "match-coverage {entity}.{field}"),
            Self::CrossCalls { system } => write!(f, "cross-calls from {system}"),
            Self::Deadlock { system } => write!(f, "deadlock {system}"),
            Self::Not(inner) => write!(f, "not {inner}"),
            Self::Temporal {
                op,
                bounds,
                target,
                expr,
            } => {
                let op = match op {
                    TemporalOp::Always => "always",
                    TemporalOp::Eventually => "eventually",
                };
                if !bounds.is_empty() {
                    write!(f, "{op}")?;
                    if let Some(slots) = bounds.slots {
                        write!(f, " --slots {slots}")?;
                    }
                    for (entity, slots) in &bounds.scopes {
                        write!(f, " --scope {entity}={slots}")?;
                    }
                    if let Some(target) = target {
                        write!(f, " on {target} {expr}")
                    } else {
                        write!(f, " {expr}")
                    }
                } else if let Some(target) = target {
                    write!(f, "{op} on {target} {expr}")
                } else {
                    write!(f, "{op} {expr}")
                }
            }
            Self::Block { .. } => write!(f, "block query"),
        }
    }
}

impl std::fmt::Display for TemporalTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(field) = &self.field {
            write!(f, "{}.{field}", self.owner)
        } else {
            write!(f, "{}", self.owner)
        }
    }
}
