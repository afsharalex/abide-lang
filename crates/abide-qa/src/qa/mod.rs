//! QA (Query Abide) — structural analysis of specifications.
//!
//! Extracts a `FlowModel` from IR (state graphs, transitions, reachability)
//! and provides graph-based queries. No SMT — microsecond response times.

pub mod artifacts;
pub mod ast;
pub mod exec;
pub mod extract;
pub mod fmt;
pub mod graph;
pub mod model;
pub mod parse;
pub mod runner;
