//! Abide QA (Query Abide): structural query engine over lowered IR.
//!
//! QA extracts a [`qa::model::FlowModel`] from an [`ir::types::IRProgram`]
//! and exposes a small query language ([`qa::ast`], [`qa::parse`]) for
//! interrogating it. Unlike the SMT-backed verifier, QA queries run at
//! microsecond timescales — they are graph and metadata queries, not
//! semantic ones.
//!
//! Top-level layout:
//! - [`qa::ast`] / [`qa::parse`] — the QA query surface.
//! - [`qa::model`] — the `FlowModel` extracted from IR.
//! - [`qa::extract`] — building the model from IR.
//! - [`qa::graph`] — graph algorithms (reachability, dependencies).
//! - [`qa::exec`] — query execution against a `FlowModel`.
//! - [`qa::fmt`] — pretty-printing results.
//! - [`qa::runner`] — the REPL / batch driver.
//! - [`qa::artifacts`] — serialization of QA results to JSON for
//!   tooling.

pub use abide_ir::ir;
pub use abide_sema::{elab, loader};
pub use abide_syntax::parse;

pub mod qa;
