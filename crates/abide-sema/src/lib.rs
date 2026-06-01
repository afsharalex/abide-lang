//! Abide semantic analysis (elaboration).
//!
//! The elaborator turns the surface AST produced by `abide-syntax`
//! into a fully resolved, typed [`elab::types::ElabResult`] that
//! `abide-ir` lowers further. Most surface-level "magic" (alias
//! resolution, qualified-path lookup, contract scoping, fairness
//! normalization) happens here.
//!
//! Pipeline (within [`elab`]):
//!
//! - [`elab::collect`] — first pass: build symbol tables and stub out
//!   declarations.
//! - [`elab::resolve`] — second pass: resolve names, qualifiers, and
//!   assumption sets.
//! - [`elab::check`] — third pass: type-check expressions, contracts,
//!   match exhaustiveness, FSM declarations, etc.
//! - [`elab::env`] — the typing environment threaded through resolve
//!   and check.
//! - [`elab::types`] — the resolved AST data model produced by the
//!   elaborator and consumed by `abide-ir`.
//! - [`elab::error`] — elaborator-specific error codes and helpers.
//!
//! [`loader`] is the small file-loading wrapper used to find and read
//! `module`/`include` dependencies.

pub use abide_core::{diagnostic, messages, span};
pub use abide_syntax::{ast, lex, parse};

pub mod elab;
pub mod loader;
