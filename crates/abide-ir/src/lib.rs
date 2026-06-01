//! Abide intermediate representation (IR).
//!
//! This crate sits below `abide-sema` and above the verification
//! backends. Its job is to turn an elaborated AST
//! ([`abide_sema::elab::types::ElabResult`]) into a flat, name-resolved
//! [`ir::types::IRProgram`] that the verifier (and external consumers
//! like Invaria) can read without needing to re-implement scope rules
//! or surface-syntax desugaring.
//!
//! - [`ir::types`] — the IR data model (declarations, expressions,
//!   types).
//! - [`ir::lower`] — the lowering pass from the elaborated AST.
//! - [`ir::relation`] — the relation-algebra primitives shared between
//!   the relation surface and its lowered form.
//!
//! The shared types re-exported at the crate root keep downstream
//! crates from having to depend on `abide_core`, `abide_sema`, and
//! `abide_syntax` separately.

pub use abide_core::{messages, span};
pub use abide_sema::elab;
pub use abide_syntax::ast;

pub mod ir;
