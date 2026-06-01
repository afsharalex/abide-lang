//! Shared core types for the Abide compiler workspace.
//!
//! This crate holds primitives that downstream crates (syntax, sema, ir,
//! verify, witness, qa, lsp) all depend on. It is intentionally small and
//! has no dependencies on the rest of the workspace.
//!
//! - [`span`] — byte-offset spans into source text.
//! - [`diagnostic`] — the cross-crate diagnostic vocabulary, including
//!   [`diagnostic::Diagnostic`], the `miette`-aware lex/parse error
//!   variants, and the [`diagnostic::DiagnosticSink`] that collects them.
//! - [`messages`] — centralized user-facing message strings used by the
//!   parser and elaborator.

pub mod diagnostic;
pub mod messages;
pub mod span;
