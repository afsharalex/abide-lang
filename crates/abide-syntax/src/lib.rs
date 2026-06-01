//! Abide surface syntax: lexer, parser, and AST.
//!
//! The hand-rolled parser in [`parse`] is the canonical grammar for
//! Abide — there is no separately maintained BNF or LBNF
//! specification. AST nodes in [`ast`] are intentionally close to the
//! surface form; desugaring happens later in `abide-sema`/`abide-ir`.
//!
//! - [`lex`] — tokeniser producing a span-tagged token stream.
//! - [`ast`] — public AST types (declarations, statements, expressions,
//!   types).
//! - [`parse`] — entry points returning `(Module, Diagnostics)`.

pub use abide_core::{diagnostic, messages, span};

pub mod ast;
pub mod lex;
pub mod parse;
