// Crate-level clippy allows. These cover style lints that the codebase has
// historically tolerated via scattered `#[allow]` attributes — consolidating
// them here keeps `cargo clippy --tests -- -D warnings` clean without
// changing established conventions:
// * `too_many_lines` / `too_many_arguments` — large compiler/verifier
// functions are intentionally flat for review and trace-ability.
// * `match_same_arms` — verifier and elab match arms are kept distinct
// for documentation even when bodies coincide.
// * `items_after_statements` — local helper fns near their first use are
// more readable than top-of-scope.
// * `format_push_string` — SMT and trace assembly use `s += &format!()`
// extensively; rewriting to `write!` would obscure intent.
// * `cast_*` (truncation/wrap/sign loss) — entity slot indices and BMC
// bounds are bounded ints, the casts are sound.
// * `many_single_char_names` / `similar_names` — math-heavy code uses
// short identifiers in tight scopes by convention.
// * `type_complexity` — IR / Z3 boundary functions return long tuples.
// * `doc_list_without_indent` / `doc_markdown` — Markdown style noise.
// * `ref_option` — `&Option<T>` is used at boundaries we don't control.
#![allow(
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::match_same_arms,
    clippy::items_after_statements,
    clippy::format_push_string,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_lossless,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    clippy::doc_lazy_continuation,
    clippy::doc_markdown,
    clippy::ref_option,
    clippy::needless_pass_by_value,
    clippy::needless_pass_by_ref_mut,
    clippy::result_large_err,
    clippy::large_enum_variant,
    clippy::unnecessary_wraps,
    clippy::cloned_ref_to_slice_refs,
    clippy::redundant_closure_call,
    clippy::used_underscore_binding
)]

pub use abide_core::{diagnostic, messages, span};
pub use abide_ir::ir;
pub use abide_qa::qa;
pub use abide_sema::{elab, loader};
pub use abide_syntax::{ast, lex, parse};
pub use abide_verify::verify;
pub use abide_witness as witness;

pub mod artifact;
pub mod cli;
pub mod driver;
pub mod ide;
pub mod render;
pub mod repl;
pub mod simulate;
pub mod workspace;
