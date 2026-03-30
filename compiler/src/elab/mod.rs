//! Abide elaboration pipeline: Collect → Resolve → Check.

pub mod check;
pub mod collect;
pub mod env;
pub mod error;
pub mod resolve;
pub mod types;

use crate::ast::Program;
use error::ElabError;
use types::ElabResult;

/// Run the full elaboration pipeline on a parsed program.
///
/// Returns the elaborated result and any errors accumulated across all passes.
pub fn elaborate(program: &Program) -> (ElabResult, Vec<ElabError>) {
    // Pass 1: Collect all declarations
    let env = collect::collect(program);

    // Passes 2-3: Resolve and check
    elaborate_env(env)
}

/// Run the resolve and check passes on an already-populated Env.
///
/// Used by the multi-file loader which handles collection (Pass 1) itself,
/// then hands off the merged Env for resolution and checking.
pub fn elaborate_env(mut env: env::Env) -> (ElabResult, Vec<ElabError>) {
    let collect_errors = env.take_errors();

    // Build bare-name working namespace from module-qualified semantic maps.
    // This flattens qualified entries (e.g. "Commerce::Order") into bare names
    // ("Order") for downstream resolve/check/lower passes.
    env.build_working_namespace();

    // Pass 2: Resolve unresolved types and names
    resolve::resolve(&mut env);
    let resolve_errors = env.take_errors();

    // Pass 3: Type-check and validate well-formedness
    let (result, check_errors) = check::check(&env);

    // Tag untagged errors with file context.
    // Resolve/check errors have spans but may lack file tags since those passes
    // run after collection. Use env.current_file (root file for single-file loads)
    // or match against DeclInfo files for multi-file.
    let root_file = env.current_file.clone();
    let mut all_errors = collect_errors;
    for mut err in resolve_errors {
        if err.file.is_none() {
            if let Some(span) = err.span {
                if let Some(file) = find_file_for_span(&env, span).or(root_file.clone()) {
                    err.file = Some(file);
                }
            }
        }
        all_errors.push(err);
    }
    for mut err in check_errors {
        if err.file.is_none() {
            if let Some(span) = err.span {
                if let Some(file) = find_file_for_span(&env, span).or(root_file.clone()) {
                    err.file = Some(file);
                }
            }
        }
        all_errors.push(err);
    }

    (result, all_errors)
}

/// Try to determine which file a span belongs to by checking declaration
/// and use-declaration spans.
fn find_file_for_span(env: &env::Env, span: crate::span::Span) -> Option<String> {
    // Check DeclInfo spans
    for decl in env.decls.values() {
        if let (Some(decl_span), Some(ref file)) = (decl.span, &decl.file) {
            if span.start >= decl_span.start && span.end <= decl_span.end {
                return Some(file.clone());
            }
        }
    }
    // Check use declaration spans
    for entry in &env.use_decls {
        if let Some(ref file) = entry.source_file {
            let use_span = match &entry.decl {
                crate::ast::UseDecl::All { span: s, .. }
                | crate::ast::UseDecl::Single { span: s, .. }
                | crate::ast::UseDecl::Alias { span: s, .. }
                | crate::ast::UseDecl::Items { span: s, .. } => *s,
            };
            if span.start >= use_span.start && span.end <= use_span.end {
                return Some(file.clone());
            }
        }
    }
    None
}
