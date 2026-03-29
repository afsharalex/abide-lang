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

    let mut all_errors = collect_errors;
    all_errors.extend(resolve_errors);
    all_errors.extend(check_errors);

    (result, all_errors)
}
