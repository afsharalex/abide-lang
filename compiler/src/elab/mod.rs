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
    let mut env = collect::collect(program);
    let collect_errors = env.take_errors();

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
