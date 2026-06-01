//! Abide verifier — SAT/SMT backends, scene witness construction,
//! and explicit-state model checking.
//!
//! Consumes lowered IR ([`ir::types::IRProgram`]) and emits
//! [`verify::VerificationResult`] values plus structured witnesses
//! (via `abide-witness`).
//!
//! Internally organized as a flat set of backends and harnesses
//! (`bmc`, `ic3`, `scene`, `theorem`, `relation_sat`, `ltl`,
//! `temporal[_relational]`, `transition`, `fn_verify`, …) coordinated
//! through [`verify`]. CLAUDE.md locks an important invariant for
//! this crate: only the Z3 backend module may import `z3::` directly;
//! all other code goes through the `SolverBackend` trait and SMT
//! facade.

pub use abide_core::{messages, span};
pub use abide_ir::ir;

pub mod verify;
