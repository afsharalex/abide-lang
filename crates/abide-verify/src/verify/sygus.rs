use std::collections::HashMap;
use std::time::Instant;

use cvc5_rs::{Kind as Cvc5Kind, Solver as Cvc5Solver, Term as Cvc5Term, TermManager as Cvc5Tm};

use crate::ir::types::{
    IRAction, IRCreateField, IREntity, IRExpr, IRField, IRStep, IRSystem, IRTransParam,
    IRTransition, IRType, LitVal,
};
mod core;
mod pooled;
use self::core::*;
pub use self::core::{try_cvc5_sygus_single_entity, try_cvc5_sygus_system_safety};
pub use self::pooled::try_cvc5_sygus_multi_system_pooled_safety;
#[cfg(test)]
use self::pooled::*;

use super::ic3::Ic3Result;

#[cfg(test)]
mod tests;
