//! Shared circuit setups and witness evaluators for the proving backends.

mod common;
mod unrolled;

pub use common::{build_common_setups, build_delegation_setup, build_inits_and_teardowns_setup};
pub use unrolled::{build_unified_setup, build_unrolled_setup};

use crate::upstream::{CircuitSetup, DelegationCircuitSetup};
use std::alloc::Global;

pub enum CanonicalCircuitSetup {
    Riscv(CircuitSetup<Global>),
    Delegation(DelegationCircuitSetup),
}

#[cfg(test)]
mod tests;
