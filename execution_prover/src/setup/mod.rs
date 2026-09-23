mod common;
mod unrolled;

pub use common::{build_common_setups, build_delegation_setup};
pub use unrolled::build_unrolled_setup;

use crate::upstream::{CircuitSetup, DelegationCircuitSetup};
use std::alloc::Global;

pub enum CanonicalCircuitSetup {
    Riscv(CircuitSetup<Global>),
    Delegation(DelegationCircuitSetup),
}

#[cfg(test)]
mod tests;
