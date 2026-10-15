mod common;
mod unrolled;

pub use common::{
    build_common_setups, build_delegation_setup, build_delegation_setup_with_cache_mode,
};
pub use unrolled::{build_unrolled_setup, build_unrolled_setup_with_cache_mode};

use crate::upstream::{CircuitSetup, DelegationCircuitSetup};
use std::alloc::Global;

pub enum CanonicalCircuitSetup {
    Riscv(CircuitSetup<Global>),
    Delegation(DelegationCircuitSetup),
}

#[cfg(test)]
mod tests;
