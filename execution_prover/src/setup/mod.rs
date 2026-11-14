mod common;
mod unrolled;

pub use common::{build_common_setups, build_delegation_setup};
pub use unified_reduced_machine_proth120::L1WrapSetup;
pub use unrolled::{
    build_unrolled_setup, build_unrolled_setup_with_preprocessing, circuit_types_for_variant,
    preprocess_binary, BinaryPreprocessing,
};

use crate::upstream::{CircuitSetup, DelegationCircuitSetup};
use std::alloc::Global;

pub enum CanonicalCircuitSetup {
    Riscv(CircuitSetup<Global>),
    Delegation(DelegationCircuitSetup),
    L1Wrap(unified_reduced_machine_proth120::L1WrapSetup),
}

#[cfg(test)]
mod tests;
