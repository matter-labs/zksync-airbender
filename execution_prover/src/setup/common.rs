//! Binary-independent setups: the four delegation circuits and the standalone
//! inits-and-teardowns circuit.

use super::CanonicalCircuitSetup;
use crate::upstream::{
    get_bigint_with_control_circuit_setup, get_blake2_g_function_circuit_setup,
    get_blake2_with_compression_circuit_setup, get_keccak_special5_circuit_setup,
    inits_and_teardowns_circuit_setup,
};
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType,
};
use std::alloc::Global;
use std::collections::BTreeMap;
use worker::Worker;

pub fn build_delegation_setup(
    delegation_type: DelegationCircuitType,
    worker: &Worker,
) -> CanonicalCircuitSetup {
    let setup = match delegation_type {
        DelegationCircuitType::BigIntWithControl => {
            get_bigint_with_control_circuit_setup(true, worker)
        }
        DelegationCircuitType::Blake2WithCompression => {
            get_blake2_with_compression_circuit_setup(true, worker)
        }
        DelegationCircuitType::Blake2GFunction => get_blake2_g_function_circuit_setup(true, worker),
        DelegationCircuitType::KeccakSpecial5 => get_keccak_special5_circuit_setup(true, worker),
    };
    CanonicalCircuitSetup::Delegation(setup)
}

pub fn build_inits_and_teardowns_setup(worker: &Worker) -> CanonicalCircuitSetup {
    CanonicalCircuitSetup::Riscv(inits_and_teardowns_circuit_setup::<Global>(true, worker))
}

/// Every binary-independent circuit, keyed by circuit type.
pub fn build_common_setups(worker: &Worker) -> BTreeMap<CircuitType, CanonicalCircuitSetup> {
    let mut out = BTreeMap::new();
    for delegation_type in DelegationCircuitType::get_all_delegation_types()
        .iter()
        .copied()
    {
        out.insert(
            CircuitType::Delegation(delegation_type),
            build_delegation_setup(delegation_type, worker),
        );
    }
    out.insert(
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
        build_inits_and_teardowns_setup(worker),
    );
    out
}
