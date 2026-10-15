use super::CircuitPrecomputations;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

use crate::upstream::{inits_and_teardowns_circuit_setup, ProofProfile, SecurityLevel};
use execution_prover::setup::{build_common_setups, CanonicalCircuitSetup};
use std::alloc::Global;
use std::collections::BTreeMap;
use worker::Worker;

/// Build the binary-independent precomputations: every delegation circuit
/// and inits-and-teardowns.
pub(crate) fn get_common_precomputations_for_all(
    worker: &Worker,
    security_level: SecurityLevel,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    build_common_setups(worker)
        .into_iter()
        .map(|(circuit_type, setup)| {
            let precomputations = CircuitPrecomputations::from_canonical(
                circuit_type,
                setup,
                security_level,
                &[ProofProfile::Standard],
            )
            .unwrap();
            (circuit_type, precomputations)
        })
        .collect()
}

pub(crate) fn get_inits_and_teardowns_precomputations(
    worker: &Worker,
    security_level: SecurityLevel,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
    let setup =
        CanonicalCircuitSetup::Riscv(inits_and_teardowns_circuit_setup::<Global>(true, worker));
    let precomputations = CircuitPrecomputations::from_canonical(
        circuit_type,
        setup,
        security_level,
        &[ProofProfile::Standard],
    )
    .unwrap();
    BTreeMap::from([(circuit_type, precomputations)])
}
