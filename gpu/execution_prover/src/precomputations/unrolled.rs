use super::CircuitPrecomputations;
use execution_prover_model::MachineType;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

use crate::upstream::SecurityLevel;
use execution_prover::setup::build_unrolled_setup;
use worker::Worker;

pub(crate) fn build_unrolled_circuit_precomputation(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
    security_level: SecurityLevel,
) -> CircuitPrecomputations {
    let setup = build_unrolled_setup(
        machine_type,
        circuit_type,
        binary_image,
        text_section,
        worker,
    );
    let circuit_type = CircuitType::Unrolled(circuit_type);
    CircuitPrecomputations::from_canonical(circuit_type, setup, security_level).unwrap()
}
