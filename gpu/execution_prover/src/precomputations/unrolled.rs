use super::{config_logs_for_circuit, CircuitPrecomputations};
use execution_prover_model::MachineType;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

use crate::upstream::SecurityLevel;
use execution_prover::setup::{build_unified_setup, build_unrolled_setup};
use worker::Worker;

/// Turn one per-binary circuit's canonical setup into GPU state.
pub(crate) fn build_unrolled_circuit_precomputation(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
    security_level: SecurityLevel,
) -> CircuitPrecomputations {
    let setup = match circuit_type {
        UnrolledCircuitType::Unified => build_unified_setup(binary_image, text_section, worker),
        UnrolledCircuitType::Memory(_) | UnrolledCircuitType::NonMemory(_) => build_unrolled_setup(
            machine_type,
            circuit_type,
            binary_image,
            text_section,
            worker,
        ),
        UnrolledCircuitType::InitsAndTeardowns => panic!(
            "inits-and-teardowns is binary-independent and belongs to the common precomputations"
        ),
    };
    let circuit_type = CircuitType::Unrolled(circuit_type);
    let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
        config_logs_for_circuit(circuit_type, security_level);
    CircuitPrecomputations::from_canonical(
        circuit_type,
        setup,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
    )
    .unwrap()
}
