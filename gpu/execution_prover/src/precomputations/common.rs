use super::CircuitPrecomputations;
use gpu_trace::witness::circuit_type::CircuitType;

use crate::upstream::SecurityLevel;
use execution_prover::setup::build_common_setups;
use std::collections::BTreeMap;
use worker::Worker;

/// Build the binary-independent precomputations — every delegation circuit and
/// inits-and-teardowns — from the shared canonical setups.
pub(crate) fn get_common_precomputations_for_all(
    worker: &Worker,
    security_level: SecurityLevel,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    build_common_setups(worker)
        .into_iter()
        .map(|(circuit_type, setup)| {
            let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
                config_logs_for_circuit(circuit_type, security_level);
            let precomputations = CircuitPrecomputations::from_canonical(
                circuit_type,
                setup,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
            )
            .unwrap();
            (circuit_type, precomputations)
        })
        .collect()
}

/// The WHIR geometry the GPU worker will use at `prove()` time, which differs
/// per circuit.
pub(crate) fn config_logs_for_circuit(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> (u32, u32, u32) {
    let prover_config = gpu_circuit_prover::config::prover_config(circuit_type, security_level)
        .expect("ExecutionProverConfiguration validated GPU security level before precomputation");
    (
        prover_config.lde_factor.trailing_zeros(),
        prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        prover_config.cap_size.trailing_zeros(),
    )
}
