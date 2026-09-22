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
            let precomputations =
                CircuitPrecomputations::from_canonical(circuit_type, setup, security_level)
                    .unwrap();
            (circuit_type, precomputations)
        })
        .collect()
}
