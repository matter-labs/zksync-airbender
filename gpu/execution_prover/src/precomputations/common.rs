use super::CircuitPrecomputations;
use gpu_trace::witness::circuit_type::CircuitType;

use crate::upstream::ProofProfile;
use execution_prover::config::SoundnessMode;
use execution_prover::setup::build_common_setups;
use std::collections::BTreeMap;
use worker::Worker;

/// Build the binary-independent precomputations: every delegation circuit
/// and inits-and-teardowns.
pub(crate) fn get_common_precomputations_for_all(
    worker: &Worker,
    soundness_mode: SoundnessMode,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    build_common_setups(worker)
        .into_iter()
        .map(|(circuit_type, setup)| {
            let precomputations = CircuitPrecomputations::from_canonical(
                circuit_type,
                setup,
                soundness_mode,
                &[ProofProfile::Standard],
            );
            (circuit_type, precomputations)
        })
        .collect()
}
