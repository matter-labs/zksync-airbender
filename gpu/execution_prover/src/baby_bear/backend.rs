use crate::precomputations::CircuitPrecomputations;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::ProofProfile;
use gpu_core::primitives::field::BF;
use std::sync::Arc;

impl CircuitPrecomputation for CircuitPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        self.baby_bear().gkr_programs.compiled_circuit()
    }

    fn setup_cap(&self, profile: ProofProfile) -> Option<MerkleTreeCapVarLength> {
        self.baby_bear()
            .setup_host
            .get_initialized(profile)
            .map(|setup_host| MerkleTreeCapVarLength {
                cap: setup_host.unified_tree_cap().to_vec(),
            })
    }
}
