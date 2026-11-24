pub mod compression;
pub(crate) mod generated;

use crate::proof::memory_policy::presets::is_compression;
use crate::upstream::ProofProfile;
use gpu_gkr::baby_bear::stage1::merged_commitment::MergedCommitStrategy;
use gpu_trace::witness::circuit_type::CircuitType;

pub fn merged_commit_strategy(circuit: CircuitType, profile: ProofProfile) -> MergedCommitStrategy {
    if is_compression(circuit, profile) {
        MergedCommitStrategy::Monomials
    } else {
        MergedCommitStrategy::AllCosets
    }
}
