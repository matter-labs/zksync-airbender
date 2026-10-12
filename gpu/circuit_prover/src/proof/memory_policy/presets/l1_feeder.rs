use super::super::{
    GkrMemoryPolicy, OpeningStrategy, ProofMemoryPolicy, WitnessCommitmentStrategy,
    WitnessMemoryPolicy, WitnessOpeningStrategy, WitnessPostCommitStorage,
};

pub const POLICY: ProofMemoryPolicy = ProofMemoryPolicy {
    gkr: GkrMemoryPolicy::Materialize,
    setup: OpeningStrategy::PerCoset,
    memory: OpeningStrategy::PerCoset,
    witness: WitnessMemoryPolicy {
        commitment: WitnessCommitmentStrategy::InPlace,
        post_commitment: WitnessPostCommitStorage::RawEvaluations,
        opening: WitnessOpeningStrategy::Recompute(OpeningStrategy::PerCoset),
    },
};

pub fn policy(_arena_bytes: usize) -> ProofMemoryPolicy {
    POLICY
}
