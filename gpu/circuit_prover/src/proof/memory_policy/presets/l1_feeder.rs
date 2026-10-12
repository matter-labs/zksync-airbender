use super::super::{
    GkrMemoryPolicy, OpeningStrategy, ProofMemoryPolicy, WitnessCommitmentStrategy,
    WitnessMemoryPolicy, WitnessOpeningStrategy, WitnessPostCommitStorage,
};

/// Analytic floor (the generated tier the Standard 2^23 unified policy fits), not a tested capacity.
pub const L1_FEEDER_FLOOR_BYTES: usize = 21 << 30;
pub const L1_FEEDER_FLOOR_SOURCE: &str = "analytic";

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
