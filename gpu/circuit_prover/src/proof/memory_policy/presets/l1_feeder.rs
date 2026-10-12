use super::super::{
    GkrMemoryPolicy, OpeningStrategy, ProofMemoryPolicy, WitnessCommitmentStrategy,
    WitnessMemoryPolicy, WitnessOpeningStrategy, WitnessPostCommitStorage,
};

/// Smallest sufficient arena of the bounded capacity matrix (`gpu/execution_prover/tests/l1_memory.rs`: 21/30/40/48/64 GiB candidates, commitment and proof stages, both directions, three opposite followers) on the RTX PRO 6000 Blackwell (sm_120).
pub const L1_FEEDER_FLOOR_BYTES: usize = 21 << 30;
pub const L1_FEEDER_FLOOR_SOURCE: &str = "measured";

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
