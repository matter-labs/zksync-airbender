use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

/// Arena floor carried from the previously qualified compression source.
/// Requalification uses A/C, commitment/proof and both allocation directions with `standard_it`.
/// Other followers and lower arenas remain outside that evidence.
pub const COMPRESSION_FINAL_FLOOR_BYTES: usize = 21 << 30;
pub const COMPRESSION_FINAL_FLOOR_SOURCE: &str = "measured";

pub const POLICY: ProofMemoryPolicy = ProofMemoryPolicy {
    gkr: GkrMemoryPolicy::Materialize,
    setup: OpeningStrategy::PerCoset,
    memory: OpeningStrategy::PerCoset,
    witness: WitnessMemoryPolicy {
        commitment: WitnessCommitmentStrategy::PerCoset,
        post_commitment: WitnessPostCommitStorage::RawAndMonomials,
        opening: WitnessOpeningStrategy::Recompute(OpeningStrategy::PerCoset),
    },
};

pub const PARTIAL_TREES: PartialTreePolicy = PartialTreePolicy {
    setup: 10,
    memory: 10,
    ..PartialTreePolicy::DEFAULT
};

pub fn policy(_arena_bytes: usize) -> ProofMemoryPolicy {
    POLICY
}
