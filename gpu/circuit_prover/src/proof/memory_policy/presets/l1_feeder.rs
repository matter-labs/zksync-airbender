use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

/// Admission budget for an L1 feeder proof. With a 21 GiB arena, the bounded feeder capacity
/// cases (`gpu/execution_prover/tests/l1_memory.rs`) pass for profile A (2^23 `Unified`, LDE 4,
/// cap 4) and profile C (2^22 `Unified22`, LDE 16, cap 16), at the commitment and proof stages,
/// in both allocation directions, beside a Standard follower, on the RTX PRO 6000 Blackwell
/// (sm_120). The measured peaks are 19,685,965,824 B (A) and 10,695,475,200 B (C), both at the
/// proof stage. Feeder and wrap followers and arenas below 21 GiB are not covered by these
/// measurements, and no lower failing bracket establishes a minimum.
pub const L1_FEEDER_FLOOR_BYTES: usize = 21 << 30;
pub const L1_FEEDER_FLOOR_SOURCE: &str = "measured";

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
