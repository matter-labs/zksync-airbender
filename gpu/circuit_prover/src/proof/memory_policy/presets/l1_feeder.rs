use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

/// A 21 GiB arena passes the bounded feeder capacity matrix: commitment and proof
/// stages, both allocation directions, and Standard, feeder, and wrap followers
/// (`gpu/execution_prover/tests/l1_memory.rs`). On the RTX PRO 6000 Blackwell
/// (sm_120), the worst measured peak is 19,954,401,280 B for the 2^23 `Unified`
/// profile A (LDE 4, cap 4), and 10,829,692,928 B for the 2^22 `Unified22` profile C
/// (LDE 16, cap 16), both beside a Standard follower. The 21 GiB candidate is the
/// smallest tested passing arena; no lower failing bracket establishes a minimum.
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
