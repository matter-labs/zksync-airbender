use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

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
