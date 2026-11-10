use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

pub const fn align_up(bytes: usize, unit: usize) -> usize {
    assert!(unit > 0, "L1Wrap arena alignment unit must be positive");
    let rounded = bytes
        .checked_add(unit - 1)
        .expect("L1Wrap arena alignment overflow");
    (rounded / unit)
        .checked_mul(unit)
        .expect("L1Wrap arena alignment overflow")
}

pub const L1_WRAP_POLICY: ProofMemoryPolicy = ProofMemoryPolicy {
    gkr: GkrMemoryPolicy::Materialize,
    setup: OpeningStrategy::PerCoset,
    memory: OpeningStrategy::PerCoset,
    witness: WitnessMemoryPolicy {
        commitment: WitnessCommitmentStrategy::PerCoset,
        post_commitment: WitnessPostCommitStorage::RawAndMonomials,
        opening: WitnessOpeningStrategy::PackedCosetRecompute,
    },
};

pub const PARTIAL_TREES: PartialTreePolicy = PartialTreePolicy {
    setup: gpu_gkr::setup::L1WrapSetupHost::PARTIAL_TREE_REDUCTION_LAYERS,
    memory: 10,
    ..PartialTreePolicy::DEFAULT
};
