//! Upstream types used by `gpu_gkr`.

// -----------------------------------------------------------------------
// `gkr_eval_ir` — canonical GPU-independent evaluation DAG
// -----------------------------------------------------------------------

pub(crate) use gkr_eval_ir::{
    ChallengeKey, ChallengePower, ChallengeRef, FieldKind, PermutationSlot, RangeWidth, ReadPlace,
    VirtualSetupKind,
};

// -----------------------------------------------------------------------
// `cs` — circuit description, GKR layout, and compilation artifacts
// -----------------------------------------------------------------------

pub(crate) use cs::definitions::{
    split_timestamp, GKRAddress, VirtualSetupPoly,
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
pub(crate) use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
pub(crate) type GKRLayerDescription = cs::gkr_compiler::GKRLayerDescription<BabyBearField>;
pub(crate) type GKRRelation = cs::gkr_compiler::GKRRelation<BabyBearField>;
pub(crate) use cs::tables::TableType;

// -----------------------------------------------------------------------
// `field` — base field, extension towers
// -----------------------------------------------------------------------

pub(crate) use field::baby_bear::base::BabyBearField;
pub(crate) use field::{Field, FieldExtension, PrimeField};

// -----------------------------------------------------------------------
// `prover` — CPU prover types the GPU prover mirrors / interoperates with
// -----------------------------------------------------------------------

pub(crate) use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub(crate) use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
// Aliased to avoid collision with crate-local types of the same name.
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub(crate) use prover::gkr::prover::{
    CommitmentMode, SumcheckIntermediateProofValues, SumcheckRoundCoefficients, WhirSchedule,
};
pub(crate) use prover::gkr::prover_config::pow_bits::{
    lookup_challenges_pow_bits, lookup_identity_degree,
};
pub(crate) use prover::gkr::prover_config::ProverConfig;
pub(crate) use prover::gkr::whir::{
    BaseFieldQuery, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries, WhirCommitment,
    WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
pub(crate) use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
#[cfg(test)]
pub(crate) use prover::transcript::Seed;
