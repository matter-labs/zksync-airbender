//! Upstream types used by `gpu_gkr`.

// -----------------------------------------------------------------------
// `gkr_eval_ir` — canonical GPU-independent evaluation DAG
// -----------------------------------------------------------------------

pub(crate) use gkr_eval_ir::{
    ChallengeKey, ChallengePower, ChallengeRef, FieldKind, PermutationSlot, RangeWidth, ReadPlace,
    VirtualSetupKind,
};

/// Runtime-only launch-family spelling. Compiler policy stays split across
/// typed R0 and continuation entry points.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum BwdRegime {
    R0,
    Ext,
}

// -----------------------------------------------------------------------
// `cs` — circuit description, GKR layout, and compilation artifacts
// -----------------------------------------------------------------------

pub(crate) use cs::definitions::{
    GKRAddress, VirtualSetupPoly, NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
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

pub(crate) use prover::definitions::GKRExternalChallenges;
pub(crate) use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
// Aliased to avoid collision with crate-local types of the same name.
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub(crate) use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
pub(crate) use prover::gkr::prover::{
    SumcheckIntermediateProofValues, SumcheckRoundCoefficients, WhirSchedule,
};
pub(crate) use prover::gkr::sumcheck::evaluation_kernels::GKRInputs;
pub(crate) use prover::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
pub(crate) use prover::gkr::whir::{
    BaseFieldQuery, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries, WhirCommitment,
    WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
pub(crate) use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
pub(crate) use prover::transcript::{Blake2sTranscript, Seed};
