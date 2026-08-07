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

pub(crate) use cs::definitions::gkr::{
    AddressSpaceType, RamWordRepresentation, DECODER_LOOKUP_FORMAL_SET_INDEX,
};
pub(crate) use cs::definitions::{
    GKRAddress, VirtualSetupPoly, NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
pub(crate) use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, InitsOrTeardownsTimestampAndValue,
    NoFieldSpecialMemoryContributionRelation, OutputType,
};
pub(crate) type GKRLayerDescription = cs::gkr_compiler::GKRLayerDescription<BabyBearField>;
pub(crate) use cs::gkr_compiler::{
    GKRLayerDescription as CSGKRLayerDescription, GateArtifacts as CSGateArtifacts,
};
pub(crate) type NoFieldGKRRelation = cs::gkr_compiler::NoFieldGKRRelation<BabyBearField>;
pub(crate) use cs::gkr_compiler::NoFieldGKRRelation as CSNoFieldGKRRelation;
pub(crate) use cs::gkr_compiler::NoFieldStructuredExpression;
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
pub(crate) use prover::gkr::high_bits_offset_for_inits_and_teardowns;
pub(crate) use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
// Aliased to avoid collision with crate-local types of the same name.
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub(crate) use prover::gkr::prover::{SumcheckIntermediateProofValues, WhirSchedule};
pub(crate) use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchedGKRKernel, ExtensionCopyGKRRelation, GKRInputs,
    LookupBaseExtMinusBaseExtGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
    LookupBasePairGKRRelation, LookupExtensionMinusMultiplicityByExtensionGKRRelation,
    LookupExtensionPairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
pub(crate) use prover::gkr::virtual_polys::init_and_teardown_base::materialize_virtual_inits_and_teardowns_base_address_setup_poly;
pub(crate) use prover::gkr::whir::{
    BaseFieldQuery, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries, WhirCommitment,
    WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
pub(crate) use prover::merkle_trees::{
    ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, MerkleTreeCapVarLength,
};
pub(crate) use prover::transcript::Seed;
