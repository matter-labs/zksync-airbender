//! Single-file audit point for items consumed from upstream crates
//! (`cs`, `prover`, `field`, `common_constants`).
//!
//! When bumping an upstream version, scan this file first — every type,
//! function, and constant the crate depends on is re-exported here, so a
//! missing/renamed item surfaces as a compile error pointing at this
//! manifest rather than at scattered call sites.
//!
//! Consumers under `gpu/gkr/src/` import upstream items exclusively through
//! `crate::upstream` — direct `use cs::…` / `use prover::…` lines in consumer
//! code are forbidden. `#[cfg(test)]` modules are exempt.

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
    GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, InitsOrTeardownsTimestampAndValue,
    NoFieldGKRCacheRelation, NoFieldGKRRelation, NoFieldMaxQuadraticConstraintsGKRRelation,
    NoFieldMaxQuadraticGKRRelation, NoFieldSpecialMemoryContributionRelation, OutputType,
};
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
