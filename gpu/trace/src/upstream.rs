//! Single-file audit point for items `gpu_trace` consumes from upstream crates
//! (`cs`, `prover`, `field`, `setups`).
//!
//! Production code (`witness/**`, `trace/**`) imports upstream items exclusively
//! through `crate::upstream` — direct `use cs::…` / `use prover::…` lines in
//! non-test code are forbidden. This manifest is the contract: a missing/renamed
//! upstream item surfaces as a compile error pointing here, and the drift guards
//! in [`crate::witness`] assert native-side literals against these values.
//!
//! Sliced from `gpu_circuit_prover`'s manifest to exactly the items the moved
//! trees reference; grouped by upstream crate, then module. Aliases noted inline.

// -----------------------------------------------------------------------
// `cs` — circuit description, GKR layout, and compilation artifacts
// -----------------------------------------------------------------------

pub(crate) use cs::definitions::gkr::{
    GKRMachineState, GKRMemoryLayout, NoFieldLinearRelation, NoFieldSingleColumnLookupRelation,
};
// Aliased to avoid collision with crate-local types of the same name.
pub(crate) use cs::definitions::gkr::DecoderPlacementDescription as CSDecoderPlacementDescription;
pub(crate) use cs::definitions::gkr::IndirectRamAccessAddress as CSIndirectRamAccessAddress;
pub(crate) use cs::definitions::gkr::MachineStatePermutationDescription as CSMachineStatePermutationDescription;
pub(crate) use cs::definitions::gkr::RamAddress as CSRamAddress;
pub(crate) use cs::definitions::gkr::RamAuxComparisonSet as CSRamAuxComparisonSet;
pub(crate) use cs::definitions::gkr::RamQuery as CSRamQuery;
pub(crate) use cs::definitions::gkr::RamReadQuery as CSRamReadQuery;
pub(crate) use cs::definitions::gkr::RamWordRepresentation as CSRamWordRepresentation;
pub(crate) use cs::definitions::gkr::RamWriteQuery as CSRamWriteQuery;
pub(crate) use cs::definitions::gkr::RegisterOnlyAccessAddress as CSRegisterOnlyAccessAddress;
pub(crate) use cs::definitions::gkr::RegisterOrRamAccessAddress as CSRegisterOrRamAccessAddress;
pub(crate) use cs::definitions::gkr::RegisterOrRamAddressSpace as CSRegisterOrRamAddressSpace;
pub(crate) use cs::definitions::{
    GKRAddress, BIGINT_BASE_ABI_REGISTER, BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    BIGINT_X10_NUM_WRITES, BIGINT_X11_NUM_READS, BLAKE2S_BASE_ABI_REGISTER,
    BLAKE2S_DELEGATION_CSR_REGISTER, BLAKE2S_G_FUNCTION_BASE_ABI_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, BLAKE2S_G_FUNCTION_X10_NUM_WRITES,
    BLAKE2S_G_FUNCTION_X11_NUM_READS, BLAKE2S_X10_NUM_WRITES, BLAKE2S_X11_NUM_READS,
    KECCAK_SPECIAL5_BASE_ABI_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
    KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS, KECCAK_SPECIAL5_X11_NUM_WRITES, NON_DETERMINISM_CSR,
    NUM_BIGINT_REGISTER_ACCESSES, NUM_BIGINT_VARIABLE_OFFSETS,
    NUM_BLAKE2S_G_FUNCTION_REGISTER_ACCESSES, NUM_BLAKE2S_G_FUNCTION_VARIABLE_OFFSETS,
    NUM_BLAKE2S_REGISTER_ACCESSES, NUM_BLAKE2S_VARIABLE_OFFSETS, NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP,
    NUM_KECCAK_SPECIAL5_INDIRECT_READS, NUM_KECCAK_SPECIAL5_REGISTER_ACCESSES,
    NUM_TIMESTAMP_COLUMNS_FOR_RAM, NUM_TIMESTAMP_DATA_LIMBS, REGISTER_SIZE,
    TIMESTAMP_COLUMNS_NUM_BITS,
};
pub(crate) use cs::gkr_circuits::ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData;
pub(crate) use cs::gkr_compiler::{GKRAuxLayoutData, GKRCircuitArtifact};
pub(crate) use cs::tables::TableType;

// -----------------------------------------------------------------------
// `field` — base field, extension towers
// -----------------------------------------------------------------------

pub(crate) use field::baby_bear::base::BabyBearField;
// Trait methods only exercised by `trace::holder::tests` (LDE/coset host-side checks).
#[cfg(test)]
pub(crate) use field::{Field, PrimeField};

// -----------------------------------------------------------------------
// `prover` — CPU prover types the GPU prover mirrors / interoperates with
// -----------------------------------------------------------------------

pub(crate) use prover::gkr::prover_config::ProverConfig;
// CPU-reference helper only exercised by `trace::holder::tests`.
#[cfg(test)]
pub(crate) use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
// CPU merkle-tree reference construction only exercised by `trace::holder::tests`.
#[cfg(test)]
pub(crate) use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
#[cfg(test)]
pub(crate) use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
pub(crate) use prover::merkle_trees::MerkleTreeCapVarLength;

// -----------------------------------------------------------------------
// `setups` — compiled-circuit binary loading
// -----------------------------------------------------------------------

pub(crate) use setups::{
    inits_and_teardowns, AddSubLuiAuipcMopCircuit, BigIntDelegationCircuit,
    Blake2sGFunctionDelegationCircuit, Blake2sWithCompressionDelegationCircuit,
    JumpBranchSltCircuit, KeccakSpecial5DelegationCircuit, LoadStoreSubwordOnlyCircuit,
    LoadStoreWordOnlyCircuit, ShiftBinaryCircuit, UnifiedReducedMachineCircuit,
    UnsignedMulDivCircuit,
};
