//! Single-file audit point for items consumed from upstream crates
//! (`cs`, `prover`, `field`, `setups`, `trace_and_split`).
//!
//! When bumping an upstream version, scan this file first — every type,
//! function, and constant the crate depends on is re-exported here, so a
//! missing/renamed item surfaces as a compile error pointing at this
//! manifest rather than at scattered call sites. Conversely, additions to
//! this file are the documented surface contract with the upstream crates.
//!
//! Items are grouped by upstream crate, then by module path. Aliases are
//! noted inline.
//!
//! Consumers under `gpu/circuit_prover/src/` import upstream items exclusively
//! through `crate::upstream` — direct `use cs::…` / `use prover::…` lines
//! in consumer code are forbidden. The manifest is the contract.
//!
//! ```ignore
//! use crate::upstream::{GKRCircuitArtifact, Field, ...};
//! ```

// -----------------------------------------------------------------------
// `cs` — circuit description, GKR layout, and compilation artifacts
// -----------------------------------------------------------------------

pub(crate) use cs::cs::circuit_trait::Circuit;
pub(crate) use cs::definitions::gkr::{
    AddressSpaceType, GKRMachineState, GKRMemoryLayout, NoFieldLinearRelation,
    NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation, RamWordRepresentation,
    DECODER_LOOKUP_FORMAL_SET_INDEX,
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
    GKRAddress, VirtualSetupPoly, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
    BIGINT_BASE_ABI_REGISTER, BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BIGINT_X10_NUM_WRITES,
    BIGINT_X11_NUM_READS, BLAKE2S_BASE_ABI_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_BASE_ABI_REGISTER, BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_X10_NUM_WRITES, BLAKE2S_G_FUNCTION_X11_NUM_READS, BLAKE2S_X10_NUM_WRITES,
    BLAKE2S_X11_NUM_READS, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX, KECCAK_SPECIAL5_BASE_ABI_REGISTER,
    KECCAK_SPECIAL5_CSR_REGISTER, KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS,
    KECCAK_SPECIAL5_X11_NUM_WRITES, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
    LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, MUL_DIV_CIRCUIT_FAMILY_IDX, NON_DETERMINISM_CSR,
    NUM_BIGINT_REGISTER_ACCESSES, NUM_BIGINT_VARIABLE_OFFSETS,
    NUM_BLAKE2S_G_FUNCTION_REGISTER_ACCESSES, NUM_BLAKE2S_G_FUNCTION_VARIABLE_OFFSETS,
    NUM_BLAKE2S_REGISTER_ACCESSES, NUM_BLAKE2S_VARIABLE_OFFSETS, NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP,
    NUM_KECCAK_SPECIAL5_INDIRECT_READS, NUM_KECCAK_SPECIAL5_REGISTER_ACCESSES,
    NUM_PERMUTATION_ARGUMENT_KEY_PARTS, NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES,
    NUM_TIMESTAMP_COLUMNS_FOR_RAM, NUM_TIMESTAMP_DATA_LIMBS,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, REGISTER_SIZE, ROM_SECOND_WORD_BITS,
    SHIFT_BINARY_CIRCUIT_FAMILY_IDX, TIMESTAMP_COLUMNS_NUM_BITS,
};
pub(crate) use cs::gkr_circuits::{
    add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
    add_sub_lui_auipc_mop_table_addition_fn, create_mem_subword_only_special_tables,
    create_mem_word_only_special_tables,
    jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr, jump_branch_slt_table_addition_fn,
    jump_branch_slt_table_driver_fn, mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr,
    mem_subword_only_table_addition_fn, mem_subword_only_table_driver_fn,
    mem_word_only_circuit_with_preprocessed_bytecode_for_gkr, mem_word_only_table_addition_fn,
    mem_word_only_table_driver_fn,
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
    shift_binop_circuit_with_preprocessed_bytecode_for_gkr, shift_binop_table_addition_fn,
    shift_binop_table_driver_fn, ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData,
};
pub(crate) use cs::gkr_compiler::{
    compile_unrolled_circuit_state_transition_into_gkr, CompiledAddressSpaceRelationStrict,
    CompiledAddressStrict, CompiledMemoryTimestamp, GKRAuxLayoutData, GKRCircuitArtifact,
    GKRLayerDescription, GateArtifacts, InitsOrTeardownsTimestampAndValue, NoFieldGKRCacheRelation,
    NoFieldGKRRelation, NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldSpecialMemoryContributionRelation, OutputType,
};
pub(crate) use cs::tables::{TableDriver, TableType};

// -----------------------------------------------------------------------
// `field` — base field, extension towers
// -----------------------------------------------------------------------
//
// E6 (`BabyBearExt6`) is included even though it has no current consumer;
// the upstream surface keeps it for planned E6 work, and surfacing it here
// makes that future-availability explicit.

pub(crate) use field::baby_bear::base::BabyBearField;
pub(crate) use field::baby_bear::ext2::BabyBearExt2;
pub(crate) use field::baby_bear::ext4::BabyBearExt4;
pub(crate) use field::baby_bear::ext6::BabyBearExt6;
pub(crate) use field::{Field, FieldExtension, PrimeField};

// -----------------------------------------------------------------------
// `prover` — CPU prover types the GPU prover mirrors / interoperates with
// -----------------------------------------------------------------------

pub(crate) use prover::definitions::{GKRExternalChallenges, SecurityLevel, Transcript};
pub(crate) use prover::gkr::high_bits_offset_for_inits_and_teardowns;
pub(crate) use prover::gkr::prover::dimension_reduction::{
    self, forward::DimensionReducingInputOutput,
};
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub(crate) use prover::gkr::prover::stages::stage1::{
    self, commit_trace_part, ColumnMajorCosetBoundTracePart,
};
pub(crate) use prover::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_query_bits, draw_random_field_els,
};
pub(crate) use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
pub(crate) use prover::gkr::prover::{
    forward_loop, prove_configured_with_gkr, sumcheck_loop, GKRProof,
    SumcheckIntermediateProofValues, WhirSchedule,
};
pub(crate) use prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture;
pub(crate) use prover::gkr::prover_config::ProverConfig;
pub(crate) use prover::gkr::sumcheck::access_and_fold::{
    BaseFieldPoly, GKRLayerSource, GKRStorage,
};
pub(crate) use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
pub(crate) use prover::gkr::sumcheck::evaluate_small_univariate_poly;
pub(crate) use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchedGKRKernel, ExtensionCopyGKRRelation, GKRInputs,
    LookupBaseExtMinusBaseExtGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
    LookupBasePairGKRRelation, LookupExtensionMinusMultiplicityByExtensionGKRRelation,
    LookupExtensionPairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
pub(crate) use prover::gkr::virtual_polys::init_and_teardown_base::{
    evaluate_virtual_inits_and_teardowns_base_address_setup_polys,
    materialize_virtual_inits_and_teardowns_base_address_setup_poly,
};
pub(crate) use prover::gkr::virtual_polys::range_check::{
    evaluate_virtual_range_check_setup_poly, materialize_virtual_range_check_setup_poly,
};
pub(crate) use prover::gkr::whir::hypercube_to_monomial::{
    multivariate_coeffs_into_hypercube_evals, multivariate_hypercube_evals_into_coeffs,
};
pub(crate) use prover::gkr::whir::{
    whir_fold, BaseFieldQuery, ColumnMajorBaseOracleForLDE, ColumnMajorExtensionOracleForCoset,
    ColumnMajorExtensionOracleForLDE, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries,
    WhirCommitment, WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
pub(crate) use prover::gkr::witness_gen::delegation_circuits::{
    evaluate_gkr_memory_witness_for_delegation_circuit, evaluate_gkr_witness_for_delegation_circuit,
};
pub(crate) use prover::gkr::witness_gen::family_circuits::{
    evaluate_gkr_memory_witness_for_executor_family, evaluate_gkr_witness_for_executor_family,
    evaluate_init_and_teardown_memory_witness, GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
pub(crate) use prover::gkr::witness_gen::oracles::{MemoryCircuitOracle, NonMemoryCircuitOracle};
pub(crate) use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
pub(crate) use prover::merkle_trees::{
    ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, MerkleTreeCapVarLength,
};
pub(crate) use prover::query_utils::{assemble_query_index, BitSource};
pub(crate) use prover::tracers::oracles::transpiler_oracles::delegation::{
    BigintDelegationOracle, Blake2sDelegationOracle, KeccakDelegationOracle,
};
pub(crate) use prover::transcript::Seed;
pub(crate) use prover::utils::extension_field_from_base_coeffs;

// -----------------------------------------------------------------------
// `setups` — compiled-circuit binary loading
// -----------------------------------------------------------------------

pub(crate) use setups::circuits::{
    get_bigint_with_control_circuit_setup, get_blake2_g_function_circuit_setup,
    get_blake2_with_compression_circuit_setup, get_keccak_special5_circuit_setup,
};
pub(crate) use setups::pad_bytecode_for_proving;
pub(crate) use setups::unrolled_circuits::{
    add_sub_lui_auipc_mop_circuit_setup, inits_and_teardowns_circuit_setup,
    jump_branch_slt_circuit_setup, load_store_subword_only_circuit_setup,
    load_store_word_only_circuit_setup, mul_div_unsigned_circuit_setup, shift_binary_circuit_setup,
};
pub(crate) use setups::{
    inits_and_teardowns, read_binary, AddSubLuiAuipcMopCircuit, BigIntDelegationCircuit,
    Blake2sGFunctionDelegationCircuit, Blake2sWithCompressionDelegationCircuit,
    JumpBranchSltCircuit, KeccakSpecial5DelegationCircuit, LoadStoreSubwordOnlyCircuit,
    LoadStoreWordOnlyCircuit, ShiftBinaryCircuit, UnsignedMulDivCircuit,
};

// -----------------------------------------------------------------------
// `prover` — final-register snapshot type
// -----------------------------------------------------------------------

pub(crate) use prover::definitions::FinalRegisterValue;

// -----------------------------------------------------------------------
// `trace_and_split` — Fiat-Shamir transform for permutation argument
// -----------------------------------------------------------------------

pub(crate) use trace_and_split::fs_transform_for_permutation_argument;
