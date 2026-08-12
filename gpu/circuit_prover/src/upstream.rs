//! Single-file audit point for items consumed from upstream crates
//! (`cs`, `prover`, `field`).
//!
//! When bumping an upstream version, scan this file first — every type,
//! function, and constant the crate depends on is re-exported here, so a
//! missing/renamed item surfaces as a compile error pointing at this
//! manifest rather than at scattered call sites. Conversely, additions to
//! this file are the documented surface contract with the upstream crates.
//!
//! Consumers under `gpu/circuit_prover/src/` import upstream items exclusively
//! through `crate::upstream` — direct `use cs::…` / `use prover::…` lines
//! in consumer code are forbidden. The manifest is the contract.
//!
//! ```ignore
//! use crate::upstream::{GKRCircuitArtifact, Field, ...};
//! ```
//!
//! The apex owns only proof assembly and configuration, so the production
//! surface is small: `proof/` + `config.rs`.
//! The e2e test suite (`tests/`) imports far more via `use crate::upstream::*`;
//! those items live in the clearly-marked `#[cfg(test)]` section below.

// -----------------------------------------------------------------------
// Production surface — referenced by `proof/**` and `config.rs`.
// -----------------------------------------------------------------------

// `cs` — circuit description, GKR layout, and compilation artifacts.
pub(crate) use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;
pub(crate) use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};

// `field` — base field.
pub(crate) use field::Field;

// `prover` — CPU prover types the GPU prover mirrors / interoperates with.
pub(crate) use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub(crate) use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
pub(crate) use prover::gkr::prover::{GKRProof, WhirSchedule};
pub(crate) use prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture;
pub(crate) use prover::gkr::prover_config::pow_bits;
pub(crate) use prover::gkr::prover_config::ProverConfig;
pub(crate) use prover::merkle_trees::DefaultTreeConstructor;

// -----------------------------------------------------------------------
// Test-only upstream items — the e2e suite (tests/) imports these via
// `use crate::upstream::*`. Excluded from the production build.
// -----------------------------------------------------------------------

#[cfg(test)]
pub(crate) use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
#[cfg(test)]
pub(crate) use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
#[cfg(test)]
pub(crate) use cs::cs::circuit_trait::Circuit;
#[cfg(test)]
pub(crate) use cs::definitions::{
    ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    BLAKE2S_DELEGATION_CSR_REGISTER, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
    KECCAK_SPECIAL5_CSR_REGISTER, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
    LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, MUL_DIV_CIRCUIT_FAMILY_IDX, NON_DETERMINISM_CSR,
    NUM_PERMUTATION_ARGUMENT_KEY_PARTS, ROM_SECOND_WORD_BITS, SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
};
#[cfg(test)]
pub(crate) use cs::gkr_circuits::{
    add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
    add_sub_lui_auipc_mop_table_addition_fn, create_mem_subword_only_special_tables,
    create_mem_word_only_special_tables,
    jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr, jump_branch_slt_table_addition_fn,
    mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr,
    mem_subword_only_table_addition_fn, mem_word_only_circuit_with_preprocessed_bytecode_for_gkr,
    mem_word_only_table_addition_fn,
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    process_binary_into_separate_tables_ext,
    shift_binop_circuit_with_preprocessed_bytecode_for_gkr, shift_binop_table_addition_fn,
    ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData,
};
#[cfg(test)]
pub(crate) use cs::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
#[cfg(test)]
pub(crate) use cs::tables::TableDriver;
#[cfg(test)]
pub(crate) use cs::utils::split_timestamp;
#[cfg(test)]
pub(crate) use field::{FieldExtension, PrimeField};
#[cfg(test)]
pub(crate) use prover::definitions::produce_initial_permutation_product_contribution;
#[cfg(test)]
pub(crate) use prover::gkr::prover::backend::NaiveBackend;
#[cfg(test)]
pub(crate) use prover::gkr::prover::prove_configured_with_gkr;
#[cfg(test)]
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
#[cfg(test)]
pub(crate) use prover::gkr::prover::stages::commitment_utils::commit_trace_part;
#[cfg(test)]
pub(crate) use prover::gkr::prover::stages::initial_commit::commit_separate_memory_and_witness_subtrees;
#[cfg(test)]
pub(crate) use prover::gkr::prover::transcript_utils::draw_query_bits;
#[cfg(test)]
pub(crate) use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
#[cfg(test)]
pub(crate) use prover::gkr::prover::CommitmentMode;
#[cfg(test)]
pub(crate) use prover::gkr::witness_gen::delegation_circuits::{
    evaluate_gkr_memory_witness_for_delegation_circuit, evaluate_gkr_witness_for_delegation_circuit,
};
#[cfg(test)]
pub(crate) use prover::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_memory_witness_for_executor_family,
    evaluate_gkr_witness_for_executor_family, evaluate_init_and_teardown_memory_witness,
    GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
#[cfg(test)]
pub(crate) use prover::gkr::witness_gen::oracles::{
    MemoryCircuitOracle, NonMemoryCircuitOracle, UnifiedRiscvCircuitOracle,
};
#[cfg(test)]
pub(crate) use prover::merkle_trees::MerkleTreeCapVarLength;
#[cfg(test)]
pub(crate) use prover::query_utils::{assemble_query_index, BitSource};
#[cfg(test)]
pub(crate) use prover::tracers::oracles::transpiler_oracles::delegation::{
    BigintDelegationOracle, Blake2sDelegationOracle, KeccakDelegationOracle,
};
#[cfg(test)]
pub(crate) use prover::transcript::{Blake2sTranscript, Seed, Transcript};
