//! Upstream imports for the shared execution orchestrator. Keep them here so
//! upstream API changes surface in one place.

// `common_constants` — ROM geometry.
pub(crate) use common_constants::ROM_WORD_SIZE;

// `cs` — decoder/opcode helpers and the compiled-circuit artifact.
pub(crate) use cs::gkr_circuits::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
    ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData,
};
pub(crate) use cs::gkr_compiler::GKRCircuitArtifact;
pub(crate) use cs::tables::TableDriver;

// `field` — base/extension field aliases used across the execution protocol.
pub(crate) use field::baby_bear::base::BabyBearField as BF;
pub(crate) use field::baby_bear::ext4::BabyBearExt4 as E4;

// `prover` — shared proof, setup and transcript types.
pub(crate) use prover::definitions::USE_REDUCED_BLAKE2_ROUNDS;
pub(crate) use prover::definitions::{FinalRegisterValue, GKRExternalChallenges, SecurityLevel};
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub(crate) use prover::gkr::prover::GKRProof;
pub(crate) use prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture;
pub(crate) use prover::gkr::prover_config::ProverConfig;
#[cfg(test)]
pub(crate) use prover::gkr::witness_gen::family_circuits::build_unified_table_driver;
pub(crate) use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
pub(crate) use prover::transcript::Seed;
pub type Blake2sTranscript = prover::transcript::Blake2sTranscript<{ USE_REDUCED_BLAKE2_ROUNDS }>;

// `trace_and_split` — Fiat-Shamir transforms, split per execution kind.
pub(crate) use trace_and_split::fs_transform_unified_for_permutation_argument;
pub(crate) use trace_and_split::fs_transform_unrolled_for_permutation_argument as fs_transform_for_permutation_argument;

// `setups` — canonical per-circuit setup construction.
pub(crate) use setups::circuits::{
    get_bigint_with_control_circuit_setup, get_blake2_g_function_circuit_setup,
    get_blake2_with_compression_circuit_setup, get_keccak_special5_circuit_setup,
    DelegationCircuitSetup,
};
pub(crate) use setups::unrolled_circuits::{
    add_sub_lui_auipc_mop_circuit_setup, inits_and_teardowns_circuit_setup,
    jump_branch_slt_circuit_setup, load_store_subword_only_circuit_setup,
    load_store_word_only_circuit_setup, mul_div_unsigned_circuit_setup, shift_binary_circuit_setup,
    unified_reduced_machine_circuit_setup,
};
pub(crate) use setups::{pad_bytecode_for_proving, CircuitSetup, UnrolledCircuitWitnessEvalFn};
