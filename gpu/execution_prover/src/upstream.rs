//! Single-file audit point for items the execution orchestrator consumes from
//! upstream crates (`cs`, `prover`, `setups`, `trace_and_split`). This is the
//! execution-side analogue of `gpu_circuit_prover::upstream`: a thin contract
//! surface so an upstream version bump surfaces here rather than at scattered
//! call sites.
//!
//! Consumers under `gpu/execution_prover/src/` import upstream items
//! exclusively through `crate::upstream` — direct `use cs::…` / `use prover::…`
//! lines in orchestrator code are forbidden.

// `cs` — GKR circuit artifacts + decoder/opcode helpers.
pub use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
pub use cs::gkr_circuits::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
    ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData, OpcodeFamilyDecoder,
};
pub use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};

// `common_constants` — ROM geometry for unified decoder preprocessing.
pub use common_constants::ROM_WORD_SIZE;

// `prover` — CPU prover types the GPU orchestrator interoperates with.
pub use prover::definitions::{
    FinalRegisterValue, GKRExternalChallenges, SecurityLevel, USE_REDUCED_BLAKE2_ROUNDS,
};
pub use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub use prover::gkr::prover::GKRProof;
pub use prover::gkr::witness_gen::family_circuits::build_unified_table_driver;
pub use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
pub use prover::transcript::Seed;
pub type Blake2sTranscript = prover::transcript::Blake2sTranscript<{ USE_REDUCED_BLAKE2_ROUNDS }>;

// `setups` — compiled-circuit binary loading + per-circuit setup constructors.
pub use setups::circuits::{
    get_bigint_with_control_circuit_setup, get_blake2_g_function_circuit_setup,
    get_blake2_with_compression_circuit_setup, get_keccak_special5_circuit_setup,
};
pub use setups::pad_bytecode_for_proving;
pub use setups::unified_reduced_machine::get_circuit as get_unified_reduced_machine_circuit;
pub use setups::unrolled_circuits::{
    add_sub_lui_auipc_mop_circuit_setup, inits_and_teardowns_circuit_setup,
    jump_branch_slt_circuit_setup, load_store_subword_only_circuit_setup,
    load_store_word_only_circuit_setup, mul_div_unsigned_circuit_setup, shift_binary_circuit_setup,
};
pub use setups::{inits_and_teardowns, read_binary};

// `trace_and_split` — Fiat-Shamir transforms for the permutation argument.
// The transform is split per execution kind: the unrolled one absorbs
// per-family cap lists plus a dedicated inits-and-teardowns slot, the unified
// one absorbs one (inits-and-teardowns top bits, memory cap) pair per unified
// circuit (i&t are inline in the unified circuit). `derive_proof_artifacts`
// dispatches on `ExecutionKind`.
pub use trace_and_split::fs_transform_unified_for_permutation_argument;
pub use trace_and_split::fs_transform_unrolled_for_permutation_argument as fs_transform_for_permutation_argument;
