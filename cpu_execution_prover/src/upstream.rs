//! Single-file audit point for items this crate consumes from upstream crates.
//!
//! Same convention as `execution_prover::upstream`: modules under `src/` import
//! upstream items exclusively through `crate::upstream`, so an upstream rename
//! surfaces here rather than at scattered call sites.

pub(crate) use cs::definitions::split_timestamp;
pub(crate) use cs::gkr_circuits::ExecutorFamilyDecoderData;
pub(crate) use cs::gkr_compiler::GKRCircuitArtifact;
pub(crate) use cs::tables::TableDriver;
pub(crate) use cs::utils::split_u32_into_pair_u16;

pub(crate) use field::baby_bear::base::BabyBearField as BF;
pub(crate) use field::baby_bear::ext4::BabyBearExt4 as E4;
pub(crate) use field::{Field, PrimeField};

pub(crate) use prover::definitions::{
    GKRExternalChallenges, SecurityLevel, USE_REDUCED_BLAKE2_ROUNDS,
};
pub(crate) use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
pub(crate) use prover::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
pub(crate) use prover::gkr::witness_gen::family_circuits::{
    evaluate_gkr_witness_for_executor_family, evaluate_init_and_teardown_memory_witness,
    GKRFullWitnessTrace,
};
pub(crate) use prover::gkr::witness_gen::oracles::{
    MemoryCircuitOracle, NonMemoryCircuitOracle, UnifiedRiscvCircuitOracle,
};
pub(crate) use prover::tracers::oracles::transpiler_oracles::delegation::DelegationOracle;

/// The transcript the whole protocol is bound to. Spelled out rather than left
/// to the type's default, because a different round count is a different proof.
pub(crate) type Blake2sTranscript =
    prover::transcript::Blake2sTranscript<USE_REDUCED_BLAKE2_ROUNDS>;
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub(crate) use prover::gkr::prover::{
    prove_configured_with_gkr_with_backends, Backend, CommitmentMode, DefaultBabyBearBackend,
    DefaultBabyBearGKRBackend, SetupCommitment, TwiddleSetOps,
};
pub(crate) use prover::gkr::prover_config::ProverConfig;
pub(crate) use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};

pub(crate) use setups::{
    bigint_witness_eval_fn, blake2_g_function_witness_eval_fn,
    blake2_with_compression_witness_eval_fn, keccak_special5_witness_eval_fn, CircuitSetup,
    UnrolledCircuitWitnessEvalFn,
};

pub(crate) use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
pub(crate) use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionAbiDescription;
pub(crate) use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
pub(crate) use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
pub(crate) use riscv_transpiler::witness::{DelegationAbiDescription, DelegationWitness};

pub(crate) use trace_and_split::{
    commit_memory_tree_for_delegation_circuit, commit_memory_tree_for_inits_and_teardowns,
    commit_memory_tree_for_unified_circuits, commit_memory_tree_for_unrolled_mem_circuits,
    commit_memory_tree_for_unrolled_nonmem_circuits,
};
