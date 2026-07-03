//! Single-file audit point for items this crate consumes from upstream crates
//! (`full_statement_verifier`, `prover`, `setups`, `common_constants`,
//! `verifier_common`). Same convention as `circuit_prover::upstream` /
//! `execution_prover::upstream`: consumers import upstream items exclusively
//! through `crate::upstream`.

// `full_statement_verifier` — the program-level proof container and (behind
// the `verifiers` feature) the native verifier entry points.
pub use full_statement_verifier::program_proof::ProgramProof;
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::unified_circuit_statement::{
    verify_unified_circuit_base_layer, verify_unified_circuit_recursion_layer,
};
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::unrolled_proof_statement::{
    verify_unrolled_base_layer, verify_unrolled_recursion_layer,
};

// `prover` — CPU-side setup commitment machinery for the per-family setup
// caps that prefix the verifier ND streams.
pub use prover::definitions::{MerkleTreeCap, SecurityLevel, DEFAULT_CAP_SIZE};
pub use prover::fft::Twiddles;
pub use prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture;
pub use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor};

// `setups` — the per-program setup-params entry the ND stream contract uses.
pub use setups::UnrolledCircuitSetupParams;

// `common_constants` — timestamp geometry for `proof_cycles`.
pub use common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};

// `verifier_common` — transcript for end-params / recursion-chain hashing and
// the debug error reporter for native verification.
pub use verifier_common::errors::DebugErrorCreator;
pub use verifier_common::transcript::Blake2sBufferingTranscript;

// PR-332 follow-up (3a5f4102): the recursion protocol helpers we asked
// upstream to export as library code. These replace the deleted
// `interim_upstream` byte-mirrors.
pub use full_statement_verifier::host_utils::{
    bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
    final_blake_mode, load_fsv_program, unified_switch_cycles, unrolled_blake_mode,
    FsvRecursionChain, DEFAULT_UNIFIED_SWITCH_CYCLES,
};
pub use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::host_utils::{native_verify_unrolled, native_verify_unified};
pub use setups::Setups;
