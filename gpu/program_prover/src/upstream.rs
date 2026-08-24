//! Single-file audit point for items this crate consumes from upstream crates
//! (`full_statement_verifier`, `prover`, `setups`, `verifier_common`). Same
//! convention as `gpu_circuit_prover::upstream` /
//! `gpu_execution_prover::upstream`: consumers import upstream items exclusively
//! through `crate::upstream`.

// `full_statement_verifier` — the program-level proof container.
pub use full_statement_verifier::program_proof::ProgramProof;
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::unified_circuit_statement::{
    verify_unified_circuit_base_layer_sec_100, verify_unified_circuit_recursion_layer_sec_100,
};
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::unrolled_proof_statement::{
    verify_unrolled_base_layer_sec_100, verify_unrolled_recursion_layer_sec_100,
};

// `prover` — definitions consumed by tests only.
pub use prover::definitions::SecurityLevel;

// `setups` — the per-program setup-params entry the ND stream contract uses.
pub use setups::UnrolledCircuitSetupParams;

// The recursion protocol helpers we asked upstream to export as library code.
pub use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles;
pub use full_statement_verifier::host_utils::{
    bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
    final_blake_mode, load_fsv_program, unified_switch_cycles, unrolled_blake_mode,
    FsvRecursionChain,
};
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::host_utils::{native_verify_unified, native_verify_unrolled};
pub use setups::Setups;
pub use verifier_common::fsv_binaries::FsvProgram;
