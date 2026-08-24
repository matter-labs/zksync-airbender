#![cfg_attr(all(test, feature = "verifiers"), feature(allocator_api))]
//! Program-level GPU proving driver: the top of the `gpu/` crate stack.
//!
//! Converts `gpu_execution_prover::ProveResult` into
//! `full_statement_verifier::ProgramProof`, builds the non-determinism word
//! streams the `fsv_*` verifier binaries consume, and (behind the non-default
//! `verifiers` feature) verifies proofs natively.

pub mod proof_assembly;
pub mod upstream;

pub use proof_assembly::assemble_program_proof;
pub use upstream::Setups;

#[cfg(test)]
mod tests;

#[cfg(test)]
gpu_core::force_serial_libtest!();
