//! Single-file audit point for items this crate consumes from upstream crates
//! (`full_statement_verifier`, `prover`, `setups`, `common_constants`,
//! `verifier_common`). Same convention as `circuit_prover::upstream` /
//! `execution_prover::upstream`: consumers import upstream items exclusively
//! through `crate::upstream`.

// `full_statement_verifier` — the program-level proof container and (behind
// the `verifiers` feature) the native verifier entry points.
pub use full_statement_verifier::program_proof::ProgramProof;
#[cfg(feature = "verifiers")]
pub use full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer;
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
