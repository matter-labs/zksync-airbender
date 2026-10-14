//! `verifier_evm` — generate the on-chain (EVM/Yul) GKR+WHIR verifier for a Proth120 circuit,
//! and flatten a proof into the calldata it consumes.
//!
//! Two production entry points:
//! - [`generate_verifier`]: from a [`GKRCircuitArtifact<Proth120>`](cs::gkr_compiler::GKRCircuitArtifact)
//!   (+ the prover config, PoW bits and the program's final PC), produce the merged
//!   `GkrWhirVerifier` Solidity source — GKR and WHIR verified in ONE transaction, the GKR→WHIR
//!   handoff state passed in memory (no committed state, no registry).
//! - [`flatten`] / [`seed`]: from a proof, compute the single-transaction calldata
//!   ([`merged_calldata`] = GKR stream ‖ WHIR proof stream) and the intermediate GKR→WHIR seed.
//!
//! Nothing in `src/` reads on-disk fixtures; the Solidity templates are embedded via
//! `include_str!`. Intermediate/debug artifacts live under `debug_data/` and are produced by
//! tests, never by these functions.

pub mod flatten;
pub mod generator;
pub mod seed;

pub use flatten::{gkr_calldata, merged_calldata, whir_stream};
pub use generator::{emit_circuit_yul, generate_verifier};
pub use seed::{commit_seed_preimage, gkr_whir_handoff_seed};
