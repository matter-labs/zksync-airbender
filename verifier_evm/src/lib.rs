//! `verifier_evm` — generate the on-chain (EVM/Yul) GKR + WHIR verifiers for a Proth120 circuit,
//! and flatten a proof into the calldata those verifiers consume.
//!
//! Two production entry points:
//! - [`generate_verifiers`]: from a [`GKRCircuitArtifact<Proth120>`](cs::gkr_compiler::GKRCircuitArtifact)
//!   (+ PoW bits and final PC), produce the GKR/WHIR/Registry Solidity sources.
//! - [`flatten`] / [`seed`]: from a proof, compute the GKR + WHIR calldata and the intermediate
//!   GKR→WHIR commit seed.
//!
//! Nothing in `src/` reads on-disk fixtures; the Solidity templates are embedded via
//! `include_str!`. Intermediate/debug artifacts live under `debug_data/` and are produced by
//! tests, never by these functions.

pub mod flatten;
pub mod generator;
pub mod seed;

pub use flatten::{gkr_calldata, whir_calldata};
pub use generator::{emit_circuit_yul, generate_verifiers, GeneratedContracts};
pub use seed::{commit_seed_preimage, gkr_whir_handoff_seed};
