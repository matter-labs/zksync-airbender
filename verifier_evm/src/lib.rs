//! `verifier_evm` — generate the on-chain (EVM/Yul) GKR+WHIR verifier for a Proth120 circuit,
//! and flatten a proof into the calldata it consumes.
//!
//! [`generate_f1_verifier`] renders the GKR/WHIR verifier and SetupFrontier data
//! contract from a circuit, ProverConfig and deployment parameters. The verifier
//! constructor takes the registry and data-contract addresses; proof acceptance
//! reports the verified statement to that registry.
//!
//! [`encoding::encode_single_tx`] encodes a proof as F1 calldata, and
//! [`verified_mark`] computes the statement returned and reported by the verifier.
//! [`seed`] builds the transcript preimage and verified statement.
//!
//! Nothing in `src/` reads on-disk fixtures; the Solidity templates are embedded via
//! `include_str!`. Intermediate/debug artifacts live under `debug_data/` and are produced by
//! tests, never by these functions.

pub mod encoding;
mod flatten;
pub mod generator;
pub mod seed;

pub use generator::{emit_circuit_yul, generate_f1_verifier, F1Contracts};
pub use seed::{commit_seed_preimage, verified_mark, VerifiedMark};
