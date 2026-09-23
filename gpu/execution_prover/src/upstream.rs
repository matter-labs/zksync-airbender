//! Single-file audit point for items the execution orchestrator consumes from
//! upstream crates (`cs`, `prover`, `setups`). This is the
//! execution-side analogue of `gpu_circuit_prover::upstream`: a thin contract
//! surface so an upstream version bump surfaces here rather than at scattered
//! call sites.
//!
//! Consumers under `gpu/execution_prover/src/` import upstream items
//! exclusively through `crate::upstream` — direct `use cs::…` / `use prover::…`
//! lines in orchestrator code are forbidden.

// `cs` — GKR circuit artifacts.
pub use cs::gkr_compiler::GKRCircuitArtifact;

// `common_constants` — ROM geometry for unified decoder preprocessing.
pub use common_constants::ROM_WORD_SIZE;

// `prover` — CPU prover types the GPU orchestrator interoperates with.
pub use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub use prover::gkr::prover::GKRProof;
pub use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};

// `setups` — per-circuit witness evaluators carrying the decoder tables.
pub use setups::UnrolledCircuitWitnessEvalFn;
