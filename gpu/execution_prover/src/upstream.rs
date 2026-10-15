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
pub use execution_prover::setup::L1WrapSetup;
pub use execution_prover::CommitmentMode;
pub use execution_prover::ProofProfile;
pub use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
pub use prover::gkr::prover::GKRProof;
pub use prover::gkr::prover_config::ProverConfig;
pub use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};

// `setups` — per-circuit witness evaluators carrying the decoder tables.
#[cfg(feature = "memory_sweep")]
pub use setups::unrolled_circuits::inits_and_teardowns_circuit_setup;
pub use setups::UnrolledCircuitWitnessEvalFn;

// The capacity rows pin the exact layout and ROM used to build wrap programs.
#[cfg(feature = "memory_sweep")]
pub use unified_reduced_machine_proth120::l1_wrap_2p21;
