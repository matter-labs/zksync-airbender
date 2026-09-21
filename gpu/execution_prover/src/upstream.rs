//! Single-file audit point for items the execution orchestrator consumes from
//! upstream crates (`cs`, `prover`, `common_constants`). This is the
//! execution-side analogue of `gpu_circuit_prover::upstream`: a thin contract
//! surface so an upstream version bump surfaces here rather than at scattered
//! call sites.
//!
//! Consumers under `gpu/execution_prover/src/` import upstream items
//! exclusively through `crate::upstream` — direct `use cs::…` / `use prover::…`
//! lines in orchestrator code are forbidden. Sibling workspace crates
//! (`execution_prover`, `execution_prover_model`, `gpu_*`) are not upstream and
//! are imported directly at their call sites.
//!
//! Items reached only from the `memory_sweep` module carry that feature gate so
//! an item losing its last consumer surfaces as an `unused_imports` warning.

// `cs` — GKR circuit artifacts + the executor-family decoder payload.
pub use cs::gkr_circuits::ExecutorFamilyDecoderData as CSExecutorFamilyDecoderData;
pub use cs::gkr_compiler::GKRCircuitArtifact;

// `common_constants` — ROM geometry for the sweep's synthetic unified inputs.
#[cfg(feature = "memory_sweep")]
pub use common_constants::ROM_WORD_SIZE;

// `prover` — CPU prover types the GPU orchestrator interoperates with.
pub use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
#[cfg(feature = "memory_sweep")]
pub use prover::gkr::prover::GKRProof;
#[cfg(feature = "memory_sweep")]
pub use prover::merkle_trees::DefaultTreeConstructor;
pub use prover::merkle_trees::MerkleTreeCapVarLength;
