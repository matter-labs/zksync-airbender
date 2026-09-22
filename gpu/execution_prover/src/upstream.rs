//! Upstream imports for the GPU execution backend. Keep them here so upstream
//! API changes surface in one place.
//!
//! Consumers under `gpu/execution_prover/src/` import upstream items
//! exclusively through `crate::upstream` — direct `use cs::…` / `use prover::…`
//! lines in backend code are forbidden. Sibling workspace crates
//! (`execution_prover`, `execution_prover_model`, `gpu_*`) are not upstream and
//! are imported directly at their call sites.
//!
//! Items reached only from the `memory_sweep` module carry that feature gate so
//! an item losing its last consumer surfaces as an `unused_imports` warning.

pub use cs::gkr_compiler::GKRCircuitArtifact;
pub use setups::UnrolledCircuitWitnessEvalFn;

// `common_constants` — ROM geometry for the sweep's synthetic unified inputs.
#[cfg(feature = "memory_sweep")]
pub use common_constants::ROM_WORD_SIZE;

// `prover` — shared proof and configuration types.
pub use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
#[cfg(feature = "memory_sweep")]
pub use prover::gkr::prover::GKRProof;
#[cfg(feature = "memory_sweep")]
pub use prover::merkle_trees::DefaultTreeConstructor;
pub use prover::merkle_trees::MerkleTreeCapVarLength;
