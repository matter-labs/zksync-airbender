//! Single-file audit point for items consumed from upstream crates
//! (`cs`, `prover`, `field`).
//!
//! When bumping an upstream version, scan this file first — every type,
//! function, and constant the crate depends on is re-exported here, so a
//! missing/renamed item surfaces as a compile error pointing at this
//! manifest rather than at scattered call sites. Conversely, additions to
//! this file are the documented surface contract with the upstream crates.
//!
//! Consumers under `gpu/circuit_prover/src/` import upstream items exclusively
//! through `crate::upstream` — direct `use cs::…` / `use prover::…` lines
//! in consumer code are forbidden. The manifest is the contract.
//!
//! ```ignore
//! use crate::upstream::{GKRCircuitArtifact, Field, ...};
//! ```
//!
//! The apex owns only proof assembly and configuration, so the production
//! surface is small: `proof/` + `config.rs`.
//! The e2e test suite (`tests/`) imports far more via `use crate::upstream::*`;
//! those items live in the clearly-marked `#[cfg(test)]` section below.

// -----------------------------------------------------------------------
// Production surface — referenced by `proof/**` and `config.rs`.
// -----------------------------------------------------------------------

// `cs` — circuit description, GKR layout, and compilation artifacts.
pub(crate) use cs::definitions::{
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES, TIMESTAMP_COLUMNS_NUM_BITS,
};
pub(crate) use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};

// `field` — base field.
pub(crate) use execution_prover::setup::L1WrapSetup;
pub(crate) use execution_prover::L1WrapResult;
pub(crate) use field::Field;
#[cfg(test)]
pub(crate) use field::PrimeField;
pub(crate) use prover::common_constants::rom::RomGeometry;
// `prover` — CPU prover types the GPU prover mirrors / interoperates with.
pub(crate) use prover::definitions::{GKRExternalChallenges, SecurityLevel};
pub(crate) use prover::field::Proth120;
pub(crate) use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
pub(crate) use prover::gkr::prover::{GKRProof, WhirSchedule};
pub(crate) use prover::gkr::prover_config::commitment_geometry::{
    BaseCommitmentGeometry, BaseOracleRole,
};
pub(crate) use prover::gkr::prover_config::pow_bits;
pub(crate) use prover::gkr::prover_config::BaseColumns;
pub(crate) use prover::gkr::prover_config::{ProofProfile, ProverConfig};
pub(crate) use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
pub(crate) use prover::merkle_trees::DefaultTreeConstructor;

// -----------------------------------------------------------------------
// Test-only upstream items — the e2e suite (tests/) imports these via
// `use crate::upstream::*`. Excluded from the production build.
// -----------------------------------------------------------------------

#[cfg(test)]
pub(crate) use field::FieldExtension;
#[cfg(test)]
pub(crate) use prover::gkr::prover::backend::NaiveBackend;
#[cfg(test)]
pub(crate) use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
#[cfg(test)]
pub(crate) use prover::gkr::prover::stages::commitment_utils::commit_trace_part;
#[cfg(test)]
pub(crate) use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
pub(crate) use prover::gkr::prover::OperationMode;

pub use prover::gkr::prover::CommitmentMode;
#[cfg(test)]
pub(crate) use prover::merkle_trees::MerkleTreeCapVarLength;
#[cfg(test)]
pub(crate) use prover::transcript::{Blake2sTranscript, Transcript};
