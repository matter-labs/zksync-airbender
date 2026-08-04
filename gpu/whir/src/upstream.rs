//! Single-file manifest of every upstream item `gpu_whir` consumes.
//!
//! Production code imports upstream crates exclusively through this module.
//! `field` supplies the field-extension degree used by the production kernels
//! (`FieldExtension`). Everything else here backs the WHIR-oracle parity + query
//! test-support surface (`#[doc(hidden)] pub`, reached by the apex e2e suite),
//! which lives behind the non-default `test-utils` feature (plus `test` for the
//! crate's own tests) — so those re-exports are gated
//! `#[cfg(any(test, feature = "test-utils"))]` (or `#[cfg(test)]` for the ones
//! only whir's own tests use). Every `prover`-sourced item is test-support only;
//! `prover` nonetheless stays a **normal** (not dev-only) dependency because the
//! `deterministic_pow` feature forwards `prover/deterministic_pow` (see
//! Cargo.toml).

// -----------------------------------------------------------------------
// `field` — field-extension degree (production) + field traits (test-support)
// -----------------------------------------------------------------------
pub(crate) use field::FieldExtension;
#[cfg(any(test, feature = "test-utils"))]
pub(crate) use field::{Field, PrimeField};

// -----------------------------------------------------------------------
// `prover` — CPU WHIR reference the GPU oracle/parity helpers mirror
// (all test-support: behind `test-utils`, or `#[cfg(test)]` where only whir's
// own tests use it)
// -----------------------------------------------------------------------
#[cfg(any(test, feature = "test-utils"))]
pub(crate) use prover::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_random_field_els,
};
// CPU-reference helper only exercised by `fold::tests`.
#[cfg(test)]
pub(crate) use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
// CPU-reference helper only exercised by `fold::tests`.
#[cfg(test)]
pub(crate) use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
// `BaseFieldQuery` only exercised by `fold::debug`'s #[cfg(test)] query-parity helpers.
#[cfg(test)]
pub(crate) use prover::gkr::whir::BaseFieldQuery;
#[cfg(any(test, feature = "test-utils"))]
pub(crate) use prover::gkr::whir::WhirCommitment;
// CPU merkle-tree reference construction only exercised by `fold::tests::query_tests`.
#[cfg(test)]
pub(crate) use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
#[cfg(test)]
pub(crate) use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
#[cfg(any(test, feature = "test-utils"))]
pub(crate) use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
#[cfg(any(test, feature = "test-utils"))]
pub(crate) use prover::transcript::{Blake2sTranscript, Seed};
#[cfg(any(test, feature = "test-utils"))]
pub(crate) use prover::utils::extension_field_from_base_coeffs;
