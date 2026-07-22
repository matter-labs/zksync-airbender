//! Single-file manifest of every upstream item `gpu_whir` consumes.
//!
//! Production code imports upstream crates exclusively through this module.
//! `field` supplies the field-extension traits; `prover` supplies the CPU WHIR
//! reference types the GPU-oracle parity + query test-support surface
//! (`#[doc(hidden)] pub`, reached by the apex e2e suite) is built against. That
//! surface is permanently compiled, so `prover` is a **normal** dependency and
//! these re-exports are ungated — see Cargo.toml for the PoW-determinism
//! feature consequence.

// -----------------------------------------------------------------------
// `field` — field-extension degree + field traits
// -----------------------------------------------------------------------
pub(crate) use field::{Field, FieldExtension, PrimeField};

// -----------------------------------------------------------------------
// `prover` — CPU WHIR reference the GPU oracle/parity helpers mirror
// -----------------------------------------------------------------------
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
pub(crate) use prover::gkr::whir::WhirCommitment;
// CPU merkle-tree reference construction only exercised by `fold::tests::query_tests`.
#[cfg(test)]
pub(crate) use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
#[cfg(test)]
pub(crate) use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
pub(crate) use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};
pub(crate) use prover::transcript::Seed;
pub(crate) use prover::utils::extension_field_from_base_coeffs;
