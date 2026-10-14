//! Single-file manifest of every upstream item `gpu_whir` consumes.
//!
//! Production code imports upstream crates exclusively through this module.
//! Re-exports supply production field, WHIR proof and schedule types,
//! domain generators and constants, plus CPU references for this crate's tests.

// -----------------------------------------------------------------------
// `field` — field-extension degree (production) + field traits (test-support)
// -----------------------------------------------------------------------
pub(crate) use field::FieldExtension;
#[cfg(test)]
pub(crate) use field::{Field, PrimeField};

// -----------------------------------------------------------------------
// `prover` — CPU WHIR references used by tests
// -----------------------------------------------------------------------
// CPU-reference helper only exercised by `fold::tests`.
#[cfg(test)]
pub(crate) use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full_lsb;
// CPU-reference helper only exercised by `fold::tests`.
#[cfg(test)]
pub(crate) use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
// `BaseFieldQuery` supplies WHIR proof assembly and test query-parity helpers.
pub(crate) use prover::gkr::whir::BaseFieldQuery;
// CPU merkle-tree reference construction only exercised by `fold::tests::query_tests`.
#[cfg(test)]
pub(crate) use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
#[cfg(test)]
pub(crate) use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
#[cfg(test)]
pub(crate) use prover::merkle_trees::DefaultTreeConstructor;
pub(crate) use prover::merkle_trees::MerkleTreeCapVarLength;
#[cfg(test)]
pub(crate) use prover::merkle_trees::PathQueryable;
#[cfg(test)]
pub(crate) use prover::utils::extension_field_from_base_coeffs;

pub(crate) use fft::domain_generator_for_size;
#[allow(unused_imports)]
pub(crate) use field::Proth120;
pub(crate) use prover::gkr::prover::WhirSchedule;
pub(crate) use prover::gkr::whir::queries::ExtensionFieldQuery;
pub(crate) use prover::gkr::whir::{
    WhirBaseLayerCommitmentAndQueries, WhirCommitment, WhirIntermediateCommitmentAndQueries,
    WhirPolyCommitProof,
};
pub(crate) use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
