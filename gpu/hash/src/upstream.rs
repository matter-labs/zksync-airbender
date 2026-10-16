//! Upstream re-export manifest for `gpu_hash`.
//!
//! Production code is `gpu_core`-only. The test suites verify the GPU
//! kernels against host references — the `field` trait, the host blake2s
//! (`blake2s_u32`), and the host Fiat-Shamir transcript (`transcript::Seed` +
//! `prover`'s `Blake2sTranscript` and challenge-draw helpers). All are dev-only,
//! so this shim is `#[cfg(test)]` and none of it leaks downstream.

#[cfg(test)]
pub(crate) use blake2s_u32::Blake2sState;
#[cfg(test)]
pub(crate) use field::Field;
#[cfg(test)]
pub(crate) use prover::gkr::prover::transcript_utils::{
    draw_fresh_random_field_els, draw_random_field_els,
};
#[cfg(test)]
pub(crate) use transcript::Seed;

/// Host round-count parity constant. `ROUNDS` in `native/hash.cuh` must match;
/// deriving the test references from `prover::definitions` turns silent drift
/// into a parity-test failure.
#[cfg(test)]
pub(crate) use prover::definitions::USE_REDUCED_BLAKE2_ROUNDS;

#[cfg(test)]
pub(crate) type Blake2sTranscript =
    prover::transcript::Blake2sTranscript<{ USE_REDUCED_BLAKE2_ROUNDS }>;

#[cfg(test)]
pub(crate) use fft::Twiddles;
#[cfg(test)]
pub(crate) use field::proth120::Proth120;
#[cfg(all(test, feature = "deterministic_pow"))]
pub(crate) use prover::cs::utils::split_timestamp;
#[cfg(all(test, feature = "deterministic_pow"))]
pub(crate) use prover::gkr::prover::{CommitmentMode, GKRProof};
#[cfg(test)]
pub(crate) use prover::gkr::whir::coset_commit::{
    CosetByCosetBaseCommitment, CosetByCosetExtCommitment,
};
#[cfg(test)]
pub(crate) use prover::merkle_trees::{
    keccak256_for_everything_tree::{keccak_leaf_encoding_words, Keccak256MerkleTreeWithCap},
    ColumnMajorMerkleTreeConstructor, MerkleTreeCapVarLength, PathQueryable, PlainCosetLeaves,
};
#[cfg(all(test, feature = "deterministic_pow"))]
pub(crate) use prover::query_utils::{assemble_query_index, BitSource};
#[cfg(test)]
pub(crate) use transcript::Transcript;
#[cfg(test)]
pub(crate) use transcript::{Keccak256Seed, Keccak256Transcript};
