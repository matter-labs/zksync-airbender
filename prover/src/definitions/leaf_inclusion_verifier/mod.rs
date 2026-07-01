use crate::definitions::MerkleTreeCap;
use crate::definitions::USE_REDUCED_BLAKE2_ROUNDS;
use blake2s_u32::AlignedSlice64;
use field::PrimeField;
use core::fmt::Debug;
use non_determinism_source::NonDeterminismSource;

mod blake2s_for_everything;
pub use self::blake2s_for_everything::Blake2sForEverythingVerifier;

mod blake2s_for_everything_with_alternative_compression;
pub use self::blake2s_for_everything_with_alternative_compression::Blake2sForEverythingVerifierWithAlternativeCompression;

pub trait LeafInclusionVerifier<F: PrimeField>: 'static + Send + Sync + Debug {
    fn new() -> Self;
    unsafe fn verify_leaf_inclusion<
        I: NonDeterminismSource<F>,
        const CAP_SIZE: usize,
        const NUM_COSETS: usize,
    >(
        &mut self,
        coset_index: u32,
        leaf_index: u32,
        depth: usize,
        leaf_encoding: &AlignedSlice64<u32>,
        merkle_cap: &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
        nd_source: &mut I,
    ) -> bool;
}
