use core::mem::MaybeUninit;

use blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS,
    BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use cs::definitions::GKRAddress;
use field::Field;
use non_determinism_source::NonDeterminismSource;
use transcript::{Blake2sTranscript, Seed};

pub use crate::lazy_vec::LazyVec;

#[cfg(any(test, feature = "proof_utils"))]
pub mod flatten;

#[derive(Clone, Debug)]
pub struct LayerState<E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub prev_point: [E; ROUNDS],
    pub prev_point_len: usize,
    pub prev_claims: LazyVec<E, ADDRS>,
    pub batching_challenge: E,
}

#[inline(always)]
pub fn read_eval_data_from_nds<I: NonDeterminismSource, const BUF: usize>(
    buf: &mut AlignedArray64<MaybeUninit<u32>, BUF>,
    data_words: usize,
) {
    let total_commit_words = BLAKE2S_DIGEST_SIZE_U32_WORDS + data_words;
    for i in 0..data_words {
        buf.write(BLAKE2S_DIGEST_SIZE_U32_WORDS + i, I::read_word());
    }
    let padded = total_commit_words.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
    unsafe { buf.zero_range(BLAKE2S_DIGEST_SIZE_U32_WORDS + data_words, padded) };
}

#[inline(always)]
pub fn commit_eval_buffer<const BUF: usize>(
    buf: &mut AlignedArray64<MaybeUninit<u32>, BUF>,
    hasher: &mut DelegatedBlake2sState,
    seed: &mut Seed,
    data_words: usize,
) {
    let total_commit_words = BLAKE2S_DIGEST_SIZE_U32_WORDS + data_words;
    buf.copy_from_slice(0, &seed.0);
    let buf_ref = unsafe { buf.assume_init_ref() };
    Blake2sTranscript::commit_with_seed_using_hasher_and_aligned_buffer(
        hasher,
        seed,
        buf_ref,
        total_commit_words,
    );
}

#[derive(Clone, Debug)]
pub enum GKRVerificationError {
    SumcheckRoundFailed { layer: usize, round: usize },
    FinalStepCheckFailed { layer: usize },
}

pub struct GKRVerifierOutput<
    'a,
    E: Field,
    const ROUNDS: usize,
    const ADDRS: usize,
    const CAP_WORDS: usize,
> {
    pub base_layer_addrs: &'a [GKRAddress],
    pub evaluation_point: [E; ROUNDS],
    pub evaluation_point_len: usize,
    pub grand_product_accumulator: E,
    pub additional_base_layer_openings: &'a [GKRAddress],
    pub whir_batching_challenge: E,
    pub whir_transcript_seed: Seed,
    pub base_layer_claims: LazyVec<E, ADDRS>,
    pub setup_cap: [u32; CAP_WORDS],
    pub memory_cap: [u32; CAP_WORDS],
    pub witness_cap: [u32; CAP_WORDS],
}
