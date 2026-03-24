use core::mem::MaybeUninit;

use blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS,
    BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use cs::definitions::GKRAddress;
use field::Field;
use non_determinism_source::NonDeterminismSource;
use transcript::{Blake2sTranscript, Seed};

#[cfg(any(test, feature = "proof_utils"))]
pub mod flatten;

#[derive(Clone, Debug)]
pub struct LayerState<E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub prev_point: [E; ROUNDS],
    pub prev_point_len: usize,
    pub prev_claims: LazyVec<E, ADDRS>,
    pub batching_challenge: E,
}

#[derive(Clone, Debug)]
#[repr(C)]
pub struct LazyVec<V: Copy, const N: usize> {
    data: [MaybeUninit<V>; N],
    len: usize,
}

impl<V: Copy, const N: usize> LazyVec<V, N> {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            data: [MaybeUninit::uninit(); N],
            len: 0,
        }
    }

    #[inline(always)]
    pub fn push(&mut self, val: V) {
        debug_assert!(self.len < N);
        unsafe {
            self.data.get_unchecked_mut(self.len).write(val);
        }
        self.len += 1;
    }

    #[inline(always)]
    pub fn get(&self, idx: usize) -> &V {
        debug_assert!(idx < self.len);
        unsafe { self.data.get_unchecked(idx).assume_init_ref() }
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[V] {
        unsafe { core::slice::from_raw_parts(self.data.as_ptr().cast::<V>(), self.len) }
    }

    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [V] {
        unsafe { core::slice::from_raw_parts_mut(self.data.as_mut_ptr().cast::<V>(), self.len) }
    }

    #[inline(always)]
    pub const fn clear(&mut self) {
        self.len = 0;
    }

    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub unsafe fn get_unchecked(&self, idx: usize) -> &V {
        self.data.get_unchecked(idx).assume_init_ref()
    }

    #[inline(always)]
    pub unsafe fn set_unchecked(&mut self, idx: usize, val: V) {
        self.data.get_unchecked_mut(idx).write(val);
    }

    #[inline(always)]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N);
        self.len = new_len;
    }

    #[inline(always)]
    pub unsafe fn into_array(self) -> [V; N] {
        MaybeUninit::array_assume_init(self.data)
    }
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

pub struct GKRVerifierOutput<'a, E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub base_layer_addrs: &'a [GKRAddress],
    pub evaluation_point: [E; ROUNDS],
    pub evaluation_point_len: usize,
    pub grand_product_accumulator: E,
    pub additional_base_layer_openings: &'a [GKRAddress],
    pub whir_batching_challenge: E,
    pub whir_transcript_seed: Seed,
    pub base_layer_claims: LazyVec<E, ADDRS>,
}
