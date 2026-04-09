#[cfg(feature = "gkr_verify")]
use blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS,
    BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
#[cfg(feature = "gkr_verify")]
use core::mem::MaybeUninit;
#[cfg(feature = "gkr_verify")]
use transcript::{Blake2sTranscript, Seed};

/// layout `[seed | data | zero-padding]`
/// Callers write data via `data_write(i, val)` — the seed offset is handled internally.
#[cfg(feature = "gkr_verify")]
pub struct CommitBuf<const N: usize> {
    inner: AlignedArray64<MaybeUninit<u32>, N>,
}

#[cfg(feature = "gkr_verify")]
impl<const N: usize> CommitBuf<N> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            inner: AlignedArray64::new_uninit(),
        }
    }

    #[inline(always)]
    pub fn data_write(&mut self, i: usize, val: u32) {
        self.inner.write(BLAKE2S_DIGEST_SIZE_U32_WORDS + i, val);
    }

    #[inline(always)]
    pub fn commit(
        &mut self,
        hasher: &mut DelegatedBlake2sState,
        seed: &mut Seed,
        data_words: usize,
    ) {
        let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + data_words;
        let padded = total.next_multiple_of(BLAKE2S_BLOCK_SIZE_U32_WORDS);
        debug_assert!(padded <= N);
        if padded > total {
            unsafe { self.inner.zero_range(total, padded) };
        }
        self.inner.copy_from_slice(0, &seed.0);
        #[cfg(any(feature = "blake2_with_compression", feature = "blake2_g_function"))]
        {
            Blake2sTranscript::commit_with_seed_using_hasher_and_aligned_buffer(
                hasher,
                seed,
                unsafe { self.inner.assume_init_ref() },
                total,
            );
        }
        #[cfg(not(any(feature = "blake2_with_compression", feature = "blake2_g_function")))]
        {
            let buf = unsafe { self.inner.assume_init_ref() };
            // Skip the seed region — commit_with_seed_using_hasher prepends it internally.
            Blake2sTranscript::commit_with_seed_using_hasher(
                hasher,
                seed,
                &buf[BLAKE2S_DIGEST_SIZE_U32_WORDS..total],
            );
        }
    }

    #[inline(always)]
    pub unsafe fn data_as<T>(&self, count: usize) -> &[T] {
        self.inner
            .transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, count)
    }

    #[inline(always)]
    pub unsafe fn read_one<T: Copy>(&self) -> T {
        *self.data_as::<T>(1).get_unchecked(0)
    }
}

#[cfg(feature = "gkr_verify")]
pub struct TranscriptState {
    pub hasher: DelegatedBlake2sState,
    pub seed: Seed,
}

#[cfg(feature = "gkr_verify")]
impl TranscriptState {
    #[inline(always)]
    pub fn new(seed: Seed) -> Self {
        Self {
            hasher: DelegatedBlake2sState::new(),
            seed,
        }
    }

    #[inline(always)]
    pub fn commit<const N: usize>(&mut self, buf: &mut CommitBuf<N>, data_words: usize) {
        buf.commit(&mut self.hasher, &mut self.seed, data_words);
    }

    #[inline(always)]
    pub fn draw_raw(&mut self, dst: &mut [u32]) {
        Blake2sTranscript::draw_randomness_using_hasher(&mut self.hasher, &mut self.seed, dst);
    }
}

#[cfg(feature = "gkr_verify")]
pub struct FoldBuffers<E: Copy, const N: usize> {
    buf_a: [MaybeUninit<E>; N],
    buf_b: [MaybeUninit<E>; N],
}

#[cfg(feature = "gkr_verify")]
impl<E: Copy, const N: usize> FoldBuffers<E, N> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            buf_a: unsafe { MaybeUninit::uninit().assume_init() },
            buf_b: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }

    #[inline(always)]
    pub unsafe fn src_dst(
        &mut self,
        round: usize,
        src_len: usize,
        dst_len: usize,
    ) -> (&[E], &mut [E]) {
        if round % 2 == 0 {
            let src = core::slice::from_raw_parts(self.buf_b.as_ptr().cast::<E>(), src_len);
            let dst = core::slice::from_raw_parts_mut(self.buf_a.as_mut_ptr().cast::<E>(), dst_len);
            (src, dst)
        } else {
            let src = core::slice::from_raw_parts(self.buf_a.as_ptr().cast::<E>(), src_len);
            let dst = core::slice::from_raw_parts_mut(self.buf_b.as_mut_ptr().cast::<E>(), dst_len);
            (src, dst)
        }
    }

    #[inline(always)]
    pub unsafe fn dst_a(&mut self, len: usize) -> &mut [E] {
        core::slice::from_raw_parts_mut(self.buf_a.as_mut_ptr().cast::<E>(), len)
    }

    #[inline(always)]
    pub unsafe fn result(&self, num_rounds: usize) -> E {
        if num_rounds % 2 == 1 {
            *self.buf_a.get_unchecked(0).assume_init_ref()
        } else {
            *self.buf_b.get_unchecked(0).assume_init_ref()
        }
    }
}

pub struct BitSource<'a> {
    u32_values: &'a [u32],
    index: usize,
}

impl<'a> BitSource<'a> {
    pub fn new(u32_values: &'a [u32]) -> Self {
        Self {
            u32_values,
            index: 0,
        }
    }
}

impl<'a> Iterator for BitSource<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.u32_values.len() * (u32::BITS as usize) {
            return None;
        }

        let word_index = self.index / (u32::BITS as usize);
        let bit_index = self.index % (u32::BITS as usize);
        let word = unsafe { core::ptr::read_volatile(&self.u32_values[word_index]) };
        let bit = (word >> bit_index) & 1;
        self.index += 1;

        Some(bit as usize)
    }
}

pub fn assemble_query_index(
    num_bits: usize,
    bit_source: &mut impl Iterator<Item = usize>,
) -> usize {
    // assemble as LE
    debug_assert!(num_bits <= usize::BITS as usize);
    let mut result = 0usize;
    for i in 0..num_bits {
        result |= unsafe { bit_source.next().unwrap_unchecked() } << i;
    }

    result
}

pub fn bitreverse_for_bitlength(num: u32, bitlength: u32) -> u32 {
    let shift = u32::BITS - bitlength;
    num.reverse_bits() >> shift
}
