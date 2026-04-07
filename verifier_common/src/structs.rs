#[cfg(feature = "gkr_verify")]
use blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS,
    BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
#[cfg(feature = "gkr_verify")]
use core::mem::MaybeUninit;
#[cfg(feature = "gkr_verify")]
use transcript::{Blake2sTranscript, Seed};

/// Aligned buffer for read-then-commit patterns.
///
/// Encapsulates the layout `[seed | data | zero-padding]` required by
/// `commit_with_seed_using_hasher_and_aligned_buffer`. Callers write data
/// via `data_write(i, val)` — the seed offset is handled internally.
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

    /// Write a value at position `i` in the data region (after the seed).
    #[inline(always)]
    pub fn data_write(&mut self, i: usize, val: u32) {
        self.inner.write(BLAKE2S_DIGEST_SIZE_U32_WORDS + i, val);
    }

    /// Commit the buffer contents to the transcript.
    /// Zeros the padding tail (at most 15 words), copies seed, and calls the
    /// aligned commit path.
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
        Blake2sTranscript::commit_with_seed_using_hasher_and_aligned_buffer(
            hasher,
            seed,
            unsafe { self.inner.assume_init_ref() },
            total,
        );
    }

    /// Reinterpret the data region as a slice of `T`.
    ///
    /// # Safety
    /// The caller must ensure that `count` elements of type `T` have been
    /// written (via `data_write`) and that the alignment is correct.
    #[inline(always)]
    pub unsafe fn data_as<T>(&self, count: usize) -> &[T] {
        self.inner
            .transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, count)
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
        // Use read_volatile to force a full 32-bit load and prevent the
        // compiler from optimizing into a subword (lhu/lbu) load, which
        // the reduced RISC-V transpiler does not support.
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
