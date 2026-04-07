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

    /// Read a single item of type `T` from the data region.
    ///
    /// # Safety
    /// The caller must ensure that `size_of::<T>() / size_of::<u32>()` words
    /// have been written via `data_write`.
    #[inline(always)]
    pub unsafe fn read_one<T: Copy>(&self) -> T {
        *self.data_as::<T>(1).get_unchecked(0)
    }
}

/// Bundles the Blake2s hasher and transcript seed used throughout verification.
///
/// Replaces the repeated `(&mut hasher, &mut seed)` parameter pair. The struct
/// is stack-allocated and zero-cost.
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

    /// Commit the contents of a `CommitBuf` to the transcript.
    #[inline(always)]
    pub fn commit<const N: usize>(&mut self, buf: &mut CommitBuf<N>, data_words: usize) {
        buf.commit(&mut self.hasher, &mut self.seed, data_words);
    }

    /// Draw raw u32 words from the transcript into `dst`.
    /// This is the low-level draw — field-specific wrappers are generated.
    #[inline(always)]
    pub fn draw_raw(&mut self, dst: &mut [u32]) {
        Blake2sTranscript::draw_randomness_using_hasher(&mut self.hasher, &mut self.seed, dst);
    }
}

/// Double-buffered workspace for `fold_coset`.
///
/// Encapsulates the A/B buffer swap pattern, hiding raw pointer arithmetic
/// behind a named interface. Both buffers use `MaybeUninit` (no zero-init).
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

    /// Get `(source, destination)` slices for the given fold round.
    ///
    /// Round 0 is special — the caller must provide the initial `evals` slice
    /// as the source. For round > 0 this method returns the correct buffer pair.
    ///
    /// The buffer swap pattern matches `fold_coset`:
    ///   - round 0 → dst = buf_a (src = external evals)
    ///   - round 1 → src = buf_a, dst = buf_b
    ///   - round 2 → src = buf_b, dst = buf_a
    ///   - ...
    ///
    /// # Safety
    /// `src_len` and `dst_len` must not exceed `N`.
    /// Source buffer must have been written to in a prior round.
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

    /// Mutable access to buf_a for writing initial fold output (round 0).
    ///
    /// # Safety
    /// `len` must not exceed `N`.
    #[inline(always)]
    pub unsafe fn dst_a(&mut self, len: usize) -> &mut [E] {
        core::slice::from_raw_parts_mut(self.buf_a.as_mut_ptr().cast::<E>(), len)
    }

    /// Get the final folded value after all rounds.
    ///
    /// # Safety
    /// At least one round must have been executed, and the result must be
    /// in the first element of the appropriate buffer.
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
