#![cfg_attr(not(feature = "pow"), no_std)]

use blake2s_u32::*;

pub use blake2s_u32;
use field::{FieldExtension, PrimeField};

#[cfg(feature = "pow")]
pub mod pow;

pub trait Transcript<F: PrimeField, E: FieldExtension<F>>: 'static + Send + Sync + Clone + Copy + Default {
    type Seed: 'static + Send + Sync + Clone + Copy + Default;
    type Hasher: 'static + Send + Sync + Clone + Copy + Default;

    fn commit_initial_u32(input: &[u32]) -> Self::Seed;
    fn commit_u32_with_seed(seed: &mut Seed, input: &[u32]);
    fn commit_initial_u32_using_hasher(
        hasher: &mut Self::Hasher,
        input: &[u32],
    ) -> Self::Seed;
    fn commit_u32_with_seed_using_hasher(
        hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        input: &[u32],
    );

    // TODO: more pub methods from Blake2sTranscript

    // absorbing field elements
    fn commit_base_field_elements(seed: &mut Seed, els: &[F]);
    fn commit_extension_field_elements(seed: &mut Seed, els: &[E]);
    fn draw_random_field_elements(
        seed: &mut Seed,
        buffer: &mut [E],
    );
}

// Our transcript for verifier efficiency is effectively stateless and has 3 functions:
// - commit initial -> seed
// - commit using some seed -> new seed
// - use seed -> (randomness, new_see)

#[derive(Clone, Copy, Debug, Default)]
pub struct Blake2sTranscript<const REDUCED_ROUNDS: bool = true>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Seed(pub [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]);

impl<const REDUCED_ROUNDS: bool> Blake2sTranscript<REDUCED_ROUNDS> {
    pub fn commit_initial(input: &[u32]) -> Seed {
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();
        let mut offset = 0;
        unsafe {
            Self::commit_inner(&mut hasher, input, &mut offset);
            Self::flush(&mut hasher, offset);
        }

        Seed(hasher.read_state_for_output())
    }

    pub fn commit_with_seed(seed: &mut Seed, input: &[u32]) {
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();
        let mut offset = 0;
        unsafe {
            Self::commit_inner(&mut hasher, &seed.0, &mut offset);
            Self::commit_inner(&mut hasher, input, &mut offset);
            Self::flush(&mut hasher, offset);
        }

        *seed = Seed(hasher.read_state_for_output());
    }

    /// Transcript implementation can use the pre-allocated hasher, and will drive it by itself
    #[inline(never)]
    pub fn commit_initial_using_hasher(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        input: &[u32],
    ) -> Seed {
        let mut offset = 0;
        unsafe {
            hasher.reset();
            Self::commit_inner(hasher, input, &mut offset);
            Self::flush(hasher, offset);
        }

        Seed(hasher.read_state_for_output())
    }

    pub fn commit_with_seed_using_hasher(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        seed: &mut Seed,
        input: &[u32],
    ) {
        let mut offset = 0;
        unsafe {
            hasher.reset();
            Self::commit_inner(hasher, &seed.0, &mut offset);
            Self::commit_inner(hasher, input, &mut offset);
            Self::flush(hasher, offset);
        }

        *seed = Seed(hasher.read_state_for_output());
    }

    /// Commit from a pre-arranged aligned buffer where `[seed | data | zero-padding]` is
    /// already laid out in 16-word aligned blocks. Avoids the memcopy that `commit_with_seed`
    /// performs. Unused words in the last block must be zeroed by the caller.
    /// `total_words` is the number of meaningful words (seed + data, excluding padding).
    #[inline(always)]
    pub fn commit_with_seed_using_hasher_and_aligned_buffer<const N: usize>(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        seed: &mut Seed,
        buf: &AlignedArray64<u32, N>,
        total_words: usize,
    ) {
        hasher.reset();
        let num_full_blocks = total_words / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let last_block_words = total_words % BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let num_blocks = num_full_blocks + if last_block_words > 0 { 1 } else { 0 };
        unsafe {
            for i in 0..num_blocks - 1 {
                let block_ptr = (buf.as_ptr()).add(i * BLAKE2S_BLOCK_SIZE_U32_WORDS);
                let block =
                    &*(block_ptr as *const AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>);
                hasher.run_round_function_with_input::<REDUCED_ROUNDS>(
                    block,
                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                    false,
                );
            }
            let last_ptr = (buf.as_ptr()).add((num_blocks - 1) * BLAKE2S_BLOCK_SIZE_U32_WORDS);
            let last_block =
                &*(last_ptr as *const AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>);
            let last_active = if last_block_words > 0 {
                last_block_words
            } else {
                BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            hasher.run_round_function_with_input::<REDUCED_ROUNDS>(last_block, last_active, true);
        }
        *seed = Seed(hasher.read_state_for_output());
    }

    /// Commit from a pre-arranged aligned buffer where `[data | zero-padding]` is
    /// already laid out in 16-word aligned blocks. Avoids the memcopy that `commit_with_seed`
    /// performs. Unused words in the last block must be zeroed by the caller.
    /// `total_words` is the number of meaningful words (seed + data, excluding padding).
    #[inline(always)]
    pub unsafe fn commit_initial_using_hasher_and_aligned_buffer(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        buf: &[AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>],
        total_words: usize,
    ) -> Seed {
        hasher.reset();
        let num_full_blocks = total_words / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let last_block_words = total_words % BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let num_blocks = num_full_blocks + if last_block_words > 0 { 1 } else { 0 };
        unsafe {
            for i in 0..num_blocks - 1 {
                let block_ptr = (buf.as_ptr()).add(i);
                hasher.run_round_function_with_input::<REDUCED_ROUNDS>(
                    block_ptr.as_ref_unchecked(),
                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                    false,
                );
            }
            let last_ptr = (buf.as_ptr()).add(num_blocks - 1);
            let last_active = if last_block_words > 0 {
                last_block_words
            } else {
                BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            hasher.run_round_function_with_input::<REDUCED_ROUNDS>(
                last_ptr.as_ref_unchecked(),
                last_active,
                true,
            );
        }
        Seed(hasher.read_state_for_output())
    }

    unsafe fn commit_inner(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        input: &[u32],
        offset: &mut usize,
    ) {
        debug_assert!(input.len() > 0);
        // hasher is in the proper state, and we just need to drive it effectively computing blake2s hash over input sequence
        let input_len_words = input.len();
        let effective_input_len = *offset + input_len_words;
        let mut num_rounds = effective_input_len / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        if effective_input_len % BLAKE2S_BLOCK_SIZE_U32_WORDS > 0 {
            num_rounds += 1;
        }
        let mut remaining = input_len_words;
        let mut input_ptr = input.as_ptr();
        let mut buffer_offset = *offset;
        for _ in 0..num_rounds {
            let mut dst_ptr: *mut u32 = hasher
                .input_buffer
                .as_mut_ptr()
                .cast::<u32>()
                .add(buffer_offset);
            let words_to_use =
                core::cmp::min(remaining, BLAKE2S_BLOCK_SIZE_U32_WORDS - buffer_offset);
            crate::spec_memcopy_u32_nonoverlapping(input_ptr, dst_ptr, words_to_use);
            remaining -= words_to_use;
            buffer_offset += words_to_use;
            input_ptr = input_ptr.add(words_to_use);
            dst_ptr = dst_ptr.add(words_to_use);
            // zero out the rest
            crate::spec_memzero_u32(
                dst_ptr,
                hasher.input_buffer.as_mut_ptr_range().end.cast::<u32>(),
            );
            if remaining > 0 {
                debug_assert_eq!(buffer_offset, BLAKE2S_BLOCK_SIZE_U32_WORDS);
                hasher.run_round_function::<REDUCED_ROUNDS>(BLAKE2S_BLOCK_SIZE_U32_WORDS, false);

                buffer_offset = 0;
            }
        }
        *offset = buffer_offset;
    }

    #[inline(always)]
    unsafe fn flush(hasher: &mut blake2s_u32::DelegatedBlake2sState, offset: usize) {
        hasher.run_round_function::<REDUCED_ROUNDS>(offset, true);
    }

    pub fn draw_randomness(seed: &mut Seed, dst: &mut [u32]) {
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();
        Self::draw_randomness_using_hasher(&mut hasher, seed, dst);
    }

    pub fn draw_randomness_using_hasher(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        seed: &mut Seed,
        dst: &mut [u32],
    ) {
        debug_assert_eq!(
            dst.len() % BLAKE2S_DIGEST_SIZE_U32_WORDS,
            0,
            "please pad the dst buffer to the multiple of {}",
            BLAKE2S_DIGEST_SIZE_U32_WORDS
        );
        let num_rounds = dst.len() / BLAKE2S_DIGEST_SIZE_U32_WORDS;
        unsafe {
            let mut dst_ptr: *mut u32 = dst.as_mut_ptr().cast::<u32>();
            // first we can just take values from the seed
            crate::spec_memcopy_u32_nonoverlapping(
                seed.0.as_ptr().cast::<u32>(),
                dst_ptr,
                BLAKE2S_DIGEST_SIZE_U32_WORDS,
            );
            dst_ptr = dst_ptr.add(BLAKE2S_DIGEST_SIZE_U32_WORDS);
            // and if we need more - we will hash it with the increasing sequence counter
            for _ in 1..(num_rounds as u32) {
                Self::draw_randomness_inner(hasher, seed);
                crate::spec_memcopy_u32_nonoverlapping(
                    seed.0.as_ptr().cast::<u32>(),
                    dst_ptr,
                    BLAKE2S_DIGEST_SIZE_U32_WORDS,
                );
                dst_ptr = dst_ptr.add(BLAKE2S_DIGEST_SIZE_U32_WORDS);
            }
        }
    }

    #[unroll::unroll_for_loops]
    #[inline(always)]
    unsafe fn draw_randomness_inner(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        seed: &mut Seed,
    ) {
        hasher.reset();
        crate::spec_memcopy_u32_nonoverlapping(
            seed.0.as_ptr().cast::<u32>(),
            hasher.input_buffer.as_mut_ptr().cast::<u32>(),
            BLAKE2S_DIGEST_SIZE_U32_WORDS,
        );
        crate::spec_memzero_u32(
            hasher
                .input_buffer
                .as_mut_ptr()
                .cast::<u32>()
                .add(BLAKE2S_DIGEST_SIZE_U32_WORDS),
            hasher.input_buffer.as_mut_ptr_range().end.cast::<u32>(),
        );

        if blake2s_u32::DelegatedBlake2sState::SUPPORT_SPEC_SINGLE_ROUND {
            unsafe {
                hasher.spec_run_single_round_into_destination::<REDUCED_ROUNDS>(
                    BLAKE2S_DIGEST_SIZE_U32_WORDS,
                    &mut seed.0 as *mut _,
                );
            }
        } else {
            // we take the seed + sequence id, and produce hash
            hasher.run_round_function::<REDUCED_ROUNDS>(BLAKE2S_DIGEST_SIZE_U32_WORDS, true);

            seed.0 = hasher.read_state_for_output();
        }
    }

    #[inline(always)]
    pub fn pow_threshold(pow_bits: u32) -> u32 {
        u32::MAX.checked_shr(pow_bits).unwrap_or(0)
    }

    pub fn verify_pow(seed: &mut Seed, nonce: u64, pow_bits: u32) {
        let mut hasher = blake2s_u32::DelegatedBlake2sState::new();
        Self::verify_pow_using_hasher(&mut hasher, seed, nonce, pow_bits);
    }

    pub fn verify_pow_using_hasher(
        hasher: &mut blake2s_u32::DelegatedBlake2sState,
        seed: &mut Seed,
        nonce: u64,
        pow_bits: u32,
    ) {
        assert!(pow_bits <= 32);
        unsafe {
            hasher.reset();
            // first we can just take values from the seed
            crate::spec_memcopy_u32_nonoverlapping(
                seed.0.as_ptr().cast::<u32>(),
                hasher.input_buffer.as_mut_ptr().cast::<u32>(),
                BLAKE2S_DIGEST_SIZE_U32_WORDS,
            );
            // LE words of nonce
            hasher.input_buffer[8] = nonce as u32;
            hasher.input_buffer[9] = (nonce >> 32) as u32;
            crate::spec_memzero_u32(
                hasher
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(BLAKE2S_DIGEST_SIZE_U32_WORDS + 2),
                hasher.input_buffer.as_mut_ptr_range().end.cast::<u32>(),
            );

            hasher.run_round_function::<REDUCED_ROUNDS>(BLAKE2S_DIGEST_SIZE_U32_WORDS + 2, true);
        }

        // check that first element is small enough
        assert!(
            hasher.state[0] <= Self::pow_threshold(pow_bits),
            "we expect {} bits of PoW using nonce {}, but top word is 0x{:08x} and full state is {:?}",
            pow_bits,
            nonce,
            hasher.state[0],
            &hasher.state,
        );

        // copy it out
        *seed = Seed(hasher.read_state_for_output());
    }
}

#[derive(Clone, Debug)]
pub struct Blake2sBufferingTranscript<const REDUCED_ROUNDS: bool = true> {
    state: DelegatedBlake2sState,
    buffer_offset: usize,
}

impl<const REDUCED_ROUNDS: bool> Blake2sBufferingTranscript<REDUCED_ROUNDS> {
    pub fn new() -> Self {
        Self {
            state: DelegatedBlake2sState::new(),
            buffer_offset: 0,
        }
    }

    pub fn get_current_buffer_offset(&self) -> usize {
        self.buffer_offset
    }

    pub fn absorb(&mut self, values: &[u32]) {
        unsafe {
            let mut to_absorb = values.len();
            let mut src_ptr = values.as_ptr();
            while to_absorb > 0 {
                let absorb_this_round =
                    core::cmp::min(to_absorb, BLAKE2S_BLOCK_SIZE_U32_WORDS - self.buffer_offset);
                crate::spec_memcopy_u32_nonoverlapping(
                    src_ptr,
                    self.state
                        .input_buffer
                        .as_mut_ptr()
                        .cast::<u32>()
                        .add(self.buffer_offset),
                    absorb_this_round,
                );
                src_ptr = src_ptr.add(absorb_this_round);
                self.buffer_offset += absorb_this_round;
                to_absorb -= absorb_this_round;
                // if we have more - run round function, otherwise - we will do final one in finalize
                if to_absorb > 0 {
                    self.run_absorb();
                }
            }
        }
    }

    #[inline(always)]
    unsafe fn run_absorb(&mut self) {
        debug_assert_eq!(self.buffer_offset, BLAKE2S_BLOCK_SIZE_U32_WORDS);

        self.state
            .run_round_function::<REDUCED_ROUNDS>(BLAKE2S_BLOCK_SIZE_U32_WORDS, false);

        self.buffer_offset = 0;
    }

    // Pad whatever is in the buffer by 0s and run round function. This
    // works as-if we absorbed enough zeroes, but allows to only keep the state
    // and `t` and not buffer state if we want to propagate it into another
    // computation
    pub unsafe fn pad(&mut self) {
        crate::spec_memzero_u32(
            self.state
                .input_buffer
                .as_mut_ptr()
                .cast::<u32>()
                .add(self.buffer_offset),
            self.state.input_buffer.as_mut_ptr_range().end.cast::<u32>(),
        );
        self.buffer_offset = BLAKE2S_BLOCK_SIZE_U32_WORDS;
    }

    pub fn finalize(mut self) -> Seed {
        // easy - always run a final round
        unsafe {
            crate::spec_memzero_u32(
                self.state
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(self.buffer_offset),
                self.state.input_buffer.as_mut_ptr_range().end.cast::<u32>(),
            );
            self.state
                .run_round_function::<REDUCED_ROUNDS>(self.buffer_offset, true);
        }

        Seed(self.state.read_state_for_output())
    }

    pub fn finalize_reset(&mut self) -> Seed {
        // easy - always run a final round
        unsafe {
            crate::spec_memzero_u32(
                self.state
                    .input_buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(self.buffer_offset),
                self.state.input_buffer.as_mut_ptr_range().end.cast::<u32>(),
            );
            self.state
                .run_round_function::<REDUCED_ROUNDS>(self.buffer_offset, true);
        }

        let seed = Seed(self.state.read_state_for_output());

        self.state.reset();
        self.buffer_offset = 0;

        seed
    }
}

pub struct TranscriptState<const REDUCED_ROUNDS: bool = true> {
    pub hasher: DelegatedBlake2sState,
    pub seed: Seed,
}

impl<const REDUCED_ROUNDS: bool> TranscriptState<REDUCED_ROUNDS> {
    #[inline(always)]
    pub fn new(seed: Seed) -> Self {
        Self {
            hasher: DelegatedBlake2sState::new(),
            seed,
        }
    }

    #[inline(always)]
    pub fn from_hasher_and_seed(hasher: DelegatedBlake2sState, seed: Seed) -> Self {
        Self { hasher, seed }
    }

    #[inline(always)]
    pub fn commit<const N: usize>(&mut self, buf: &mut CommitBuf<N>, data_words: usize) {
        buf.commit(&mut self.hasher, &mut self.seed, data_words);
    }

    #[inline(always)]
    pub fn draw_raw(&mut self, dst: &mut [u32]) {
        Blake2sTranscript::<REDUCED_ROUNDS>::draw_randomness_using_hasher(
            &mut self.hasher,
            &mut self.seed,
            dst,
        );
    }

    #[inline(always)]
    pub fn iterator<'a>(&'a mut self) -> TranscriptStateU32Iterator<'a, REDUCED_ROUNDS> {
        TranscriptStateU32Iterator {
            state: self,
            buffer_offset: 0,
        }
    }

    #[inline(always)]
    pub fn into_seed(self) -> Seed {
        self.seed
    }
}

pub struct TranscriptStateU32Iterator<'a, const REDUCED_ROUNDS: bool> {
    state: &'a mut TranscriptState<REDUCED_ROUNDS>,
    buffer_offset: usize,
}

impl<'a, const REDUCED_ROUNDS: bool> core::iter::Iterator
    for TranscriptStateU32Iterator<'a, REDUCED_ROUNDS>
{
    type Item = u32;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.buffer_offset == BLAKE2S_DIGEST_SIZE_U32_WORDS {
                self.buffer_offset = 0;
                Blake2sTranscript::<REDUCED_ROUNDS>::draw_randomness_inner(
                    &mut self.state.hasher,
                    &mut self.state.seed,
                );
            }

            let word = *self.state.seed.0.get_unchecked(self.buffer_offset);
            self.buffer_offset += 1;

            Some(word)
        }
    }
}

/// layout `[seed | data | zero-padding]`
/// Callers write data via `data_write(i, val)` — the seed offset is handled internally.
pub struct CommitBuf<const N: usize, const REDUCED_ROUNDS: bool = true> {
    inner: AlignedArray64<core::mem::MaybeUninit<u32>, N>,
}

impl<const N: usize, const REDUCED_ROUNDS: bool> CommitBuf<N, REDUCED_ROUNDS> {
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
        {
            Blake2sTranscript::<REDUCED_ROUNDS>::commit_with_seed_using_hasher_and_aligned_buffer(
                hasher,
                seed,
                unsafe { self.inner.assume_init_ref() },
                total,
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
