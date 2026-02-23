#![cfg_attr(not(feature = "pow"), no_std)]

use blake2s_u32::*;

// const USE_REDUCED_BLAKE2_ROUNDS: bool = false;
const USE_REDUCED_BLAKE2_ROUNDS: bool = true;

pub use blake2s_u32;

#[cfg(feature = "pow")]
pub mod pow;

// Our transcript for verifier efficiency is effectively stateless and has 3 functions:
// - commit initial -> seed
// - commit using some seed -> new seed
// - use seed -> (randomness, new_see)

#[derive(Clone, Copy, Debug, Default)]
pub struct Blake2sTranscript;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Seed(pub [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]);

impl Blake2sTranscript {
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
                hasher.run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(
                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                    false,
                );

                buffer_offset = 0;
            }
        }
        *offset = buffer_offset;
    }

    #[inline(always)]
    unsafe fn flush(hasher: &mut blake2s_u32::DelegatedBlake2sState, offset: usize) {
        hasher.run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(offset, true);
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
                hasher.spec_run_single_round_into_destination::<USE_REDUCED_BLAKE2_ROUNDS>(
                    BLAKE2S_DIGEST_SIZE_U32_WORDS,
                    &mut seed.0 as *mut _,
                );
            }
        } else {
            // we take the seed + sequence id, and produce hash
            hasher.run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(
                BLAKE2S_DIGEST_SIZE_U32_WORDS,
                true,
            );

            seed.0 = hasher.read_state_for_output();
        }
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

            hasher.run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(
                BLAKE2S_DIGEST_SIZE_U32_WORDS + 2,
                true,
            );
        }

        // check that first element is small enough
        assert!(
            hasher.state[0] <= (0xffffffff >> pow_bits),
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
pub struct Blake2sBufferingTranscript {
    state: DelegatedBlake2sState,
    buffer_offset: usize,
}

impl Blake2sBufferingTranscript {
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
            .run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(BLAKE2S_BLOCK_SIZE_U32_WORDS, false);

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
                .run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(self.buffer_offset, true);
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
                .run_round_function::<USE_REDUCED_BLAKE2_ROUNDS>(self.buffer_offset, true);
        }

        let seed = Seed(self.state.read_state_for_output());

        self.state.reset();
        self.buffer_offset = 0;

        seed
    }
}
