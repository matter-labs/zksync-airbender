use super::*;
use common_constants::delegation_types::blake2s_g_function::*;
use core::mem::MaybeUninit;

impl Blake2RoundFunctionEvaluator {
    pub const SUPPORT_SPEC_SINGLE_ROUND: bool = false;

    #[unroll::unroll_for_loops]
    #[inline(always)]
    pub unsafe fn spec_run_single_round_into_destination<const REDUCED_ROUNDS: bool>(
        &mut self,
        _block_len: usize,
        _dst: *mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    ) {
        unreachable!("unsupported")
    }

    /// NOTE: caller must explicitly "reset" before using if use mode is not compression
    #[allow(invalid_value)]
    pub fn new() -> Self {
        unsafe {
            // NOTE: it would only be used in RISC-V simulated machine with zero-by-default state,
            // where all memory is initialized and physical, so "touching" memory slots is not required
            let mut new: Self = MaybeUninit::uninit().assume_init();
            new.t = 0;

            // we will copy-over the initial state to avoid complications
            new.reset();

            new
        }
    }

    #[inline(always)]
    pub fn reset(&mut self) {
        unsafe {
            crate::spec_memcopy_u32_nonoverlapping(
                CONFIGURED_IV.as_ptr().cast::<u32>(),
                self.state.as_mut_ptr().cast::<u32>(),
                8,
            );
        }

        self.t = 0;
    }

    /// caller must fill the buffer (do not forget to zero-pad),
    /// and then specify the parameters of the input block
    #[inline(always)]
    pub unsafe fn run_round_function_with_input<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_words: usize,
        last_round: bool,
    ) {
        self.run_round_function_with_input_and_byte_len::<REDUCED_ROUNDS>(
            input_buffer,
            input_size_words * core::mem::size_of::<u32>(),
            last_round,
        );
    }

    #[inline]
    #[unroll::unroll_for_loops]
    pub unsafe fn run_round_function_with_input_and_byte_len<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;
        {
            let mut extended_state = [
                self.state[0],
                self.state[1],
                self.state[2],
                self.state[3],
                self.state[4],
                self.state[5],
                self.state[6],
                self.state[7],
                IV[0],
                IV[1],
                IV[2],
                IV[3],
                self.t ^ IV[4],
                IV[5],
                (0xffffffff * last_round as u32) ^ IV[6],
                IV[7],
            ];

            if REDUCED_ROUNDS {
                unsafe {
                    blake_g_function_csr_trigger_delegation_reduced_rounds(
                        self.state.as_mut_ptr(),
                        input_buffer.as_ptr(),
                    );
                }
            } else {
                unsafe {
                    blake_g_function_csr_trigger_delegation_full_rounds(
                        self.state.as_mut_ptr(),
                        input_buffer.as_ptr(),
                    );
                }
            }

            for i in 0..8 {
                self.state[i] ^= extended_state[i];
                self.state[i] ^= extended_state[i + 8];
            }
        }
    }

    #[inline(always)]
    pub unsafe fn run_round_function<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_size_words: usize,
        last_round: bool,
    ) {
        self.run_round_function_with_byte_len::<REDUCED_ROUNDS>(
            input_size_words * core::mem::size_of::<u32>(),
            last_round,
        );
    }

    #[inline]
    #[unroll::unroll_for_loops]
    pub unsafe fn run_round_function_with_byte_len<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;

        {
            let mut extended_state = [
                self.state[0],
                self.state[1],
                self.state[2],
                self.state[3],
                self.state[4],
                self.state[5],
                self.state[6],
                self.state[7],
                IV[0],
                IV[1],
                IV[2],
                IV[3],
                self.t ^ IV[4],
                IV[5],
                (0xffffffff * last_round as u32) ^ IV[6],
                IV[7],
            ];

            if REDUCED_ROUNDS {
                unsafe {
                    blake_g_function_csr_trigger_delegation_reduced_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                    );
                }
            } else {
                unsafe {
                    blake_g_function_csr_trigger_delegation_full_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                    );
                }
            }

            for i in 0..8 {
                self.state[i] ^= extended_state[i];
                self.state[i] ^= extended_state[i + 8];
            }
        }
    }

    #[inline(always)]
    pub fn compress_two_to_one<const REDUCED_ROUNDS: bool>(
        _message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        _dst: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    ) {
        panic!("Must not be used in conjunction with prover, please check the features across your build chain");
    }

    /// This function will use witness scratch of self as path witness input,
    /// and self-state as the hash input and destination
    #[unroll::unroll_for_loops]
    pub fn compress_node<const REDUCED_ROUNDS: bool>(&mut self, is_right: bool) {
        {
            let mut extended_state = [
                CONFIGURED_IV[0],
                CONFIGURED_IV[1],
                CONFIGURED_IV[2],
                CONFIGURED_IV[3],
                CONFIGURED_IV[4],
                CONFIGURED_IV[5],
                CONFIGURED_IV[6],
                CONFIGURED_IV[7],
                IV[0],
                IV[1],
                IV[2],
                IV[3],
                (BLAKE2S_BLOCK_SIZE_BYTES as u32) ^ IV[4],
                IV[5],
                0xffffffff ^ IV[6],
                IV[7],
            ];

            let mut input = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            if is_right {
                input[..8].copy_from_slice(&self.input_buffer[..8]);
                input[8..16].copy_from_slice(&self.state);
            } else {
                input[..8].copy_from_slice(&self.state);
                input[8..16].copy_from_slice(&self.input_buffer[..8]);
            }

            if REDUCED_ROUNDS {
                unsafe {
                    blake_g_function_csr_trigger_delegation_reduced_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                    );
                }
            } else {
                unsafe {
                    blake_g_function_csr_trigger_delegation_full_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                    );
                }
            }

            for i in 0..8 {
                self.state[i] = CONFIGURED_IV[i] ^ extended_state[i] ^ extended_state[i + 8];
            }
        }
    }
}
