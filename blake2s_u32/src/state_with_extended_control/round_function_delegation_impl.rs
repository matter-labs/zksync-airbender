use super::*;
use common_constants::delegation_types::blake2s_with_control::*;
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
    pub unsafe fn run_round_function_with_input_and_byte_len<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;
        {
            self.extended_state[12] = self.t ^ IV[4];
            self.extended_state[14] = (0xffffffff * last_round as u32) ^ IV[6];

            if REDUCED_ROUNDS {
                let control_register = BLAKE2S_NORMAL_MODE_REDUCED_ROUNDS_INITIAL_CONTROL_REGISTER;
                unsafe {
                    blake_csr_trigger_delegation_reduced_rounds(
                        self.state.as_mut_ptr(),
                        input_buffer.as_ptr(),
                        control_register,
                    );
                }
            } else {
                let control_register = BLAKE2S_NORMAL_MODE_FULL_ROUNDS_INITIAL_CONTROL_REGISTER;
                unsafe {
                    blake_csr_trigger_delegation_full_rounds(
                        self.state.as_mut_ptr(),
                        input_buffer.as_ptr(),
                        control_register,
                    );
                }
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
    pub unsafe fn run_round_function_with_byte_len<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;
        {
            self.extended_state[12] = self.t ^ IV[4];
            self.extended_state[14] = (0xffffffff * last_round as u32) ^ IV[6];

            if REDUCED_ROUNDS {
                let control_register = BLAKE2S_NORMAL_MODE_REDUCED_ROUNDS_INITIAL_CONTROL_REGISTER;
                unsafe {
                    blake_csr_trigger_delegation_reduced_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        control_register,
                    );
                }
            } else {
                let control_register = BLAKE2S_NORMAL_MODE_FULL_ROUNDS_INITIAL_CONTROL_REGISTER;
                unsafe {
                    blake_csr_trigger_delegation_full_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        control_register,
                    );
                }
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
    pub fn compress_node<const REDUCED_ROUNDS: bool>(&mut self, is_right: bool) {
        {
            if REDUCED_ROUNDS {
                let control_register = BLAKE2S_NORMAL_MODE_REDUCED_ROUNDS_INITIAL_CONTROL_REGISTER
                    | BLAKE2S_COMPRESSION_MODE_EXTRA_BITS
                    | (BLAKE2S_COMPRESSION_MODE_IS_RIGHT_EXTRA_BITS * (is_right as u32));
                unsafe {
                    blake_csr_trigger_delegation_reduced_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        control_register,
                    );
                }
            } else {
                let control_register = BLAKE2S_NORMAL_MODE_FULL_ROUNDS_INITIAL_CONTROL_REGISTER
                    | BLAKE2S_COMPRESSION_MODE_EXTRA_BITS
                    | (BLAKE2S_COMPRESSION_MODE_IS_RIGHT_EXTRA_BITS * (is_right as u32));
                unsafe {
                    blake_csr_trigger_delegation_full_rounds(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        control_register,
                    );
                }
            }
        }
    }

    // if "is right" then the hash contained in the state is "right node"
    #[inline(always)]
    pub fn get_merkle_path_proof_buffer(
        &mut self,
        _is_right: bool,
    ) -> &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        // we use first "half" of the internal input buffer, and delegation takes care of it
        unsafe {
            self.input_buffer
                .deref_mut_impl()
                .as_chunks_mut()
                .0
                .iter_mut()
                .next()
                .unwrap_unchecked()
        }
    }
}
