use core::mem::MaybeUninit;

// NOTE: here we need struct definition for external crates, but we will panic in implementations instead

use super::*;

// Here we try different approach to Blake round function, but placing extra burden
// into "precompile" in terms of control flow

pub const CSR_REGISTER_TO_TRIGGER: u32 = 0x7c7;

// we will pass
// - mutable ptr to state + extended state (basically - to self),
// with words 12 and 14 set in the extended state to what we need if we do not use "compression" mode
// - const ptr to input (that may be treated differently)
// - round mask
// - control register: output_flag || is_right flag for compression || compression mode flag

#[cfg(all(target_arch = "riscv32", feature = "blake2_with_compression"))]
#[inline(always)]
fn csr_trigger_delegation(
    states_ptr: *mut u32,
    input_ptr: *const u32,
    round_mask: u32,
    control_mask: u32,
) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7c7, x0",
            in("x10") states_ptr.addr(),
            in("x11") input_ptr.addr(),
            in("x12") round_mask,
            in("x13") control_mask,
            options(nostack, preserves_flags)
        )
    }
}

#[cfg(target_arch = "riscv32")]
const NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER: u32 = 0b000;
#[cfg(target_arch = "riscv32")]
const NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER: u32 = 0b001;
#[cfg(target_arch = "riscv32")]
const COMPRESSION_MODE_FIRST_ROUNDS_BASE_CONTROL_REGISTER: u32 = 0b100;
#[cfg(target_arch = "riscv32")]
const COMPRESSION_MODE_LAST_ROUND_EXTRA_BITS: u32 = 0b001;
#[cfg(target_arch = "riscv32")]
const COMPRESSION_MODE_IS_RIGHT_EXTRA_BITS: u32 = 0b010;

#[derive(Clone, Copy, Debug)]
#[repr(C, align(128))]
pub struct Blake2RoundFunctionEvaluator {
    pub state: [u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS], // represents current state
    extended_state: [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS], // represents scratch space for evaluation
    // there is no input buffer, and we will use registers to actually pass control flow flags
    // there will be special buffer for witness to write into, that
    // we will take care to initialize, even though we will use only half of it
    pub input_buffer: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    t: u32, // we limit ourselves to <4Gb inputs
}

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
    pub const fn read_state_for_output(&self) -> [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        [
            self.state[0],
            self.state[1],
            self.state[2],
            self.state[3],
            self.state[4],
            self.state[5],
            self.state[6],
            self.state[7],
        ]
    }

    #[inline(always)]
    pub const fn read_state_for_output_ref(&self) -> &[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        &self.state
    }

    #[inline(always)]
    pub const fn get_witness_buffer(&mut self) -> &mut [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] {
        &mut self.input_buffer
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
        input_buffer: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
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
        input_buffer: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;

        #[cfg(all(target_arch = "riscv32", feature = "blake2_with_compression"))]
        {
            self.extended_state[12] = self.t ^ IV[4];
            self.extended_state[14] = (0xffffffff * last_round as u32) ^ IV[6];

            if REDUCED_ROUNDS {
                for round_idx in 0..6 {
                    let round_bitmask = 1 << round_idx;
                    let _ = csr_trigger_delegation(
                        self.state.as_mut_ptr(),
                        input_buffer.as_ptr(),
                        round_bitmask,
                        NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER,
                    );
                }
                let round_bitmask = 1 << 6;
                let _ = csr_trigger_delegation(
                    self.state.as_mut_ptr(),
                    input_buffer.as_ptr(),
                    round_bitmask,
                    NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER,
                );
            } else {
                for round_idx in 0..9 {
                    let round_bitmask = 1 << round_idx;
                    let _ = csr_trigger_delegation(
                        self.state.as_mut_ptr(),
                        input_buffer.as_ptr(),
                        round_bitmask,
                        NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER,
                    );
                }
                let round_bitmask = 1 << 9;
                let _ = csr_trigger_delegation(
                    self.state.as_mut_ptr(),
                    input_buffer.as_ptr(),
                    round_bitmask,
                    NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER,
                );
            }
        }

        #[cfg(all(target_arch = "riscv32", not(feature = "blake2_with_compression")))]
        panic!("feature `blake2_with_compression` must be activated on RISC-V architecture to use this module");

        #[cfg(not(target_arch = "riscv32"))]
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
                round_function_reduced_rounds(&mut extended_state, input_buffer);
            } else {
                round_function_full_rounds(&mut extended_state, input_buffer);
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

        #[cfg(all(target_arch = "riscv32", feature = "blake2_with_compression"))]
        {
            self.extended_state[12] = self.t ^ IV[4];
            self.extended_state[14] = (0xffffffff * last_round as u32) ^ IV[6];

            if REDUCED_ROUNDS {
                for round_idx in 0..6 {
                    let round_bitmask = 1 << round_idx;
                    let _ = csr_trigger_delegation(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        round_bitmask,
                        NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER,
                    );
                }
                let round_bitmask = 1 << 6;
                let _ = csr_trigger_delegation(
                    self.state.as_mut_ptr(),
                    self.input_buffer.as_ptr(),
                    round_bitmask,
                    NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER,
                );
            } else {
                for round_idx in 0..9 {
                    let round_bitmask = 1 << round_idx;
                    let _ = csr_trigger_delegation(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        round_bitmask,
                        NORMAL_MODE_FIRST_ROUNDS_CONTROL_REGISTER,
                    );
                }
                let round_bitmask = 1 << 9;
                let _ = csr_trigger_delegation(
                    self.state.as_mut_ptr(),
                    self.input_buffer.as_ptr(),
                    round_bitmask,
                    NORMAL_MODE_LAST_ROUND_CONTROL_REGISTER,
                );
            }
        }

        #[cfg(all(target_arch = "riscv32", not(feature = "blake2_with_compression")))]
        panic!("feature `blake2_with_compression` must be activated on RISC-V architecture to use this module");

        #[cfg(not(target_arch = "riscv32"))]
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
                round_function_reduced_rounds(&mut extended_state, &self.input_buffer);
            } else {
                round_function_full_rounds(&mut extended_state, &self.input_buffer);
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
    pub fn compress_node<const REDUCED_ROUNDS: bool>(&mut self, is_right: bool) {
        #[cfg(all(target_arch = "riscv32", feature = "blake2_with_compression"))]
        {
            let mut mask = COMPRESSION_MODE_FIRST_ROUNDS_BASE_CONTROL_REGISTER
                | (COMPRESSION_MODE_IS_RIGHT_EXTRA_BITS * (is_right as u32));

            if REDUCED_ROUNDS {
                for round_idx in 0..6 {
                    let round_bitmask = 1 << round_idx;
                    let _ = csr_trigger_delegation(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        round_bitmask,
                        mask,
                    );
                }
                mask |= COMPRESSION_MODE_LAST_ROUND_EXTRA_BITS;
                let round_bitmask = 1 << 6;
                let _ = csr_trigger_delegation(
                    self.state.as_mut_ptr(),
                    self.input_buffer.as_ptr(),
                    round_bitmask,
                    mask,
                );
            } else {
                for round_idx in 0..9 {
                    let round_bitmask = 1 << round_idx;
                    let _ = csr_trigger_delegation(
                        self.state.as_mut_ptr(),
                        self.input_buffer.as_ptr(),
                        round_bitmask,
                        mask,
                    );
                }
                mask |= COMPRESSION_MODE_LAST_ROUND_EXTRA_BITS;
                let round_bitmask = 1 << 9;
                let _ = csr_trigger_delegation(
                    self.state.as_mut_ptr(),
                    self.input_buffer.as_ptr(),
                    round_bitmask,
                    mask,
                );
            }
        }

        #[cfg(all(target_arch = "riscv32", not(feature = "blake2_with_compression")))]
        panic!("feature `blake2_with_compression` must be activated on RISC-V architecture to use this module");

        #[cfg(not(target_arch = "riscv32"))]
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
                round_function_reduced_rounds(&mut extended_state, &input);
            } else {
                round_function_full_rounds(&mut extended_state, &input);
            }

            for i in 0..8 {
                self.state[i] = CONFIGURED_IV[i] ^ extended_state[i] ^ extended_state[i + 8];
            }
        }
    }
}
