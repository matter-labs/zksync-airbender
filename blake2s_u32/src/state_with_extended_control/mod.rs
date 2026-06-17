// NOTE: here we need struct definition for external crates, but we will panic in implementations instead
use super::*;
use crate::aligned_array::AlignedArray64;
#[cfg(feature = "blake2_g_function")]
use crate::aligned_array::A64;

#[cfg(all(
    target_arch = "riscv32",
    all(feature = "blake2_with_compression", feature = "blake2_g_function")
))]
compile_error!("multiple features activated for blake delegation");

#[cfg(not(all(
    target_arch = "riscv32",
    any(
        feature = "blake2_with_compression",
        feature = "blake2_g_function",
        feature = "special_opcodes_extension"
    )
)))]
mod baseline_impl;

#[cfg(all(target_arch = "riscv32", feature = "blake2_with_compression"))]
mod round_function_delegation_impl;

#[cfg(all(target_arch = "riscv32", feature = "blake2_g_function"))]
mod mixing_function_delegation_impl;

#[cfg(all(target_arch = "riscv32", feature = "special_opcodes_extension"))]
mod use_special_opcodes_impl;

// we will pass
// - mutable ptr to state + extended state (basically - to self),
// with words 12 and 14 set in the extended state to what we need if we do not use "compression" mode
// - const ptr to input (that may be treated differently)
// - round mask
// - control register: output_flag || is_right flag for compression || compression mode flag

#[derive(Clone, Copy, Debug)]
#[repr(C, align(128))]
pub struct Blake2RoundFunctionEvaluator {
    pub state: [u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS], // represents current state
    #[cfg(all(target_arch = "riscv32", feature = "blake2_g_function"))]
    _aligner: A64,

    #[cfg(any(
        all(target_arch = "riscv32", feature = "blake2_with_compression"),
        all(target_arch = "riscv32", feature = "blake2_g_function")
    ))]
    pub extended_state: [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS], // represents scratch space for evaluation
    // there is no input buffer, and we will use registers to actually pass control flow flags
    // there will be special buffer for witness to write into, that
    // we will take care to initialize, even though we will use only half of it
    pub input_buffer: AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
    pub t: u32, // we limit ourselves to <4Gb inputs
}

impl Blake2RoundFunctionEvaluator {
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
        self.input_buffer.deref_mut_impl()
    }
}
