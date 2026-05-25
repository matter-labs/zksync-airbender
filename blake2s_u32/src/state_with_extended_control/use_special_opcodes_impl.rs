use super::*;
use common_constants::mops::MOP_TRI_ADD;

// #[inline(always)]
// fn tri_add(a: u32, b: u32, mut c: u32) -> u32 {
//     unsafe {
//         core::arch::asm!(
//             "mop.rr.{idx} {c}, {a}, {b}",
//             a = in(reg) a,
//             b = in(reg) b,
//             c = inout(reg) c,
//             idx = const MOP_TRI_ADD,
//             options(nomem, nostack, preserves_flags)
//         );
//     }

//     c
// }

// #[inline(always)]
// fn xor_rotate<const AMT: u32>(a: u32, mut b: u32) -> u32 {
//     unsafe {
//         core::arch::asm!(
//             "mop.r.{amt} {rd}, {rs1}",
//             rs1 = in(reg) a,
//             rd = inout(reg) b,
//             amt = const AMT,
//             options(nomem, nostack, preserves_flags)
//         );
//     }

//     b
// }

// #[inline(always)]
// fn spec_g_function(
//     mut a: u32,
//     mut b: u32,
//     mut c: u32,
//     mut d: u32,
//     x: u32,
//     y: u32,
// ) -> (u32, u32, u32, u32) {
//     a = tri_add(a, b, x);
//     d = xor_rotate::<16>(a, d);
//     c = c.wrapping_add(d);
//     b = xor_rotate::<12>(c, b);
//     a = tri_add(a, b, y);
//     d = xor_rotate::<8>(a, d);
//     c = c.wrapping_add(d);
//     b = xor_rotate::<7>(c, b);

//     (a, b, c, d)
// }

#[inline(always)]
fn spec_g_function(
    mut a: u32,
    mut b: u32,
    mut c: u32,
    mut d: u32,
    x: u32,
    y: u32,
) -> (u32, u32, u32, u32) {
    unsafe {
        core::arch::asm!(
            "mop.rr.{idx} {a}, {b}, {x}",
            "mop.r.16 {d}, {a}",
            "add {c}, {c}, {d}",
            "mop.r.12 {b}, {c}",
            "mop.rr.{idx} {a}, {b}, {y}",
            "mop.r.8 {d}, {a}",
            "add {c}, {c}, {d}",
            "mop.r.7 {b}, {c}",
            a = inout(reg) a,
            b = inout(reg) b,
            c = inout(reg) c,
            d = inout(reg) d,
            x = in(reg) x,
            y = in(reg) y,
            idx = const MOP_TRI_ADD,
            options(nomem, nostack, preserves_flags)
        );
    }

    (a, b, c, d)
}

#[inline(always)]
fn first_round_spec_mixing_function(
    state: &[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS],
    t: u32,
    finalization: u32,
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    sigma: &[usize; 16],
) -> [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] {
    // mix rows and columns
    unsafe {
        let [mut s0, mut s1, mut s2, mut s3, mut s4, mut s5, mut s6, mut s7] = *state;

        let [mut s8, mut s9, mut s10, mut s11, mut s12, mut s13, mut s14, mut s15] = IV;
        s12 ^= t;
        s14 ^= finalization;

        (s0, s4, s8, s12) = spec_g_function(
            s0,
            s4,
            s8,
            s12,
            *message_block.get_unchecked(sigma[0]),
            *message_block.get_unchecked(sigma[1]),
        );
        (s1, s5, s9, s13) = spec_g_function(
            s1,
            s5,
            s9,
            s13,
            *message_block.get_unchecked(sigma[2]),
            *message_block.get_unchecked(sigma[3]),
        );
        (s2, s6, s10, s14) = spec_g_function(
            s2,
            s6,
            s10,
            s14,
            *message_block.get_unchecked(sigma[4]),
            *message_block.get_unchecked(sigma[5]),
        );
        (s3, s7, s11, s15) = spec_g_function(
            s3,
            s7,
            s11,
            s15,
            *message_block.get_unchecked(sigma[6]),
            *message_block.get_unchecked(sigma[7]),
        );

        (s0, s5, s10, s15) = spec_g_function(
            s0,
            s5,
            s10,
            s15,
            *message_block.get_unchecked(sigma[8]),
            *message_block.get_unchecked(sigma[9]),
        );
        (s1, s6, s11, s12) = spec_g_function(
            s1,
            s6,
            s11,
            s12,
            *message_block.get_unchecked(sigma[10]),
            *message_block.get_unchecked(sigma[11]),
        );
        (s2, s7, s8, s13) = spec_g_function(
            s2,
            s7,
            s8,
            s13,
            *message_block.get_unchecked(sigma[12]),
            *message_block.get_unchecked(sigma[13]),
        );
        (s3, s4, s9, s14) = spec_g_function(
            s3,
            s4,
            s9,
            s14,
            *message_block.get_unchecked(sigma[14]),
            *message_block.get_unchecked(sigma[15]),
        );

        [
            s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
        ]
    }
}

#[inline(always)]
fn spec_mixing_function(
    state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS],
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    sigma: &[usize; 16],
) {
    // mix rows and columns
    unsafe {
        let [mut s0, mut s1, mut s2, mut s3, mut s4, mut s5, mut s6, mut s7, mut s8, mut s9, mut s10, mut s11, mut s12, mut s13, mut s14, mut s15] =
            *state;

        (s0, s4, s8, s12) = spec_g_function(
            s0,
            s4,
            s8,
            s12,
            *message_block.get_unchecked(sigma[0]),
            *message_block.get_unchecked(sigma[1]),
        );
        (s1, s5, s9, s13) = spec_g_function(
            s1,
            s5,
            s9,
            s13,
            *message_block.get_unchecked(sigma[2]),
            *message_block.get_unchecked(sigma[3]),
        );
        (s2, s6, s10, s14) = spec_g_function(
            s2,
            s6,
            s10,
            s14,
            *message_block.get_unchecked(sigma[4]),
            *message_block.get_unchecked(sigma[5]),
        );
        (s3, s7, s11, s15) = spec_g_function(
            s3,
            s7,
            s11,
            s15,
            *message_block.get_unchecked(sigma[6]),
            *message_block.get_unchecked(sigma[7]),
        );

        (s0, s5, s10, s15) = spec_g_function(
            s0,
            s5,
            s10,
            s15,
            *message_block.get_unchecked(sigma[8]),
            *message_block.get_unchecked(sigma[9]),
        );
        (s1, s6, s11, s12) = spec_g_function(
            s1,
            s6,
            s11,
            s12,
            *message_block.get_unchecked(sigma[10]),
            *message_block.get_unchecked(sigma[11]),
        );
        (s2, s7, s8, s13) = spec_g_function(
            s2,
            s7,
            s8,
            s13,
            *message_block.get_unchecked(sigma[12]),
            *message_block.get_unchecked(sigma[13]),
        );
        (s3, s4, s9, s14) = spec_g_function(
            s3,
            s4,
            s9,
            s14,
            *message_block.get_unchecked(sigma[14]),
            *message_block.get_unchecked(sigma[15]),
        );

        *state = [
            s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
        ];
    }
}

#[inline(always)]
#[unroll::unroll_for_loops]
fn spec_round_function_reduced_rounds(
    state: &[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS],
    t: u32,
    finalization: u32,
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
) -> [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] {
    #[cfg(feature = "verifier_stats")]
    common_constants::stats::GKR_VERIFY_STATS.with_borrow_mut(|s| s.blake2s_hashes += 1);

    // first one we make it from state
    let mut ext_state =
        first_round_spec_mixing_function(state, t, finalization, message_block, &SIGMAS[0]);

    // reduced rounds
    for i in 1..7 {
        let sigma = &SIGMAS[i];
        spec_mixing_function(&mut ext_state, message_block, sigma);
    }

    ext_state
}

#[inline(always)]
#[unroll::unroll_for_loops]
fn spec_round_function_full_rounds(
    state: &[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS],
    t: u32,
    finalization: u32,
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
) -> [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] {
    #[cfg(feature = "verifier_stats")]
    common_constants::stats::GKR_VERIFY_STATS.with_borrow_mut(|s| s.blake2s_hashes += 1);

    // first one we make it from state
    let mut ext_state =
        first_round_spec_mixing_function(state, t, finalization, message_block, &SIGMAS[0]);

    // full rounds
    for i in 1..10 {
        let sigma = &SIGMAS[i];
        spec_mixing_function(&mut ext_state, message_block, sigma);
    }

    ext_state
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
        Self {
            state: CONFIGURED_IV,
            input_buffer: AlignedArray64::from_value(0u32),
            t: 0,
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
            let extended_state = if REDUCED_ROUNDS {
                spec_round_function_reduced_rounds(
                    &self.state,
                    self.t,
                    0xffffffff * last_round as u32,
                    input_buffer,
                )
            } else {
                spec_round_function_full_rounds(
                    &self.state,
                    self.t,
                    0xffffffff * last_round as u32,
                    input_buffer,
                )
            };

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
            let extended_state = if REDUCED_ROUNDS {
                spec_round_function_reduced_rounds(
                    &self.state,
                    self.t,
                    0xffffffff * last_round as u32,
                    &self.input_buffer,
                )
            } else {
                spec_round_function_full_rounds(
                    &self.state,
                    self.t,
                    0xffffffff * last_round as u32,
                    &self.input_buffer,
                )
            };

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
    /// and self-state as the hash input and destination. Trashes the input buffer
    #[unroll::unroll_for_loops]
    pub fn compress_node<const REDUCED_ROUNDS: bool>(&mut self, is_right: bool) {
        {
            // Caller has written path witness into get_merkle_path_proof_buffer(is_right).
            // We copy self.state into the other half.
            if is_right {
                self.input_buffer[8..16].copy_from_slice(&self.state);
            } else {
                self.input_buffer[0..8].copy_from_slice(&self.state);
            }

            let extended_state = if REDUCED_ROUNDS {
                spec_round_function_reduced_rounds(
                    &CONFIGURED_IV,
                    BLAKE2S_BLOCK_SIZE_BYTES as u32,
                    0xffffffff,
                    &self.input_buffer,
                )
            } else {
                spec_round_function_full_rounds(
                    &CONFIGURED_IV,
                    BLAKE2S_BLOCK_SIZE_BYTES as u32,
                    0xffffffff,
                    &self.input_buffer,
                )
            };

            for i in 0..8 {
                self.state[i] = CONFIGURED_IV[i] ^ extended_state[i] ^ extended_state[i + 8];
            }
        }
    }

    // if "is right" then the hash contained in the state is "right node"
    #[inline(always)]
    pub fn get_merkle_path_proof_buffer(
        &mut self,
        is_right: bool,
    ) -> &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        // we use proper "half" of the internal input buffer and only copy over the state to the "other one"
        unsafe {
            let (l, r) = self.input_buffer.split_at_mut_unchecked(8);
            let l: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] = l.as_mut_array().unwrap_unchecked();
            let r: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] = r.as_mut_array().unwrap_unchecked();
            if is_right {
                l
            } else {
                r
            }
        }
    }
}
