// mixes 4 values + 2 round constants. Always inlined to allow to unroll round into operation in registers only

use crate::asm_utils::rotate_right;
use crate::*;

#[inline(always)]
pub fn g_function(
    v: &mut [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: u32,
    y: u32,
) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = rotate_right::<16>(v[d] ^ v[a]);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = rotate_right::<12>(v[b] ^ v[c]);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = rotate_right::<8>(v[d] ^ v[a]);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = rotate_right::<7>(v[b] ^ v[c]);
}

#[inline(always)]
pub fn g_function_raw(a: &mut u32, b: &mut u32, c: &mut u32, d: &mut u32, x: u32, y: u32) {
    *a = (*a).wrapping_add(*b).wrapping_add(x);
    *d = rotate_right::<16>((*d) ^ (*a));
    *c = (*c).wrapping_add(*d);
    *b = rotate_right::<12>((*b) ^ (*c));
    *a = (*a).wrapping_add(*b).wrapping_add(y);
    *d = rotate_right::<8>((*d) ^ (*a));
    *c = (*c).wrapping_add(*d);
    *b = rotate_right::<7>((*b) ^ (*c));
}

#[inline(always)]
pub fn mixing_function(
    state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS],
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    sigma: &[usize; 16],
) {
    // mix rows and columns
    unsafe {
        g_function(
            state,
            0,
            4,
            8,
            12,
            *message_block.get_unchecked(sigma[0]),
            *message_block.get_unchecked(sigma[1]),
        );
        g_function(
            state,
            1,
            5,
            9,
            13,
            *message_block.get_unchecked(sigma[2]),
            *message_block.get_unchecked(sigma[3]),
        );
        g_function(
            state,
            2,
            6,
            10,
            14,
            *message_block.get_unchecked(sigma[4]),
            *message_block.get_unchecked(sigma[5]),
        );
        g_function(
            state,
            3,
            7,
            11,
            15,
            *message_block.get_unchecked(sigma[6]),
            *message_block.get_unchecked(sigma[7]),
        );

        g_function(
            state,
            0,
            5,
            10,
            15,
            *message_block.get_unchecked(sigma[8]),
            *message_block.get_unchecked(sigma[9]),
        );
        g_function(
            state,
            1,
            6,
            11,
            12,
            *message_block.get_unchecked(sigma[10]),
            *message_block.get_unchecked(sigma[11]),
        );
        g_function(
            state,
            2,
            7,
            8,
            13,
            *message_block.get_unchecked(sigma[12]),
            *message_block.get_unchecked(sigma[13]),
        );
        g_function(
            state,
            3,
            4,
            9,
            14,
            *message_block.get_unchecked(sigma[14]),
            *message_block.get_unchecked(sigma[15]),
        );
    }
}

#[inline(always)]
#[unroll::unroll_for_loops]
pub fn round_function_reduced_rounds(
    state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS],
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
) {
    #[cfg(feature = "verifier_stats")]
        {
            common_constants::stats::GKR_VERIFY_STATS.borrow_mut().blake2s_hashes += 1;
        }

    // reduced rounds
    for i in 0..7 {
        let sigma = &SIGMAS[i];
        mixing_function(state, message_block, sigma);
    }
}

#[inline(always)]
#[unroll::unroll_for_loops]
pub fn round_function_full_rounds(
    state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS],
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
) {
    #[cfg(feature = "verifier_stats")]
        {
            common_constants::stats::GKR_VERIFY_STATS.borrow_mut().blake2s_hashes += 1;
        }

    // full rounds
    for i in 0..10 {
        let sigma = &SIGMAS[i];
        mixing_function(state, message_block, sigma);
    }
}
