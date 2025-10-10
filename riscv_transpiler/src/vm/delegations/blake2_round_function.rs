use std::mem::MaybeUninit;

use super::*;
use blake2s_u32::state_with_extended_control_flags::*;
use blake2s_u32::*;
use common_constants::*;

#[inline(always)]
fn peek_read_words<R: RAM, const N: usize>(offset: u32, ram: &R) -> [u32; N] {
    unsafe {
        let mut result = [MaybeUninit::uninit(); N];
        let mut addr = offset;
        for dst in result.iter_mut() {
            let value = ram.peek_word(addr);
            addr += core::mem::size_of::<u32>() as u32;
            dst.write(value);
        }

        result.map(|el| el.assume_init())
    }
}

#[inline(always)]
fn read_words<C: Counters, S: Snapshotter<C>, R: RAM, const N: usize>(
    offset: u32,
    ram: &mut R,
    snapshotter: &mut S,
    timestamp: TimestampScalar,
) -> [u32; N] {
    unsafe {
        let mut result = [MaybeUninit::uninit(); N];
        let mut addr = offset;
        for dst in result.iter_mut() {
            let (read_ts, value) = ram.read_word(addr, timestamp);
            snapshotter.append_memory_read(addr, value, read_ts, timestamp);
            addr += core::mem::size_of::<u32>() as u32;
            dst.write(value);
        }

        result.map(|el| el.assume_init())
    }
}

#[inline(always)]
fn write_back_words<C: Counters, S: Snapshotter<C>, R: RAM, const N: usize>(
    offset: u32,
    ram: &mut R,
    snapshotter: &mut S,
    timestamp: TimestampScalar,
    value: &[u32; N],
) {
    let mut addr = offset;
    for src in value.iter() {
        let new_value = *src as u32;
        let (read_ts, low) = ram.write_word(addr, new_value, timestamp);
        snapshotter.append_memory_read(addr, low, read_ts, timestamp);
        addr += core::mem::size_of::<u32>() as u32;
    }
}

#[inline(never)]
pub(crate) fn blake2_round_function_call<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
) {
    let x10 = read_register::<C, 3>(state, 10);
    let x11 = read_register::<C, 3>(state, 11);
    let x12 = read_register::<C, 3>(state, 12);
    let x13 = read_register::<C, 3>(state, 13);

    assert!(x10 >= 1 << 21);
    assert!(x11 >= 1 << 21);

    assert!(x10 != x11);

    assert!(x10 % 128 == 0, "input pointer is unaligned");
    assert!(x11 % 4 == 0, "input pointer is unaligned");

    let write_ts = state.timestamp | 3;

    let mut state_accesses: [u32; BLAKE2S_X10_NUM_WRITES] = peek_read_words(x10, ram);
    let input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] = read_words(x11, ram, snapshotter, write_ts);

    blake2_round_function_impl(&mut state_accesses, input, x12, x13);

    // write back
    write_back_words(x10, ram, snapshotter, write_ts, &state_accesses);

    state.counters.bump_blake2_round_function();
}

#[inline(always)]
pub(crate) fn blake2_round_function_impl(
    state_accesses: &mut [u32; BLAKE2S_X10_NUM_WRITES],
    input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    x12: u32,
    x13: u32,
) {
    unsafe {
        let (blake_state, extended_state) =
            state_accesses.split_at_mut_unchecked(BLAKE2S_STATE_WIDTH_IN_U32_WORDS);
        let blake_state: &mut [u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS] = blake_state
            .as_mut_ptr()
            .cast::<[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS]>()
            .as_mut_unchecked();
        let mut extended_state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] =
            extended_state
                .as_mut_ptr()
                .cast::<[u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS]>()
                .as_mut_unchecked();

        let control_register = x13;
        let mode_compression =
            control_register & TEST_IF_COMPRESSION_MODE_MASK == TEST_IF_COMPRESSION_MODE_MASK;
        let last_round = control_register & TEST_IF_LAST_ROUND_MASK == TEST_IF_LAST_ROUND_MASK;
        let compression_mode_node_is_right =
            control_register & TEST_IF_INPUT_IS_RIGHT_NODE_MASK == TEST_IF_INPUT_IS_RIGHT_NODE_MASK;

        let permutation_bitmask = x12;
        assert!(
            permutation_bitmask.is_power_of_two(),
            "permutation bitmask must be a bitmask, but got 0b{:b}",
            permutation_bitmask
        );
        let permutation_index = permutation_bitmask.trailing_zeros() as usize;

        if mode_compression {
            if permutation_index == 0 {
                // overwrite first 8 elements to the extended
                for i in 0..8 {
                    extended_state[i] = CONFIGURED_IV[i];
                    extended_state[i + 8] = IV[i];
                }
                extended_state[12] ^= BLAKE2S_BLOCK_SIZE_BYTES as u32;
                extended_state[14] ^= 0xffffffff;
            }
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            if compression_mode_node_is_right {
                buffer[..8].copy_from_slice(&input[..8]);
                buffer[8..].copy_from_slice(blake_state);
            } else {
                buffer[..8].copy_from_slice(blake_state);
                buffer[8..].copy_from_slice(&input[..8]);
            }
            let sigma = &SIGMAS[permutation_index];
            mixing_function(&mut extended_state, &buffer, sigma);
        } else {
            if permutation_index == 0 {
                // overwrite first 8 elements to the state
                for i in 0..8 {
                    extended_state[i] = blake_state[i];
                }
                // overwrite elements 8-11, 13, 15
                extended_state[8] = IV[0];
                extended_state[9] = IV[1];
                extended_state[10] = IV[2];
                extended_state[11] = IV[3];
                extended_state[13] = IV[5];
                extended_state[15] = IV[7];
            }
            let sigma = &SIGMAS[permutation_index];
            mixing_function(&mut extended_state, &input, sigma);
        }

        // update output the state if needed
        if last_round {
            if mode_compression {
                // we always start from "empty state" for XORing below
                *blake_state = CONFIGURED_IV;
            }
            for i in 0..8 {
                blake_state[i] ^= extended_state[i] ^ extended_state[i + 8];
            }
        }
    }
}
