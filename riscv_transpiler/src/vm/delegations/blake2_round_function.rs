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
    let x10 = state.registers[10].value;
    let x11 = state.registers[11].value;
    let x12 = state.registers[12].value;

    assert!(
        x10 >= common_constants::rom::ROM_BYTE_SIZE as u32,
        "state pointer is in ROM"
    );
    assert!(
        x11 >= common_constants::rom::ROM_BYTE_SIZE as u32,
        "input pointer is in ROM"
    );

    assert!(x10 != x11);

    assert!(x10 % 128 == 0, "state pointer is unaligned");
    assert!(x11 % 64 == 0, "input pointer is unaligned");

    let control_bitmask = (x12 >> 16) & ((1 << BLAKE2S_NUM_CONTROL_BITS) - 1);
    let mode_compression =
        control_bitmask & TEST_IF_COMPRESSION_MODE_MASK == TEST_IF_COMPRESSION_MODE_MASK;
    let reduced_rounds = control_bitmask & TEST_IF_REDUCE_ROUNDS_MASK == TEST_IF_REDUCE_ROUNDS_MASK;
    let compression_mode_node_is_right =
        control_bitmask & TEST_IF_INPUT_IS_RIGHT_NODE_MASK == TEST_IF_INPUT_IS_RIGHT_NODE_MASK;

    {
        let permutation_bitmask = x12 >> (16 + BLAKE2S_NUM_CONTROL_BITS);
        assert!(
            permutation_bitmask.is_power_of_two(),
            "permutation bitmask must be a bitmask, but got 0b{:b}",
            permutation_bitmask
        );
        let permutation_index = permutation_bitmask.trailing_zeros() as usize;
        assert_eq!(permutation_index, 0);
    }

    let final_x12 = {
        let final_permutation_bitmask = if reduced_rounds {
            (1 << 7) & ((1 << BLAKE2S_MAX_ROUNDS) - 1)
        } else {
            (1 << 10) & ((1 << BLAKE2S_MAX_ROUNDS) - 1)
        };

        let final_x12 =
            (control_bitmask | (final_permutation_bitmask << BLAKE2S_NUM_CONTROL_BITS)) << 16;

        final_x12
    };

    let num_rounds = if reduced_rounds { 7 } else { 10 };

    state.registers[10].timestamp =
        state.timestamp + ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[11].timestamp =
        state.timestamp + ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[12].timestamp =
        state.timestamp + ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP + 3;
    state.registers[12].value = final_x12;

    // NOTE: we should touch x0 and give it a timestamp that would be at the very end of execution
    state.registers[0].timestamp =
        (state.timestamp + ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP) | 2;

    unsafe {
        // read blake state, and input
        // we are fine to NOT keep track on the initial timestamps, as we only need final write ones
        let mut blake_state_full: [MaybeUninit<u32>; 24] = [const { MaybeUninit::uninit() }; 24];

        let mut addr = x10;
        for i in 0..24 {
            let value = ram.peek_word(addr);
            addr += 4;

            blake_state_full[i].write(value);
        }
        let mut blake_state_full = blake_state_full.map(|el| el.assume_init());

        // and input doesn't change across calls
        let mut input: [MaybeUninit<u32>; 16] = [const { MaybeUninit::uninit() }; 16];

        let mut addr = x11;
        for i in 0..16 {
            let value = ram.peek_word(addr);
            addr += 4;

            input[i].write(value);
        }
        let input = input.map(|el| el.assume_init());

        let (blake_state, extended_state) =
            blake_state_full.split_at_mut_unchecked(BLAKE2S_STATE_WIDTH_IN_U32_WORDS);
        let blake_state: &mut [u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS] = blake_state
            .as_mut_ptr()
            .cast::<[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS]>()
            .as_mut_unchecked();
        let mut extended_state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] =
            extended_state
                .as_mut_ptr()
                .cast::<[u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS]>()
                .as_mut_unchecked();

        // update the state if needed before rounds

        if mode_compression {
            // overwrite first 8 elements to the extended
            for i in 0..8 {
                extended_state[i] = CONFIGURED_IV[i];
                extended_state[i + 8] = IV[i];
            }
            extended_state[12] ^= BLAKE2S_BLOCK_SIZE_BYTES as u32;
            extended_state[14] ^= 0xffffffff;
        } else {
            // overwrite first 8 elements of the extended with current state
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

        for round in 0..num_rounds {
            let last_round = round == num_rounds - 1;

            if mode_compression {
                let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                if compression_mode_node_is_right {
                    buffer[..8].copy_from_slice(&input[..8]);
                    buffer[8..].copy_from_slice(blake_state);
                } else {
                    buffer[..8].copy_from_slice(blake_state);
                    buffer[8..].copy_from_slice(&input[..8]);
                }
                let sigma = &SIGMAS[round];
                mixing_function(&mut extended_state, &buffer, sigma);
            } else {
                let sigma = &SIGMAS[round];
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

        // write back

        // we write as at the last invocation
        let write_ts = state.timestamp + ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP;
        let write_ts = write_ts | 3;

        let mut addr = x10;
        for i in 0..24 {
            let value = blake_state_full[i];

            let (ts, old_value) = ram.write_word(addr, value, write_ts);
            snapshotter.append_memory_read(addr, old_value, ts, write_ts);
            addr += 4;
        }

        let mut addr = x11;
        for i in 0..16 {
            // input is unchanged
            let (ts, old_value) = ram.read_word(addr, write_ts);
            snapshotter.append_memory_read(addr, old_value, ts, write_ts);
            addr += 4;
        }

        // and x12 is already updated
    }
    // and full machine state also moves!

    // But timestamp needs 1 less bump
    state.timestamp += ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP;
    state.counters.bump_blake2_round_function(num_rounds);
    state.pc = state
        .pc
        .wrapping_add((core::mem::size_of::<u32>() * num_rounds) as u32);
    state
        .counters
        .log_multiple_circuit_family_calls::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(num_rounds);
}

// #[inline(never)]
// pub(crate) fn blake2_round_function_call<C: Counters, S: Snapshotter<C>, R: RAM>(
//     state: &mut State<C>,
//     ram: &mut R,
//     snapshotter: &mut S,
// ) {
//     let x10 = read_register::<C, 3>(state, 10);
//     let x11 = read_register::<C, 3>(state, 11);
//     let x12 = state.registers[12].value;

//     assert!(
//         x10 >= common_constants::rom::ROM_BYTE_SIZE as u32,
//         "state pointer is in ROM"
//     );
//     assert!(
//         x11 >= common_constants::rom::ROM_BYTE_SIZE as u32,
//         "input pointer is in ROM"
//     );

//     assert!(x10 != x11);

//     assert!(x10 % 128 == 0, "input pointer is unaligned");
//     assert!(x11 % 64 == 0, "input pointer is unaligned");

//     let write_ts = state.timestamp | 3;

//     let reduced_rounds = x12 & TEST_IF_REDUCE_ROUNDS_MASK == TEST_IF_REDUCE_ROUNDS_MASK;
//     let num_round = if reduced_rounds { 7 } else { 10 };

//     let mut state_accesses: [u32; BLAKE2S_X10_NUM_WRITES] = peek_read_words(x10, ram);
//     let input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] = read_words(x11, ram, snapshotter, write_ts);

//     let updated_x12 = blake2_round_function_impl(&mut state_accesses, input, x12);

//     // write back
//     write_back_words(x10, ram, snapshotter, write_ts, &state_accesses);
//     write_register::<C, 3>(state, 12, &mut (updated_x12 as u32));

//     // and full machine state also moves!

//     // But timestamp needs 1 less bump
//     state.timestamp += ((num_round - 1) as TimestampScalar) * TIMESTAMP_STEP;
//     state.counters.bump_keccak_special5(num_round);
//     state.pc = state
//         .pc
//         .wrapping_add((core::mem::size_of::<u32>() * num_round) as u32);
//     state
//         .counters
//         .log_multiple_circuit_family_calls::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(num_round);
// }

#[inline(always)]
pub(crate) fn blake2_round_function_impl(
    state_accesses: &mut [u32; BLAKE2S_X10_NUM_WRITES],
    input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    x12: u32,
) -> u32 {
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

        let control_bitmask = (x12 >> 16) & ((1 << BLAKE2S_NUM_CONTROL_BITS) - 1);
        let mode_compression =
            control_bitmask & TEST_IF_COMPRESSION_MODE_MASK == TEST_IF_COMPRESSION_MODE_MASK;
        let reduced_rounds =
            control_bitmask & TEST_IF_REDUCE_ROUNDS_MASK == TEST_IF_REDUCE_ROUNDS_MASK;
        let compression_mode_node_is_right =
            control_bitmask & TEST_IF_INPUT_IS_RIGHT_NODE_MASK == TEST_IF_INPUT_IS_RIGHT_NODE_MASK;

        let permutation_bitmask = x12 >> (16 + BLAKE2S_NUM_CONTROL_BITS);
        assert!(
            permutation_bitmask.is_power_of_two(),
            "permutation bitmask must be a bitmask, but got 0b{:b}",
            permutation_bitmask
        );
        let permutation_index = permutation_bitmask.trailing_zeros() as usize;
        let last_round = (permutation_index == 9) || (reduced_rounds && (permutation_index == 6));

        // update control register
        let shifted_permutation_bitmask =
            (permutation_bitmask << 1) & ((1 << BLAKE2S_MAX_ROUNDS) - 1);
        let updated_x12 =
            (control_bitmask | (shifted_permutation_bitmask << BLAKE2S_NUM_CONTROL_BITS)) << 16;

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
        updated_x12
    }
}
