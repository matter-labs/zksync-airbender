use std::mem::MaybeUninit;

use super::*;
use blake2s_u32::state_with_extended_control_flags::*;
use blake2s_u32::*;
use common_constants::*;

pub(crate) fn blake_implementation(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    // Implementer here is responsible for ALL the bookkeeping, and eventually MUST update trace piece chunk via context, and and update machine state to reflect filled part of trace chunk
    assert!((trace_piece.len as usize) < TRACE_CHUNK_LEN);
    debug_assert_eq!(machine_state.timestamp % 4, 3);
    let state_ptr = machine_state.registers[10];
    let input_ptr = machine_state.registers[11];
    let x12 = machine_state.registers[12];
    assert!(state_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert!(input_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert_eq!(state_ptr % 128, 0, "`state` pointer is unaligned");
    assert_eq!(input_ptr % 64, 0, "`input` pointer is unaligned");

    assert!(state_ptr != input_ptr);

    // read and save into snapshots

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

    machine_state.timestamp += ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP; // 3 mod 4

    let write_ts = machine_state.timestamp;

    machine_state.register_timestamps[10] = write_ts;
    machine_state.register_timestamps[11] = write_ts;
    machine_state.register_timestamps[12] = write_ts;
    machine_state.registers[12] = final_x12;

    // touch x0
    machine_state.register_timestamps[0] = write_ts - 1;

    unsafe {
        // read blake state, and input

        let state_words_offset = (state_ptr as usize) / core::mem::size_of::<u32>();

        let blake_state_full = memory_holder
            .memory
            .as_mut_ptr()
            .add(state_words_offset)
            .cast::<[u32; 24]>()
            .as_mut_unchecked();
        let state_timestamps = memory_holder
            .timestamps
            .as_mut_ptr()
            .add(state_words_offset)
            .cast::<[TimestampScalar; 24]>()
            .as_mut_unchecked();

        // TODO: unroll ?
        for i in 0..24 {
            trace_piece.add_element(blake_state_full[i], state_timestamps[i]);
            state_timestamps[i] = write_ts;
        }

        let input_words_offset = (input_ptr as usize) / core::mem::size_of::<u32>();

        let input = memory_holder
            .memory
            .as_ptr()
            .add(input_words_offset)
            .cast::<[u32; 16]>()
            .as_ref_unchecked();
        let input_timestamps = memory_holder
            .timestamps
            .as_mut_ptr()
            .add(input_words_offset)
            .cast::<[TimestampScalar; 16]>()
            .as_mut_unchecked();

        // TODO: unroll ?
        for i in 0..16 {
            trace_piece.add_element(input[i], input_timestamps[i]);
            input_timestamps[i] = write_ts;
        }

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

        let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];

        for round in 0..num_rounds {
            let last_round = round == num_rounds - 1;
            if mode_compression {
                if compression_mode_node_is_right {
                    buffer[..8].copy_from_slice(&input[..8]);
                    buffer[8..].copy_from_slice(&*blake_state);
                } else {
                    buffer[..8].copy_from_slice(&*blake_state);
                    buffer[8..].copy_from_slice(&input[..8]);
                }
                let sigma = &SIGMAS[round];
                mixing_function(extended_state, &buffer, sigma);
            } else {
                let sigma = &SIGMAS[round];
                mixing_function(extended_state, &input, sigma);
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

        // we did all the manipulations "in place", and updated timestamps.
        // x12 is already updated
    }

    assert!((trace_piece.len as usize) < MAX_TRACE_CHUNK_LEN);
    let should_flush = ((trace_piece.len as usize) >= TRACE_CHUNK_LEN) as u64;

    // println!("Blake, should flush = {}", should_flush);

    should_flush
}
