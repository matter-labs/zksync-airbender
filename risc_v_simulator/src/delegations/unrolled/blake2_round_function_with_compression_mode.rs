use crate::cycle::state_new::RiscV32StateForUnrolledProver;
use crate::cycle::{state::NON_DETERMINISM_CSR, status_registers::TrapReason};
use blake2s_u32::state_with_extended_control_flags::*;
use blake2s_u32::{
    mixing_function, BLAKE2S_BLOCK_SIZE_BYTES, BLAKE2S_BLOCK_SIZE_U32_WORDS,
    BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS, BLAKE2S_STATE_WIDTH_IN_U32_WORDS, CONFIGURED_IV, IV,
    SIGMAS,
};
use cs::definitions::{TimestampData, TimestampScalar};

use super::*;

pub const BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID: u32 = NON_DETERMINISM_CSR + 7;

pub const X10_NUM_WRITES: usize = 8 + 16;
pub const X11_NUM_READS: usize = 16;

const TOTAL_RAM_ACCESSES: usize = X10_NUM_WRITES + X11_NUM_READS;
const BASE_ABI_REGISTER: u32 = 10;

pub fn blake2_round_function_with_extended_control_over_unrolled_state<
    M: MemorySource,
    TR: Tracer<C>,
    C: MachineConfig,
>(
    machine_state: &mut RiscV32StateForUnrolledProver<C>,
    memory_source: &mut M,
    tracer: &mut TR,
) {
    // read registers first
    let x10 = machine_state.registers[10];
    let x11 = machine_state.registers[11];
    let x12 = machine_state.registers[12];
    let x13 = machine_state.registers[13];

    assert!(x10 % 128 == 0, "input pointer is unaligned");
    assert!(x11 % 4 == 0, "input pointer is unaligned");

    // self-check so that we do not touch ROM
    assert!(x10 >= 1 << 21);
    assert!(x11 >= 1 << 21);

    assert!(x10 != x11);

    let mut state_accesses: [RegisterOrIndirectReadWriteData; X10_NUM_WRITES] =
        register_indirect_read_write_continuous_noexcept::<_, X10_NUM_WRITES>(
            x10 as usize,
            memory_source,
        );
    let state_read_addresses: [u32; X10_NUM_WRITES] =
        std::array::from_fn(|i| x10 + (core::mem::size_of::<u32>() * i) as u32);
    let mut input_accesses: [RegisterOrIndirectReadData; X11_NUM_READS] =
        register_indirect_read_continuous_noexcept::<_, X11_NUM_READS>(x11 as usize, memory_source);
    let input_read_addresses: [u32; X11_NUM_READS] =
        std::array::from_fn(|i| x11 + (core::mem::size_of::<u32>() * i) as u32);

    let mut state: [u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS] = state_accesses
        .array_chunks::<BLAKE2S_STATE_WIDTH_IN_U32_WORDS>()
        .next()
        .unwrap()
        .map(|el| el.read_value);
    let mut extended_state: [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] = state_accesses
        [BLAKE2S_STATE_WIDTH_IN_U32_WORDS..]
        .array_chunks::<BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS>()
        .next()
        .unwrap()
        .map(|el| el.read_value);
    let input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] = input_accesses
        .array_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>()
        .next()
        .unwrap()
        .map(|el| el.read_value);

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
            buffer[8..].copy_from_slice(&state);
        } else {
            buffer[..8].copy_from_slice(&state);
            buffer[8..].copy_from_slice(&input[..8]);
        }
        let sigma = &SIGMAS[permutation_index];
        mixing_function(&mut extended_state, &buffer, sigma);
    } else {
        if permutation_index == 0 {
            // overwrite first 8 elements to the state
            for i in 0..8 {
                extended_state[i] = state[i];
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
            state = CONFIGURED_IV;
        }
        for i in 0..8 {
            state[i] ^= extended_state[i] ^ extended_state[i + 8];
        }
    }

    // write back into our bookkeeping
    for (src, dst) in state
        .into_iter()
        .zip(state_accesses[..BLAKE2S_STATE_WIDTH_IN_U32_WORDS].iter_mut())
    {
        dst.write_value = src;
    }

    for (src, dst) in extended_state.into_iter().zip(
        state_accesses[BLAKE2S_STATE_WIDTH_IN_U32_WORDS..]
            [..BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS]
            .iter_mut(),
    ) {
        dst.write_value = src;
    }

    // write down to RAM
    write_indirect_accesses_noexcept::<_, X10_NUM_WRITES>(
        x10 as usize,
        &state_accesses,
        memory_source,
    );

    // make witness structures - there are no register writes
    let mut register_accesses = [
        RegisterOrIndirectReadWriteData {
            read_value: x10,
            write_value: x10,
            timestamp: TimestampData::EMPTY,
        },
        RegisterOrIndirectReadWriteData {
            read_value: x11,
            write_value: x11,
            timestamp: TimestampData::EMPTY,
        },
        RegisterOrIndirectReadWriteData {
            read_value: x12,
            write_value: x12,
            timestamp: TimestampData::EMPTY,
        },
        RegisterOrIndirectReadWriteData {
            read_value: x13,
            write_value: x13,
            timestamp: TimestampData::EMPTY,
        },
    ];

    tracer.record_delegation(
        BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
        10,
        &mut register_accesses,
        &input_read_addresses,
        &mut input_accesses,
        &state_read_addresses,
        &mut state_accesses,
    );
}
