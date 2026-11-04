use std::mem::MaybeUninit;

use super::*;
use crate::vm::delegations::blake2_round_function::blake2_round_function_impl;
use crate::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use blake2s_u32::state_with_extended_control_flags::*;
use blake2s_u32::*;
use common_constants::*;

// NOTE: in forward execution we read through x11 and dump witness, and then dump writes via x10,
// so in the function below we will just read via x11 and x10

#[inline(always)]
fn read_words<R: RAM, const N: usize>(
    offset: u32,
    ram: &mut R,
    timestamp: TimestampScalar,
    witness: &mut [RegisterOrIndirectReadData; N],
) -> [u32; N] {
    unsafe {
        let mut result = [MaybeUninit::uninit(); N];
        let mut addr = offset;
        for (dst, wit) in result.iter_mut().zip(witness.iter_mut()) {
            let (read_ts, value) = ram.read_word(addr, timestamp);
            wit.read_value = value;
            wit.timestamp = TimestampData::from_scalar(read_ts);
            addr += core::mem::size_of::<u32>() as u32;
            dst.write(value);
        }

        result.map(|el| el.assume_init())
    }
}

#[inline(always)]
fn read_words_for_update<R: RAM, const N: usize>(
    offset: u32,
    ram: &mut R,
    timestamp: TimestampScalar,
    witness: &mut [RegisterOrIndirectReadWriteData; N],
) -> [u32; N] {
    unsafe {
        let mut result = [MaybeUninit::uninit(); N];
        let mut addr = offset;
        for (dst, wit) in result.iter_mut().zip(witness.iter_mut()) {
            let (read_ts, value) = ram.read_word(addr, timestamp);
            wit.read_value = value;
            wit.timestamp = TimestampData::from_scalar(read_ts);
            addr += core::mem::size_of::<u32>() as u32;
            dst.write(value);
        }

        result.map(|el| el.assume_init())
    }
}

#[inline(never)]
pub(crate) fn blake2_round_function_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    let needs_cycle_data =
        tracer.needs_tracing_data_for_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>();
    let needs_delegation_data = tracer.needs_tracing_data_for_delegation_type::<{common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16}>();

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

    assert!(x10 % 128 == 0, "input pointer is unaligned");
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

    if needs_cycle_data == false && needs_delegation_data == false {
        ram.skip_if_replaying(24 + 16);

        state.timestamp += ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP;
        state.pc = state
            .pc
            .wrapping_add((core::mem::size_of::<u32>() * num_rounds) as u32);

        state.registers[0].timestamp = state.timestamp | 2;

        state.registers[10].timestamp = state.timestamp | 3;
        state.registers[11].timestamp = state.timestamp | 3;
        state.registers[12].timestamp = state.timestamp | 3;

        state.registers[12].value = final_x12;

        return;
    }

    let timestamp_on_entry = state.timestamp;

    if needs_cycle_data {
        // touch x0 many times and formally record
        for call_round in 0..num_rounds {
            let last_round = call_round == num_rounds - 1;
            {
                // cycle
                let next_pc = state.pc.wrapping_add(4);
                // touch x0
                let x0_timestamp = state.registers[0].timestamp;
                state.registers[0].timestamp = state.timestamp | 2;
                let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
                    opcode_data: NonMemoryOpcodeTracingData {
                        initial_pc: state.pc,
                        rs1_value: 0,
                        rs2_value: 0,
                        rd_old_value: 0,
                        rd_value: 0,
                        new_pc: next_pc,
                        delegation_type: BLAKE2S_DELEGATION_CSR_REGISTER as u16,
                    },
                    rs1_read_timestamp: TimestampData::from_scalar(x0_timestamp),
                    rs2_read_timestamp: TimestampData::from_scalar(state.timestamp),
                    rd_read_timestamp: TimestampData::from_scalar(state.timestamp | 1),
                    cycle_timestamp: TimestampData::from_scalar(state.timestamp),
                };
                tracer.write_non_memory_family_data::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(
                    traced_data,
                );
                state.pc = next_pc;
            }

            if last_round == false {
                state.timestamp += TIMESTAMP_STEP;
            }
        }
    } else {
        // touch x0

        state.timestamp += ((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP;
        state.pc = state
            .pc
            .wrapping_add((core::mem::size_of::<u32>() * num_rounds) as u32);

        state.registers[0].timestamp = state.timestamp | 2;
    }

    if needs_delegation_data {
        let mut current_timestamp = timestamp_on_entry;
        let upper_bound_read_timestamp =
            timestamp_on_entry + (((num_rounds - 1) as TimestampScalar) * TIMESTAMP_STEP) + 3;
        let artificial_read_timestamp = upper_bound_read_timestamp + 1;

        unsafe {
            let mut blake_state_full: [MaybeUninit<u32>; 24] =
                [const { MaybeUninit::uninit() }; 24];
            let mut blake_state_initial_timestamps: [MaybeUninit<TimestampScalar>; 24] =
                [const { MaybeUninit::uninit() }; 24];

            let mut addr = x10;
            for i in 0..24 {
                let (ts, value) = ram.read_word(addr, artificial_read_timestamp);
                addr += 4;

                blake_state_full[i].write(value);
                blake_state_initial_timestamps[i].write(ts);
            }
            let mut blake_state_full = blake_state_full.map(|el| el.assume_init());
            let blake_state_initial_timestamps =
                blake_state_initial_timestamps.map(|el| el.assume_init());

            // and input doesn't change across calls
            let mut input: [MaybeUninit<u32>; 16] = [const { MaybeUninit::uninit() }; 16];
            let mut input_initial_timestamps: [MaybeUninit<TimestampScalar>; 16] =
                [const { MaybeUninit::uninit() }; 16];

            let mut addr = x11;
            for i in 0..16 {
                let (ts, value) = ram.read_word(addr, artificial_read_timestamp);
                addr += 4;

                input[i].write(value);
                input_initial_timestamps[i].write(ts);
            }
            let input = input.map(|el| el.assume_init());
            let input_initial_timestamps = input_initial_timestamps.map(|el| el.assume_init());

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

            let mut control_flow_reg = x12;
            let mut x10_timestamp = state.registers[10].timestamp;
            let mut x11_timestamp = state.registers[11].timestamp;
            let mut x12_timestamp = state.registers[12].timestamp;

            let mut previous_round_write_ts = 0;

            for call_round in 0..num_rounds {
                let last_round = call_round == num_rounds - 1;

                let updated_control_flow = {
                    let permutation_bitmask = control_flow_reg >> (16 + BLAKE2S_NUM_CONTROL_BITS);
                    // update control register
                    let shifted_permutation_bitmask =
                        (permutation_bitmask << 1) & ((1 << BLAKE2S_MAX_ROUNDS) - 1);

                    let updated_x12 = (control_bitmask
                        | (shifted_permutation_bitmask << BLAKE2S_NUM_CONTROL_BITS))
                        << 16;

                    updated_x12
                };

                let mut witness = Blake2sRoundFunctionDelegationWitness::empty();
                witness.write_timestamp = current_timestamp | 3;

                witness.reg_accesses[0] = RegisterOrIndirectReadWriteData {
                    read_value: x10,
                    write_value: x10,
                    timestamp: TimestampData::from_scalar(x10_timestamp),
                };
                witness.reg_accesses[1] = RegisterOrIndirectReadWriteData {
                    read_value: x11,
                    write_value: x11,
                    timestamp: TimestampData::from_scalar(x11_timestamp),
                };
                witness.reg_accesses[2] = RegisterOrIndirectReadWriteData {
                    read_value: control_flow_reg,
                    write_value: updated_control_flow,
                    timestamp: TimestampData::from_scalar(x12_timestamp),
                };

                x10_timestamp = current_timestamp | 3;
                x11_timestamp = current_timestamp | 3;
                x12_timestamp = current_timestamp | 3;

                // fill read part
                for i in 0..24 {
                    witness.indirect_writes[i].read_value = blake_state_full[i];
                    if call_round == 0 {
                        witness.indirect_writes[i].timestamp =
                            TimestampData::from_scalar(blake_state_initial_timestamps[i]);
                    } else {
                        // use timestamp of the previous round
                        witness.indirect_writes[i].timestamp =
                            TimestampData::from_scalar(previous_round_write_ts);
                    }
                }

                for i in 0..16 {
                    witness.indirect_reads[i].read_value = input[i];
                    if call_round == 0 {
                        witness.indirect_reads[i].timestamp =
                            TimestampData::from_scalar(input_initial_timestamps[i]);
                    } else {
                        // use timestamp of the previous round
                        witness.indirect_reads[i].timestamp =
                            TimestampData::from_scalar(previous_round_write_ts);
                    }
                }

                // now in the first round we do some extra selects
                if call_round == 0 {
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
                }

                // actual blake round
                if mode_compression {
                    let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                    if compression_mode_node_is_right {
                        buffer[..8].copy_from_slice(&input[..8]);
                        buffer[8..].copy_from_slice(blake_state);
                    } else {
                        buffer[..8].copy_from_slice(blake_state);
                        buffer[8..].copy_from_slice(&input[..8]);
                    }
                    let sigma = &SIGMAS[call_round];
                    mixing_function(&mut extended_state, &buffer, sigma);
                } else {
                    let sigma = &SIGMAS[call_round];
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

                // write values for state only
                for i in 0..24 {
                    witness.indirect_writes[i].write_value = blake_state_full[i];
                }

                tracer.write_delegation::<{
                    common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16
                }, _, _, _, _>(witness);

                previous_round_write_ts = current_timestamp | 3;
                control_flow_reg = updated_control_flow;
                current_timestamp += TIMESTAMP_STEP;
            }
        }
        assert_eq!(current_timestamp - TIMESTAMP_STEP, state.timestamp);

        // update registers and control flow - can use state.timestamp
        state.registers[10].timestamp = state.timestamp | 3;
        state.registers[11].timestamp = state.timestamp | 3;
        state.registers[12].timestamp = state.timestamp | 3;

        state.registers[12].value = final_x12;
    } else {
        // skip all memory side effects
        ram.skip_if_replaying(24 + 16);

        // update registers and control flow - can use state.timestamp
        state.registers[10].timestamp = state.timestamp | 3;
        state.registers[11].timestamp = state.timestamp | 3;
        state.registers[12].timestamp = state.timestamp | 3;

        state.registers[12].value = final_x12;
    }
}
