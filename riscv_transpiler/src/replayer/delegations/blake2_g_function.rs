use std::mem::MaybeUninit;

use super::*;
use crate::vm::delegations::blake2_g_function::*;
use crate::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use blake2s_u32::g_function_control_flags::*;
use blake2s_u32::*;
use common_constants::*;

// NOTE: in forward execution we read through x11 and dump witness, and then dump writes via x10,
// so in the function below we will just read via x11 and x10

#[inline(never)]
pub(crate) fn blake2_g_function_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    let needs_cycle_data =
        tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();
    let needs_delegation_data =
        tracer.needs_tracing_data_for_delegation_type::<{
            common_constants::blake2s_g_function::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16
        }>();

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

    assert!(x10 % 64 == 0, "state pointer is unaligned");
    assert!(x11 % 64 == 0, "input pointer is unaligned");

    assert!(
        x12 < (1 << BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS),
        "control register 0x{:08x} is too large",
        x12
    );

    let control_bitmask = x12 >> BLAKE2S_G_FUNCTION_COUNTER_BITS;
    let counter = x12 & ((1 << BLAKE2S_G_FUNCTION_COUNTER_BITS) - 1);

    assert_eq!(counter, 0, "invoked in the middle of round function");

    let reduced_rounds = control_bitmask & TEST_IF_REDUCE_ROUNDS_MASK == TEST_IF_REDUCE_ROUNDS_MASK;

    let _num_rounds = if reduced_rounds { 7 } else { 10 };
    let num_invocations = _num_rounds * BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;

    let final_x12 = control_bitmask << BLAKE2S_G_FUNCTION_COUNTER_BITS;

    if needs_cycle_data == false && needs_delegation_data == false {
        ram.skip_if_replaying(
            BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS + BLAKE2S_BLOCK_SIZE_U32_WORDS,
        );

        state.timestamp += ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP;
        state.pc = state
            .pc
            .wrapping_add((core::mem::size_of::<u32>() * num_invocations) as u32);

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
        for call_round in 0..num_invocations {
            let last_round = call_round == num_invocations - 1;
            {
                // cycle
                let next_pc = state.pc.wrapping_add(4);
                // touch x0
                let x0_timestamp = state.registers[0].timestamp;
                // NOTE: we only touch x0 as rs1, and as rd
                state.registers[0].timestamp = state.timestamp | 2;
                let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
                    opcode_data: NonMemoryOpcodeTracingData {
                        initial_pc: state.pc,
                        rs1_value: 0,
                        rs2_value: 0,
                        rd_old_value: 0,
                        rd_value: 0,
                        new_pc: next_pc,
                        delegation_type: BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
                    },
                    rs1_read_timestamp: TimestampData::from_scalar(x0_timestamp),
                    rs2_read_timestamp: TimestampData::from_scalar(0),
                    rd_read_timestamp: TimestampData::from_scalar(state.timestamp),
                    cycle_timestamp: TimestampData::from_scalar(state.timestamp),
                };
                tracer.write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
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

        state.timestamp += ((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP;
        state.pc = state
            .pc
            .wrapping_add((core::mem::size_of::<u32>() * num_invocations) as u32);

        state.registers[0].timestamp = state.timestamp | 2;
    }

    if needs_delegation_data {
        let mut current_timestamp = timestamp_on_entry;
        let upper_bound_read_timestamp =
            timestamp_on_entry + (((num_invocations - 1) as TimestampScalar) * TIMESTAMP_STEP) + 3;
        let artificial_read_timestamp = upper_bound_read_timestamp + 1;

        unsafe {
            let mut blake_state_full: [MaybeUninit<u32>;
                BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] =
                [const { MaybeUninit::uninit() }; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS];
            let mut blake_state_initial_timestamps: [MaybeUninit<TimestampScalar>;
                BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] =
                [const { MaybeUninit::uninit() }; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS];

            let state_base_addr = x10;
            for i in 0..BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS {
                let state_word_addr = state_base_addr + (core::mem::size_of::<u32>() * i) as u32;
                let (ts, value) = ram.read_word(state_word_addr, artificial_read_timestamp);

                blake_state_full[i].write(value);
                blake_state_initial_timestamps[i].write(ts);
            }
            let mut blake_extended_state = blake_state_full.map(|el| el.assume_init());
            let mut blake_state_timestamps =
                blake_state_initial_timestamps.map(|el| el.assume_init());

            // and input doesn't change across calls
            let mut input: [MaybeUninit<u32>; BLAKE2S_BLOCK_SIZE_U32_WORDS] =
                [const { MaybeUninit::uninit() }; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            let mut input_initial_timestamps: [MaybeUninit<TimestampScalar>;
                BLAKE2S_BLOCK_SIZE_U32_WORDS] =
                [const { MaybeUninit::uninit() }; BLAKE2S_BLOCK_SIZE_U32_WORDS];

            let input_base_addr = x11;
            for i in 0..BLAKE2S_BLOCK_SIZE_U32_WORDS {
                let input_word_addr = input_base_addr + (core::mem::size_of::<u32>() * i) as u32;
                let (ts, value) = ram.read_word(input_word_addr, artificial_read_timestamp);

                input[i].write(value);
                input_initial_timestamps[i].write(ts);
            }
            let input = input.map(|el| el.assume_init());
            let mut input_timestamps = input_initial_timestamps.map(|el| el.assume_init());

            let mut control_flow_reg = x12;
            let mut x10_timestamp = state.registers[10].timestamp;
            let mut x11_timestamp = state.registers[11].timestamp;
            let mut x12_timestamp = state.registers[12].timestamp;

            for g_function_call_idx in 0..num_invocations {
                let write_ts = current_timestamp | 3;

                let updated_control_flow = {
                    let mut next_counter = g_function_call_idx + 1;
                    // counter wraps to 0
                    if next_counter >= num_invocations {
                        next_counter = 0;
                    }
                    let updated_x12 = (control_bitmask << BLAKE2S_G_FUNCTION_COUNTER_BITS)
                        | (next_counter as u32);

                    updated_x12
                };

                let mut witness = Blake2sGFunctionDelegationWitness::empty();
                witness.write_timestamp = current_timestamp | DELEGATION_INVOCATION_OFFET;

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

                // every time we read 4 elements from state and 2 elements from input

                let round_number =
                    (g_function_call_idx as usize) / BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
                let mixing_function_number =
                    (g_function_call_idx as usize) % BLAKE2S_G_FUNCTIONS_PER_ROUND_FUNCTION;
                let sigma_pairs = &SIGMAS_BY_PAIRS[round_number];

                let [a, b, c, d] = MIXING_FUNCTION_ACCESS_IDXES[mixing_function_number];
                let [x, y] = sigma_pairs[mixing_function_number];

                let state_read_values = [a, b, c, d].map(|el| blake_extended_state[el]);
                let state_read_timestamp = [a, b, c, d].map(|el| {
                    let read_ts = blake_state_timestamps[el];
                    blake_state_timestamps[el] = write_ts;

                    read_ts
                });
                let input_read_values = [x, y].map(|el| input[el]);
                let input_read_timestamp = [x, y].map(|el| {
                    let read_ts = input_timestamps[el];
                    input_timestamps[el] = write_ts;

                    read_ts
                });

                g_function(&mut blake_extended_state, a, b, c, d, input[x], input[y]);

                let state_write_values = [a, b, c, d].map(|el| blake_extended_state[el]);

                for i in 0..BLAKE2S_G_FUNCTION_X10_NUM_WRITES {
                    witness.indirect_writes[i].read_value = state_read_values[i];
                    witness.indirect_writes[i].write_value = state_write_values[i];
                    witness.indirect_writes[i].timestamp =
                        TimestampData::from_scalar(state_read_timestamp[i]);
                }

                for i in 0..BLAKE2S_G_FUNCTION_X11_NUM_READS {
                    witness.indirect_reads[i].read_value = input_read_values[i];
                    witness.indirect_reads[i].timestamp =
                        TimestampData::from_scalar(input_read_timestamp[i]);
                }

                // and fill offsets. They are in u32 WORDS
                witness.variables_offsets[0] = a as u16;
                witness.variables_offsets[1] = b as u16;
                witness.variables_offsets[2] = c as u16;
                witness.variables_offsets[3] = d as u16;
                witness.variables_offsets[4] = x as u16;
                witness.variables_offsets[5] = y as u16;

                tracer.write_delegation::<{
                    common_constants::blake2s_g_function::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16
                }, _, _, _, _>(witness);

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
        ram.skip_if_replaying(
            BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS + BLAKE2S_BLOCK_SIZE_U32_WORDS,
        );

        // update registers and control flow - can use state.timestamp
        state.registers[10].timestamp = state.timestamp | 3;
        state.registers[11].timestamp = state.timestamp | 3;
        state.registers[12].timestamp = state.timestamp | 3;

        state.registers[12].value = final_x12;
    }
}
