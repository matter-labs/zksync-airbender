use crate::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

use super::*;
use crate::vm::delegations::keccak_special5::{
    keccak_special5_impl_bump_control, keccak_special5_impl_compute_outputs,
    keccak_special5_impl_decode_control, keccak_special5_impl_extract_indices,
};
use common_constants::*;
use risc_v_simulator::machine_mode_only_unrolled::*;
use std::mem::MaybeUninit;

#[inline(never)]
pub(crate) fn keccak_special5_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    let needs_cycle_data =
        tracer.needs_tracing_data_for_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>();
    let needs_delegation_data = tracer.needs_tracing_data_for_delegation_type::<{common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16}>();

    let x10 = state.registers[10].value;
    let x11 = state.registers[11].value;
    debug_assert_eq!(state.timestamp % 4, 0);
    assert!(
        x11 as usize >= common_constants::rom::ROM_BYTE_SIZE,
        "state ptr is not in RAM"
    );
    assert!(x10 < 1 << 11, "control info is too big");
    assert_eq!(x11 % 256, 0, "state ptr is not aligned");

    assert_eq!(x10, common_constants::INITIAL_KECCAK_F1600_CONTROL_VALUE);

    // we have absolutely happy case if we do NOT need any tracing data - just touch x0 enough times, bump PC + timestamp, and update x10

    if needs_cycle_data == false && needs_delegation_data == false {
        ram.skip_if_replaying(31 * 2);

        state.timestamp +=
            ((NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP;
        state.pc = state.pc.wrapping_add(
            (core::mem::size_of::<u32>() * common_constants::NUM_DELEGATION_CALLS_FOR_KECCAK_F1600)
                as u32,
        );

        state.registers[0].timestamp = state.timestamp | 2;

        state.registers[10].value = common_constants::FINAL_KECCAK_F1600_CONTROL_VALUE;
        state.registers[10].timestamp = state.timestamp | 3;

        state.registers[11].timestamp = state.timestamp | 3;

        return;
    }

    let timestamp_on_entry = state.timestamp;

    // branches below will update state.pc and state.timestamp
    if needs_cycle_data {
        // touch x0 many times and formally record
        for call_round in 0..NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 {
            let last_round = call_round == NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1;
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
                        delegation_type: KECCAK_SPECIAL5_CSR_REGISTER as u16,
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
        state.timestamp +=
            ((NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP;
        state.pc = state.pc.wrapping_add(
            (core::mem::size_of::<u32>() * common_constants::NUM_DELEGATION_CALLS_FOR_KECCAK_F1600)
                as u32,
        );

        state.registers[0].timestamp = state.timestamp | 2;
    }

    assert_eq!(
        state.timestamp,
        timestamp_on_entry
            + ((NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP
    );

    // here we can no longer use state.timestamp for a good notion of time, so we use saved one
    if needs_delegation_data {
        let mut current_timestamp = timestamp_on_entry;
        let upper_bound_read_timestamp = timestamp_on_entry
            + (((NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP)
            + 3;
        let artificial_read_timestamp = upper_bound_read_timestamp + 1;

        // now we need to be careful with accessed state elements. We always access u64s only, and for replaying purposes we will need
        // to read 31 state elements (for snapshot), and then we will work over the
        unsafe {
            // we are fine to NOT keep track on the initial timestamps, as we only need final write ones
            let mut local_state: [MaybeUninit<u64>; 31] = [const { MaybeUninit::uninit() }; 31];
            let mut local_state_timestamps: [MaybeUninit<TimestampScalar>; 31 * 2] =
                [const { MaybeUninit::uninit() }; 31 * 2];

            let mut addr = x11;
            for i in 0..31 {
                // low and high
                let (low_ts, low_value) = ram.read_word(addr, artificial_read_timestamp);
                addr += 4;
                let (high_ts, high_value) = ram.read_word(addr, artificial_read_timestamp);
                addr += 4;

                local_state[i].write((low_value as u64) | ((high_value as u64) << 32));
                local_state_timestamps[2 * i].write(low_ts);
                local_state_timestamps[2 * i + 1].write(high_ts);
            }
            let mut local_state = local_state.map(|el| el.assume_init());
            let mut local_state_timestamps = local_state_timestamps.map(|el| el.assume_init());

            let mut control_flow_reg = x10;
            let mut x10_timestamp = state.registers[10].timestamp;
            let mut x11_timestamp = state.registers[11].timestamp;

            for call_round in 0..NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 {
                let last_round = call_round == NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1;

                let mut witness = KeccakSpecial5DelegationWitness::empty();
                witness.write_timestamp = current_timestamp | 3;

                let (precompile, iteration, round) =
                    keccak_special5_impl_decode_control(control_flow_reg);
                let next_control_reg =
                    keccak_special5_impl_bump_control(precompile, iteration, round);
                witness.reg_accesses[0] = RegisterOrIndirectReadWriteData {
                    read_value: control_flow_reg,
                    write_value: next_control_reg,
                    timestamp: TimestampData::from_scalar(x10_timestamp),
                };
                witness.reg_accesses[1] = RegisterOrIndirectReadWriteData {
                    read_value: x11,
                    write_value: x11,
                    timestamp: TimestampData::from_scalar(x11_timestamp),
                };

                x10_timestamp = current_timestamp | 3;
                x11_timestamp = current_timestamp | 3;

                let state_indexes =
                    keccak_special5_impl_extract_indices(precompile, iteration, round);

                for i in 0..KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS {
                    witness.variables_offsets[i] = state_indexes[i] as u16;
                }

                // get inputs, and also write down timestamps into witness
                let mut state_inputs = [0u64; 6];
                for i in 0..6 {
                    let state_index = state_indexes[i];
                    state_inputs[i] = local_state[state_index];

                    // read values for witness
                    let value = state_inputs[i];
                    let low = value as u32;
                    let high = (value >> 32) as u32;
                    witness.indirect_writes[i * 2].read_value = low;
                    witness.indirect_writes[i * 2 + 1].read_value = high;
                    // read timestamps
                    witness.indirect_writes[2 * i].timestamp =
                        TimestampData::from_scalar(local_state_timestamps[2 * state_index]);
                    witness.indirect_writes[2 * i + 1].timestamp =
                        TimestampData::from_scalar(local_state_timestamps[2 * state_index + 1]);
                }
                let state_inputs = state_indexes.map(|i| local_state[i]);
                // get outputs
                let state_outputs = keccak_special5_impl_compute_outputs(
                    precompile,
                    iteration,
                    round,
                    state_inputs,
                );
                // write back
                for i in 0..6 {
                    // update local state
                    let state_index = state_indexes[i];
                    local_state[state_index] = state_outputs[i];
                    local_state_timestamps[2 * state_index] = current_timestamp | 3;
                    local_state_timestamps[2 * state_index + 1] = current_timestamp | 3;

                    // record writes into witness too
                    let value = state_outputs[i];
                    let low = value as u32;
                    let high = (value >> 32) as u32;
                    witness.indirect_writes[i * 2].write_value = low;
                    witness.indirect_writes[i * 2 + 1].write_value = high;
                }

                tracer.write_delegation::<{common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16}, _, _, _, _>(witness);

                control_flow_reg = next_control_reg;
                current_timestamp += TIMESTAMP_STEP;
            }
        }
        assert_eq!(current_timestamp - TIMESTAMP_STEP, state.timestamp);

        // update registers and control flow - can use state.timestamp
        state.registers[10].value = common_constants::FINAL_KECCAK_F1600_CONTROL_VALUE;
        state.registers[10].timestamp = state.timestamp | 3;

        state.registers[11].timestamp = state.timestamp | 3;
    } else {
        // skip all memory side effects
        ram.skip_if_replaying(31 * 2);

        // update registers and control flow - can use state.timestamp
        state.registers[10].value = common_constants::FINAL_KECCAK_F1600_CONTROL_VALUE;
        state.registers[10].timestamp = state.timestamp | 3;

        state.registers[11].timestamp = state.timestamp | 3;
    }
}
