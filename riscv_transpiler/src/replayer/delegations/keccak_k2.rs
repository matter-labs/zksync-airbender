use super::*;
use crate::vm::delegations::keccak_k2::*;
use crate::witness::delegation::keccak_k2::{
    KeccakChi5DelegationWitness, KeccakColumnParityDelegationWitness,
    KeccakThetaRhoDelegationWitness,
};
use common_constants::delegation_types::keccak_k2::*;
use common_constants::*;

const COLUMN_PARITY: u16 = KECCAK_COLUMN_PARITY_CSR_REGISTER as u16;
const THETA_RHO: u16 = KECCAK_THETA_RHO_CSR_REGISTER as u16;
const CHI5: u16 = KECCAK_CHI5_CSR_REGISTER as u16;

macro_rules! call_witness {
    ($witness:ty, $slots:expr, $num_slots:expr, $control:expr, $next_control:expr, $x10_ts:expr, $x11:expr, $x11_ts:expr, $current_ts:expr, $local_state:expr, $local_ts:expr) => {{
        let mut witness = <$witness>::empty();
        witness.write_timestamp = $current_ts | DELEGATION_INVOCATION_OFFSET;
        witness.reg_accesses[0] = RegisterOrIndirectReadWriteData {
            read_value: $control,
            write_value: $next_control,
            timestamp: TimestampData::from_scalar($x10_ts),
        };
        witness.reg_accesses[1] = RegisterOrIndirectReadWriteData {
            read_value: $x11,
            write_value: $x11,
            timestamp: TimestampData::from_scalar($x11_ts),
        };
        for i in 0..$num_slots {
            let slot = $slots[i];
            witness.variables_offsets[i] = slot as u16;
            let value = $local_state[slot];
            witness.indirect_writes[2 * i].read_value = value as u32;
            witness.indirect_writes[2 * i + 1].read_value = (value >> 32) as u32;
            witness.indirect_writes[2 * i].timestamp =
                TimestampData::from_scalar($local_ts[2 * slot]);
            witness.indirect_writes[2 * i + 1].timestamp =
                TimestampData::from_scalar($local_ts[2 * slot + 1]);
        }
        keccak_k2_apply(&mut $local_state, $control);
        for i in 0..$num_slots {
            let slot = $slots[i];
            let value = $local_state[slot];
            witness.indirect_writes[2 * i].write_value = value as u32;
            witness.indirect_writes[2 * i + 1].write_value = (value >> 32) as u32;
            $local_ts[2 * slot] = $current_ts | 3;
            $local_ts[2 * slot + 1] = $current_ts | 3;
        }
        witness
    }};
}

#[inline(never)]
pub(crate) fn keccak_k2_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    const NUM_CALLS: usize = NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600;
    const LAST_CALL_OFFSET: TimestampScalar = ((NUM_CALLS - 1) as TimestampScalar) * TIMESTAMP_STEP;
    let needs_cycle_data =
        tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();
    let needs = [
        tracer.needs_tracing_data_for_delegation_type::<COLUMN_PARITY>(),
        tracer.needs_tracing_data_for_delegation_type::<THETA_RHO>(),
        tracer.needs_tracing_data_for_delegation_type::<CHI5>(),
    ];
    let needs_delegation_data = needs.iter().any(|&n| n);

    let x10 = state.registers[10].value;
    let x11 = state.registers[11].value;
    debug_assert_eq!(state.timestamp % 4, 0);
    assert!(
        x11 as usize >= common_constants::rom::ROM_BYTE_SIZE,
        "state ptr is not in RAM"
    );
    assert_eq!(x11 % 256, 0, "state ptr is not aligned");
    assert_eq!(x10, INITIAL_KECCAK_K2_CONTROL_VALUE);

    let timestamp_on_entry = state.timestamp;
    if needs_cycle_data {
        for call in 0..NUM_CALLS {
            let next_pc = state.pc.wrapping_add(4);
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
                    delegation_type: keccak_k2_call_csr(call) as u16,
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
            if call != NUM_CALLS - 1 {
                state.timestamp += TIMESTAMP_STEP;
            }
        }
    } else {
        state.timestamp += LAST_CALL_OFFSET;
        state.pc = state
            .pc
            .wrapping_add((core::mem::size_of::<u32>() * NUM_CALLS) as u32);
        state.registers[0].timestamp = state.timestamp | 2;
    }
    assert_eq!(state.timestamp, timestamp_on_entry + LAST_CALL_OFFSET);

    if needs_delegation_data {
        let artificial_read_timestamp = timestamp_on_entry + LAST_CALL_OFFSET + 3 + 1;
        let mut local_state = [0u64; 31];
        let mut local_ts = [0 as TimestampScalar; 31 * 2];
        let mut addr = x11;
        for i in 0..KECCAK_K2_ACCESSED_SLOTS {
            let (low_ts, low_value) = ram.read_word(addr, artificial_read_timestamp);
            let (high_ts, high_value) = ram.read_word(addr + 4, artificial_read_timestamp);
            addr += 8;
            local_state[i] = (low_value as u64) | ((high_value as u64) << 32);
            local_ts[2 * i] = low_ts;
            local_ts[2 * i + 1] = high_ts;
        }

        let mut control = x10;
        let mut x10_timestamp = state.registers[10].timestamp;
        let mut x11_timestamp = state.registers[11].timestamp;
        let mut current_ts = timestamp_on_entry;
        for _ in 0..NUM_CALLS {
            let next_control = keccak_k2_bump_control(control);
            let (precompile, _, _) = keccak_k2_decode_control(control);
            let slots = keccak_k2_slots(control);
            match precompile {
                KECCAK_COLUMN_PARITY_PRECOMPILE => {
                    let witness = call_witness!(
                        KeccakColumnParityDelegationWitness,
                        slots,
                        KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
                        control,
                        next_control,
                        x10_timestamp,
                        x11,
                        x11_timestamp,
                        current_ts,
                        local_state,
                        local_ts
                    );
                    if needs[0] {
                        tracer.write_delegation::<COLUMN_PARITY, _, _, _, _>(witness);
                    }
                }
                KECCAK_THETA_RHO_PRECOMPILE => {
                    let witness = call_witness!(
                        KeccakThetaRhoDelegationWitness,
                        slots,
                        KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
                        control,
                        next_control,
                        x10_timestamp,
                        x11,
                        x11_timestamp,
                        current_ts,
                        local_state,
                        local_ts
                    );
                    if needs[1] {
                        tracer.write_delegation::<THETA_RHO, _, _, _, _>(witness);
                    }
                }
                _ => {
                    let witness = call_witness!(
                        KeccakChi5DelegationWitness,
                        slots,
                        KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
                        control,
                        next_control,
                        x10_timestamp,
                        x11,
                        x11_timestamp,
                        current_ts,
                        local_state,
                        local_ts
                    );
                    if needs[2] {
                        tracer.write_delegation::<CHI5, _, _, _, _>(witness);
                    }
                }
            }
            x10_timestamp = current_ts | 3;
            x11_timestamp = current_ts | 3;
            control = next_control;
            current_ts += TIMESTAMP_STEP;
        }
        assert_eq!(control, FINAL_KECCAK_K2_CONTROL_VALUE);
        assert_eq!(current_ts - TIMESTAMP_STEP, state.timestamp);
    } else {
        ram.skip_if_replaying(KECCAK_K2_ACCESSED_SLOTS * 2);
    }

    state.registers[10].value = FINAL_KECCAK_K2_CONTROL_VALUE;
    state.registers[10].timestamp = state.timestamp | 3;
    state.registers[11].timestamp = state.timestamp | 3;
}
