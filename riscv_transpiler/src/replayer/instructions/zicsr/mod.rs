use super::*;

use common_constants::NON_DETERMINISM_CSR;

#[inline(always)]
pub(crate) fn nd_read<C: Counters, R: RAM, ND: NonDeterminismCSRSource>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
    nd: &mut ND,
) {
    let rs1_ts = touch_x0_with_ts::<C, 0>(state);
    let rs2_ts = touch_x0_with_ts::<C, 1>(state);

    let mut rd = if R::REPLAY_NON_DETERMINISM_VIA_RAM_STUB {
        // we snapshot all non-determinism reads. Address and timestamp are not important here
        let (ts, value) = ram.read_word(
            common_constants::rom::ROM_BYTE_SIZE as u32,
            common_constants::INITIAL_TIMESTAMP,
        );
        assert_eq!(
            ts, 0,
            "expected zero timestamp for non-determinism record in replayer RAM"
        );

        value
    } else {
        nd.read()
    };
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    if tracer.needs_tracing_data_for_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
                rs1_value: 0,
                rs2_value: 0,
                rd_old_value,
                rd_value: rd,
                new_pc: state.pc.wrapping_add(4),
                delegation_type: NON_DETERMINISM_CSR as u16,
            },
            rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
            rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
            rd_read_timestamp: TimestampData::from_scalar(rd_ts),
            cycle_timestamp: TimestampData::from_scalar(state.timestamp),
        };
        tracer.write_non_memory_family_data::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn nd_write<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let rs2_ts = touch_x0_with_ts::<C, 1>(state);
    let rd_ts = touch_x0_with_ts::<C, 2>(state);

    if tracer.needs_tracing_data_for_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
                rs1_value,
                rs2_value: 0,
                rd_old_value: 0,
                rd_value: 0,
                new_pc: state.pc.wrapping_add(4),
                delegation_type: NON_DETERMINISM_CSR as u16,
            },
            rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
            rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
            rd_read_timestamp: TimestampData::from_scalar(rd_ts),
            cycle_timestamp: TimestampData::from_scalar(state.timestamp),
        };
        tracer.write_non_memory_family_data::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn call_delegation<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);
    debug_assert_eq!(instr.rd, 0);

    let delegation_type = match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16
        }
        a if a == DelegationType::Blake as u32 => {
            common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16
        }
        a if a == DelegationType::Keccak as u32 => {
            common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    };

    // and then trigger delegation
    match instr.imm {
        a if a == DelegationType::BigInt as u32 => {
            delegations::bigint::bigint_call::<C, R>(state, ram, tracer)
        }
        a if a == DelegationType::Blake as u32 => {
            delegations::blake2_round_function::blake2_round_function_call::<C, R>(
                state, ram, tracer,
            )
        }
        a if a == DelegationType::Keccak as u32 => {
            delegations::keccak_special5::keccak_special5_call::<C, R>(state, ram, tracer);
        }
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}
