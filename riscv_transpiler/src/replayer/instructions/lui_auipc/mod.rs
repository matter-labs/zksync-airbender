use super::*;

#[inline(always)]
pub(crate) fn lui<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);

    let (rs1_ts) = touch_x0_with_ts::<C, 0>(state);
    let (rs2_ts) = touch_x0_with_ts::<C, 1>(state);
    let mut rd = instr.imm;
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
                rs1_value: 0,
                rs2_value: 0,
                rd_old_value,
                rd_value: rd,
                new_pc: state.pc.wrapping_add(4),
                delegation_type: 0,
            },
            rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
            rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
            rd_read_timestamp: TimestampData::from_scalar(rd_ts),
            cycle_timestamp: TimestampData::from_scalar(state.timestamp),
        };
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn auipc<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);

    let (rs1_ts) = touch_x0_with_ts::<C, 0>(state);
    let (rs2_ts) = touch_x0_with_ts::<C, 1>(state);
    let mut rd = state.pc.wrapping_add(instr.imm);
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
                rs1_value: 0,
                rs2_value: 0,
                rd_old_value,
                rd_value: rd,
                new_pc: state.pc.wrapping_add(4),
                delegation_type: 0,
            },
            rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
            rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
            rd_read_timestamp: TimestampData::from_scalar(rd_ts),
            cycle_timestamp: TimestampData::from_scalar(state.timestamp),
        };
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}
