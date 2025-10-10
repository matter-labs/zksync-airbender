use super::*;

#[inline(always)]
pub(crate) fn lui<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let mut rd = instr.imm;
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc: state.pc,
            opcode: 0u32,
            rs1_value,
            rs2_value,
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
    tracer.write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn auipc<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2); // formal
    let mut rd = state.pc.wrapping_add(instr.imm);
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc: state.pc,
            opcode: 0u32,
            rs1_value,
            rs2_value,
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
    tracer.write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    default_increase_pc::<C>(state);
}
