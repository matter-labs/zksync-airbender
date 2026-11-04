use super::*;

#[inline(always)]
pub(crate) fn jal<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let rs1_ts = touch_x0_with_ts::<C, 0>(state);
    let rs2_ts = touch_x0_with_ts::<C, 1>(state);
    let mut rd = state.pc.wrapping_add(core::mem::size_of::<u32>() as u32); // address of next opcode
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    let jump_address = state.pc.wrapping_add(instr.imm);

    if tracer.needs_tracing_data_for_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
                rs1_value: 0,
                rs2_value: 0,
                rd_old_value,
                rd_value: rd,
                new_pc: jump_address,
                delegation_type: 0,
            },
            rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
            rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
            rd_read_timestamp: TimestampData::from_scalar(rd_ts),
            cycle_timestamp: TimestampData::from_scalar(state.timestamp),
        };
        tracer.write_non_memory_family_data::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    state.pc = jump_address;
}

#[inline(always)]
pub(crate) fn jalr<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let rs2_ts = touch_x0_with_ts::<C, 1>(state);
    let mut rd = state.pc.wrapping_add(core::mem::size_of::<u32>() as u32); // address of next opcode
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, instr.rd, &mut rd);

    let jump_address = rs1_value.wrapping_add(instr.imm) & !0x1;

    if tracer.needs_tracing_data_for_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
                rs1_value,
                rs2_value: 0,
                rd_old_value,
                rd_value: rd,
                new_pc: jump_address,
                delegation_type: 0,
            },
            rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
            rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
            rd_read_timestamp: TimestampData::from_scalar(rd_ts),
            cycle_timestamp: TimestampData::from_scalar(state.timestamp),
        };
        tracer.write_non_memory_family_data::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    state.pc = jump_address;
}
