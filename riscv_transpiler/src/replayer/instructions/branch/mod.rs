use super::*;

#[inline(always)]
pub(crate) fn branch<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2); // formal
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, 0, &mut 0);

    let jump_address = state.pc.wrapping_add(instr.imm);
    // do unsigned comparison and then resolve it
    let eq = rs1_value == rs2_value;
    let unsigned_lt = rs1_value < rs2_value;
    let signed_lt = (rs1_value as i32) < (rs2_value as i32);

    // ISA has enough bits in funct3 to make it simple logical expression, and for now we rely on compiler to simplify it
    let funct3 = instr.rd;
    let should_jump = (funct3 == 0 && eq)
        || (funct3 == 1 && !eq)
        || (funct3 == 4 && signed_lt)
        || (funct3 == 5 && !signed_lt)
        || (funct3 == 6 && unsigned_lt)
        || (funct3 == 7 && !unsigned_lt);

    let jump_address = if should_jump {
        jump_address
    } else {
        state.pc.wrapping_add(4)
    };

    let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc: state.pc,
            opcode: 0u32,
            rs1_value,
            rs2_value,
            rd_old_value,
            rd_value: 0,
            new_pc: jump_address,
            delegation_type: 0,
        },
        rs1_read_timestamp: TimestampData::from_scalar(rs1_ts),
        rs2_read_timestamp: TimestampData::from_scalar(rs2_ts),
        rd_read_timestamp: TimestampData::from_scalar(rd_ts),
        cycle_timestamp: TimestampData::from_scalar(state.timestamp),
    };
    tracer.write_non_memory_family_data::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(traced_data);
    state.pc = jump_address;
}
