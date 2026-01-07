use super::*;

#[inline(always)]
pub(crate) fn branch<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let (rd_old_value, rd_ts) = write_register_with_ts::<C, 2>(state, 0, &mut 0);

    let jump_address = state.pc.wrapping_add(instr.imm);

    let funct3 = instr.rd;
    let negate = funct3 & 0b001 > 0; // lowest bit indicates eq <=> ne, lt <=> gte and so on

    // NOTE: we can hope that compiler makes a jump table here
    let mut should_jump = match funct3 & 0b110 {
        0b000 => rs1_value == rs2_value,
        0b100 => (rs1_value as i32) < (rs2_value as i32),
        0b110 => rs1_value < rs2_value,
        _ => unsafe {
            core::hint::unreachable_unchecked();
        },
    };
    if negate {
        should_jump = !should_jump;
    }

    let jump_address = if should_jump {
        jump_address
    } else {
        state.pc.wrapping_add(4)
    };

    if tracer.needs_tracing_data_for_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
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
    }
    state.pc = jump_address;
}
