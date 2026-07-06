use super::*;

#[inline(always)]
pub(crate) fn mopi_xor_rot<C: Counters, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    // xor-rotate: rd = (rd_old ^ rs1) >>> imm. rs2 aliases rd (set at decode), so the second
    // XOR operand — rd's old value — arrives through the rs2 read port at sub-slot +1 and the
    // circuit reuses the rs2 byte decomposition. Rotation amount lives in `imm`.
    // Mirrors `vm::instructions::binary_shifts_family::mopi::mopi_xor_rot`.
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    debug_assert_eq!(instr.rs2, instr.rd);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let rotation_value = instr.imm;
    let rd = (rs2_value ^ rs1_value).rotate_right(rotation_value);
    let (rd_old_value, rd_ts) = write_register_with_ts_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    debug_assert_eq!(rd_old_value, rs2_value);

    if tracer.needs_tracing_data_for_circuit_family::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>() {
        let traced_data = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data: NonMemoryOpcodeTracingData {
                initial_pc: state.pc,
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
        tracer.write_non_memory_family_data::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}
