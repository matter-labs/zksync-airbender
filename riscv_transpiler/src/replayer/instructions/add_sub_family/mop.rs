use super::*;
use field::PrimeField;

#[inline(always)]
pub(crate) fn mop_addmod<C: Counters, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let mut operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    operand_1.add_assign(&operand_2);
    let rd = operand_1.as_u32_raw_repr_reduced();
    let (rd_old_value, rd_ts) = write_register_with_ts_for_pure_opcode::<C, 2>(state, instr.rd, rd);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
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
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn mop_submod<C: Counters, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let mut operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    operand_1.sub_assign(&operand_2);
    let rd = operand_1.as_u32_raw_repr_reduced();
    let (rd_old_value, rd_ts) = write_register_with_ts_for_pure_opcode::<C, 2>(state, instr.rd, rd);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
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
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn mop_mulmod<C: Counters, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let mut operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    operand_1.mul_assign(&operand_2);
    let rd = operand_1.as_u32_raw_repr_reduced();
    let (rd_old_value, rd_ts) = write_register_with_ts_for_pure_opcode::<C, 2>(state, instr.rd, rd);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
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
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn mop_tri_add<C: Counters, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    // 3-input addition: rd = rs1 + rs2 + rd_old (wrapping u32), rd_old read like fmamod.
    // Mirrors `vm::instructions::add_sub_family::mop::mop_tri_add`.
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let rd_raw_read_value = unsafe { state.registers.get_unchecked(instr.rd as usize).value };
    let rd = rs1_value
        .wrapping_add(rs2_value)
        .wrapping_add(rd_raw_read_value);
    let (rd_old_value, rd_ts) = write_register_with_ts_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    debug_assert_eq!(rd_old_value, rd_raw_read_value);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
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
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}

#[inline(always)]
pub(crate) fn mop_fmamod<C: Counters, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    instr: Instruction,
    tracer: &mut impl WitnessTracer,
) {
    let (rs1_value, rs1_ts) = read_register_with_ts::<C, 0>(state, instr.rs1);
    let (rs2_value, rs2_ts) = read_register_with_ts::<C, 1>(state, instr.rs2);
    let rd_raw_read_value = unsafe { state.registers.get_unchecked(instr.rd as usize).value };
    let operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    let mut result = F::from_raw_repr_with_reduction(rd_raw_read_value);
    result.add_assign_product(&operand_1, &operand_2);
    let rd = result.as_u32_raw_repr_reduced();
    let (rd_old_value, rd_ts) = write_register_with_ts_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    debug_assert_eq!(rd_old_value, rd_raw_read_value);

    if tracer.needs_tracing_data_for_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>() {
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
        tracer
            .write_non_memory_family_data::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(traced_data);
    }
    default_increase_pc::<C>(state);
}
