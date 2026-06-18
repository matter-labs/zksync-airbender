use super::*;
use field::PrimeField;

#[inline(always)]
pub(crate) fn mop_addmod<C: Counters, S: Snapshotter<C>, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    operand_1.add_assign(&operand_2);
    let rd = operand_1.as_u32_raw_repr_reduced();
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mop_submod<C: Counters, S: Snapshotter<C>, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    operand_1.sub_assign(&operand_2);
    let rd = operand_1.as_u32_raw_repr_reduced();
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mop_mulmod<C: Counters, S: Snapshotter<C>, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    operand_1.mul_assign(&operand_2);
    let rd = operand_1.as_u32_raw_repr_reduced();
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mop_fmamod<C: Counters, S: Snapshotter<C>, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let rd_old_value = unsafe { state.registers.get_unchecked(instr.rd as usize).value };
    let operand_1 = F::from_raw_repr_with_reduction(rs1_value);
    let operand_2 = F::from_raw_repr_with_reduction(rs2_value);
    let mut result = F::from_raw_repr_with_reduction(rd_old_value);
    result.add_assign_product(&operand_1, &operand_2);
    let rd = result.as_u32_raw_repr_reduced();
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mop_tri_add<C: Counters, S: Snapshotter<C>, R: RAM, F: PrimeField>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let rd_old_value = unsafe { state.registers.get_unchecked(instr.rd as usize).value };
    let rd = rs1_value.wrapping_add(rs2_value).wrapping_add(rd_old_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
