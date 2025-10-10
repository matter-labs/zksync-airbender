use super::*;
use field::Field;
use field::Mersenne31Field;

#[inline(always)]
pub(crate) fn mop_addmod<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let mut operand_1 = Mersenne31Field::from_nonreduced_u32(rs1_value);
    let operand_2 = Mersenne31Field::from_nonreduced_u32(rs2_value);
    operand_1.add_assign(&operand_2);
    let mut rd = operand_1.to_reduced_u32();
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mop_submod<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let mut operand_1 = Mersenne31Field::from_nonreduced_u32(rs1_value);
    let operand_2 = Mersenne31Field::from_nonreduced_u32(rs2_value);
    operand_1.sub_assign(&operand_2);
    let mut rd = operand_1.to_reduced_u32();
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mop_mulmod<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let mut operand_1 = Mersenne31Field::from_nonreduced_u32(rs1_value);
    let operand_2 = Mersenne31Field::from_nonreduced_u32(rs2_value);
    operand_1.mul_assign(&operand_2);
    let mut rd = operand_1.to_reduced_u32();
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
