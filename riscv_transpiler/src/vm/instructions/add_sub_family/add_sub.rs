use super::*;

#[inline(always)]
pub(crate) fn add_op<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let mut rs2_value = read_register::<C, 1>(state, instr.rs2);
    debug_assert!({
        if instr.rs2 != 0 {
            instr.imm == 0
        } else {
            true
        }
    });
    rs2_value = rs2_value.wrapping_add(instr.imm);
    let rd = rs1_value.wrapping_add(rs2_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn sub_op<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    debug_assert_eq!(instr.imm, 0);

    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    debug_assert_eq!(instr.imm, 0);
    let rd = rs1_value.wrapping_sub(rs2_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
