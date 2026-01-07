use super::*;

#[inline(always)]
pub(crate) fn add_op<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value;
    if USE_IMM {
        touch_x0::<C, 1>(state);
        rs2_value = instr.imm;
    } else {
        rs2_value = read_register::<C, 1>(state, instr.rs2);
    }
    let mut rd = rs1_value.wrapping_add(rs2_value);
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn sub_op<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut rd = rs1_value.wrapping_sub(rs2_value);
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
