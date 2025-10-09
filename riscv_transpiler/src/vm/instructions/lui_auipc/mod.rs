use super::*;

#[inline(always)]
pub(crate) fn lui<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let _rs1_value = read_register::<C, 0>(state, instr.rs1);
    let _rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let mut rd = instr.imm;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn auipc<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let _rs1_value = read_register::<C, 0>(state, instr.rs1);
    let _rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let mut rd = state.pc.wrapping_add(instr.imm);
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
