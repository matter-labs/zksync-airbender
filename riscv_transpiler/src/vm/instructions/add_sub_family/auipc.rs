use super::*;

#[inline(always)]
pub(crate) fn auipc<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);

    touch_x0::<C, 1>(state);
    let rd = state.pc.wrapping_add(instr.imm);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
