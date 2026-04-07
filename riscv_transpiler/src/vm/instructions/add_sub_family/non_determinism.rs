use super::*;

#[inline(always)]
pub(crate) fn nd_read<C: Counters, S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
    state: &mut State<C>,
    _ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
    nd: &mut ND,
) {
    debug_assert_eq!(instr.rs1, 0);
    debug_assert_eq!(instr.rs2, 0);

    touch_x0::<C, 1>(state);
    let rd = nd.read();
    snapshotter.append_arbitrary_value(rd);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn nd_write<C: Counters, S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
    state: &mut State<C>,
    ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
    nd: &mut ND,
) {
    debug_assert_eq!(instr.rs2, 0);
    debug_assert_eq!(instr.rd, 0);

    // NOTE: In circuits we will just read from x0
    let non_determinism_write_value =
        unsafe { state.registers.get_unchecked(instr.rs1 as usize).value };
    touch_x0::<C, 1>(state);
    nd.write_with_memory_access(&*ram, non_determinism_write_value);
    write_register_for_pure_opcode::<C, 2>(state, 0, 0);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(state);
}
