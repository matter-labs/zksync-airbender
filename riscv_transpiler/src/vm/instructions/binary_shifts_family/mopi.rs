use super::*;

#[inline(always)]
pub(crate) fn mopi_xor_rot<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    // rs2 aliases rd (set at decode): the second XOR operand is rd's old value,
    // read through the rs2 port at sub-slot +1.
    debug_assert_eq!(instr.rs2, instr.rd);
    let rd_old_value = read_register::<C, 1>(state, instr.rs2);
    let rotation_value = instr.imm;
    let rd = (rd_old_value ^ rs1_value).rotate_right(rotation_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}
