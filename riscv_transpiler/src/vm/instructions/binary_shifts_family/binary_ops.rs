use super::*;

#[inline(always)]
pub(crate) fn and<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value & rs2_value;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn or<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value | rs2_value;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn xor<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value ^ rs2_value;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}
