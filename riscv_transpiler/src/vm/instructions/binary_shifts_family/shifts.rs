use super::*;

#[inline(always)]
pub(crate) fn sll<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value.wrapping_shl(rs2_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn srl<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value.wrapping_shr(rs2_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn sra<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = (rs1_value as i32).wrapping_shr(rs2_value) as u32;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn rol<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value.rotate_left(rs2_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn ror<C: Counters, S: Snapshotter<C>, R: RAM>(
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
    let rd = rs1_value.rotate_right(rs2_value);
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(state);
}
