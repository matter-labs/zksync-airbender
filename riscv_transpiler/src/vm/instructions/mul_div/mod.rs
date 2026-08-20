use super::*;

#[inline(always)]
pub(crate) fn mul<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut rd = (rs1_value as i32).wrapping_mul(rs2_value as i32) as u32;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mulhu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut rd = rs1_value.widening_mul(rs2_value).1;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn divu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut rd = if rs2_value == 0 {
        0xffffffff
    } else {
        rs1_value / rs2_value
    };
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn remu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let mut rd = if rs2_value == 0 {
        rs1_value
    } else {
        rs1_value % rs2_value
    };
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}
