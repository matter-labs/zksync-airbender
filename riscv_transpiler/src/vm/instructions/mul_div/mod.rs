use super::*;

#[inline(always)]
pub(crate) fn mul<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let rd = (rs1_value as i32).wrapping_mul(rs2_value as i32) as u32;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mulhu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let rd = rs1_value.carrying_mul(rs2_value, 0u32).1;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn divu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let rd = if rs2_value == 0 {
        0xffffffff
    } else {
        rs1_value / rs2_value
    };
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn remu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let rd = if rs2_value == 0 {
        rs1_value
    } else {
        rs1_value % rs2_value
    };
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

// Signed variants (RV32M `mulh`, `mulhsu`, `div`, `rem`). Not provable with the
// shipped circuits (the base layer runs on the unsigned machine), but the
// interpreter supports them so `FullMachineDecoderConfig` programs (e.g. C++
// guests where GCC emits `mulh` for division by constants) can be executed
// and profiled.

#[inline(always)]
pub(crate) fn mulh<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let product = (rs1_value as i32 as i64) * (rs2_value as i32 as i64);
    let rd = (product >> 32) as u32;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn mulhsu<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let product = (rs1_value as i32 as i64) * (rs2_value as u64 as i64);
    let rd = (product >> 32) as u32;
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn div<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1) as i32;
    let rs2_value = read_register::<C, 1>(state, instr.rs2) as i32;
    // RISC-V: division by zero yields -1, overflow (MIN / -1) yields MIN.
    let rd = if rs2_value == 0 {
        u32::MAX
    } else {
        rs1_value.wrapping_div(rs2_value) as u32
    };
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn rem<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    _ram: &mut R,
    _snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1) as i32;
    let rs2_value = read_register::<C, 1>(state, instr.rs2) as i32;
    // RISC-V: remainder by zero yields the dividend, overflow yields 0.
    let rd = if rs2_value == 0 {
        rs1_value as u32
    } else {
        rs1_value.wrapping_rem(rs2_value) as u32
    };
    write_register_for_pure_opcode::<C, 2>(state, instr.rd, rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, MUL_DIV_CIRCUIT_FAMILY_IDX>(state);
}
