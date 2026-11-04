use super::*;

#[inline(always)]
pub(crate) fn and<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
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
    let mut rd = rs1_value & rs2_value;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn or<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
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
    let mut rd = rs1_value | rs2_value;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn xor<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
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
    let mut rd = rs1_value ^ rs2_value;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}
