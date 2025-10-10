use super::*;

#[inline(always)]
pub(crate) fn sll<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let mut rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    if USE_IMM {
        rs2_value = instr.imm;
    }
    let mut rd = rs1_value.wrapping_shl(rs2_value);
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn srl<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let mut rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    if USE_IMM {
        rs2_value = instr.imm;
    }
    let mut rd = rs1_value.wrapping_shr(rs2_value);
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn sra<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let mut rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    if USE_IMM {
        rs2_value = instr.imm;
    }
    let mut rd = (rs1_value as i32).wrapping_shr(rs2_value) as u32;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>(state);
}
