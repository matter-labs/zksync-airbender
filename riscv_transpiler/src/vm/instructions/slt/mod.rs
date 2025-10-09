use super::*;

#[inline(always)]
pub(crate) fn slt<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
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
    let mut rd = ((rs1_value as i32) < (rs2_value as i32)) as u32;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(state);
}

#[inline(always)]
pub(crate) fn sltu<C: Counters, S: Snapshotter<C>, R: RAM, const USE_IMM: bool>(
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
    let mut rd = (rs1_value < rs2_value) as u32;
    write_register::<C, 2>(state, instr.rd, &mut rd);
    default_increase_pc::<C>(state);
    increment_family_counter::<C, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(state);
}
