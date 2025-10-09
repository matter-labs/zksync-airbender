use super::*;

#[inline(always)]
pub(crate) fn branch<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2); // formal
    let jump_address = state.pc.wrapping_add(instr.imm);
    // do unsigned comparison and then resolve it
    let eq = rs1_value == rs2_value;
    let unsigned_lt = rs1_value < rs2_value;
    let signed_lt = (rs1_value as i32) < (rs2_value as i32);
    // ISA has enough bits in funct3 to make it simple logical expression, and for now we rely on compiler to simplify it
    let funct3 = instr.rd;
    let should_jump = (funct3 == 0 && eq)
        || (funct3 == 1 && !eq)
        || (funct3 == 4 && signed_lt)
        || (funct3 == 5 && !signed_lt)
        || (funct3 == 6 && unsigned_lt)
        || (funct3 == 7 && !unsigned_lt);
    if should_jump {
        if jump_address & 0x3 != 0 {
            // unaligned PC
            panic!("Unaligned jump address 0x{:08x}", jump_address);
        } else {
            state.pc = jump_address;
        }
    } else {
        default_increase_pc::<C>(state);
    }
    write_register::<C, 2>(state, 0, &mut 0);
    increment_family_counter::<C, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(state);
}
