use super::*;

#[inline(always)]
pub(crate) fn branch<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
    instr: Instruction,
) {
    let rs1_value = read_register::<C, 0>(state, instr.rs1);
    let rs2_value = read_register::<C, 1>(state, instr.rs2);
    let jump_address = state.pc.wrapping_add(instr.imm);
    let funct3 = instr.rd;
    let negate = funct3 & 0b001 > 0; // lowest bit indicates eq <=> ne, lt <=> gte and so on

    // NOTE: we can hope that compiler makes a jump table here
    let mut should_jump = match funct3 & 0b110 {
        0b000 => rs1_value == rs2_value,
        0b100 => (rs1_value as i32) < (rs2_value as i32),
        0b110 => rs1_value < rs2_value,
        _ => unsafe {
            core::hint::unreachable_unchecked();
        },
    };
    if negate {
        should_jump = !should_jump;
    }
    if should_jump {
        if core::hint::unlikely(jump_address & 0x3 != 0) {
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
