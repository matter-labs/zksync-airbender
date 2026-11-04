pub const OPCODE_BRANCH: u8 = 0b110_0011;

#[must_use]
#[inline(always)]
pub const fn funct3_bits(src: u32) -> u8 {
    ((src >> 12) & 0b111) as u8
}

#[must_use]
#[inline(always)]
pub const fn funct7_bits(src: u32) -> u8 {
    ((src >> 25) & 0b1111111) as u8
}

#[must_use]
#[inline(always)]
pub const fn get_opcode_bits(src: u32) -> u8 {
    (src & 0b01111111) as u8 // opcode is always lowest 7 bits
}

#[must_use]
#[inline(always)]
pub const fn get_rd_bits(src: u32) -> u8 {
    ((src >> 7) & 0b00011111) as u8
}

#[must_use]
#[inline(always)]
pub const fn get_formal_rs1_bits(src: u32) -> u8 {
    ((src >> 15) & 0b00011111) as u8
}

#[must_use]
#[inline(always)]
pub const fn get_formal_rs2_bits(src: u32) -> u8 {
    ((src >> 20) & 0b00011111) as u8
}

#[inline(always)]
pub const fn formally_parse_rs1_rs2_rd_props_for_tracer(opcode: u32) -> (u8, u8, u8) {
    let mut rd = get_rd_bits(opcode);
    let formal_rs1 = get_formal_rs1_bits(opcode);
    let formal_rs2 = get_formal_rs2_bits(opcode);
    let op = get_opcode_bits(opcode);

    // we only check for specific families that do not write to RD, such as BRANCH
    if op == OPCODE_BRANCH {
        rd = 0;
    }

    (formal_rs1, formal_rs2, rd)
}

#[must_use]
#[inline(always)]
pub const fn get_bits_and_shift_right(src: u32, from_bit: u32, num_bits: u32, shift: u32) -> u32 {
    let mask = ((1 << num_bits) - 1) << from_bit;
    (src & mask) >> shift
}

#[must_use]
#[inline(always)]
pub const fn get_bits_and_shift_left(src: u32, from_bit: u32, num_bits: u32, shift: u32) -> u32 {
    let mask = ((1 << num_bits) - 1) << from_bit;
    (src & mask) << shift
}

#[must_use]
#[inline(always)]
pub const fn get_bits_and_align_right(src: u32, from_bit: u32, num_bits: u32) -> u32 {
    let mask = ((1 << num_bits) - 1) << from_bit;
    (src & mask) >> from_bit
}

#[inline(always)]
pub const fn sign_extend(dst: &mut u32, total_bits: u32) {
    if *dst & (1 << (total_bits - 1)) != 0 {
        *dst |= !((1 << total_bits) - 1); // put 1s into higher bits
    }
}

#[must_use]
#[inline(always)]
pub const fn b_type_imm_bits(src: u32) -> u32 {
    get_bits_and_shift_right(src, 8, 4, 8 - 1)
        | get_bits_and_shift_right(src, 25, 6, 25 - 5)
        | get_bits_and_shift_left(src, 7, 1, 11 - 7)
        | get_bits_and_shift_right(src, 31, 1, 31 - 12)
}

#[must_use]
#[inline(always)]
pub const fn i_type_imm_bits(src: u32) -> u32 {
    get_bits_and_align_right(src, 20, 12)
}

#[must_use]
#[inline(always)]
pub const fn j_type_imm_bits(src: u32) -> u32 {
    get_bits_and_shift_right(src, 21, 10, 21 - 1)
        | get_bits_and_shift_right(src, 20, 1, 20 - 11)
        | get_bits_and_shift_right(src, 12, 8, 0)
        | get_bits_and_shift_right(src, 31, 1, 31 - 20)
}

#[must_use]
#[inline(always)]
pub const fn s_type_imm_bits(src: u32) -> u32 {
    get_bits_and_align_right(src, 7, 5) | get_bits_and_shift_right(src, 25, 7, 25 - 5)
}

#[must_use]
#[inline(always)]
pub const fn u_type_imm_bits(src: u32) -> u32 {
    get_bits_and_shift_right(src, 12, 20, 0)
}
