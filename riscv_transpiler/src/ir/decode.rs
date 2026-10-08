#[inline(always)]
pub const fn sign_extend(dst: &mut u32, total_bits: u32) {
    if *dst & (1 << (total_bits - 1)) != 0 {
        *dst |= !((1 << total_bits) - 1); // put 1s into higher bits
    }
}

#[must_use]
#[inline(always)]
pub const fn get_bits_and_align_right(src: u32, from_bit: u32, num_bits: u32) -> u32 {
    let mask = ((1 << num_bits) - 1) << from_bit;
    (src & mask) >> from_bit
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
