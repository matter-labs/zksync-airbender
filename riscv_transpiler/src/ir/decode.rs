#[inline(always)]
pub const fn set_bit(dst: &mut u32, bit: u32) {
    *dst |= 1u32 << bit;
}

#[inline(always)]
pub const fn set_bits_to_value(dst: &mut u32, bit_offset: u32, value: u32) {
    *dst |= value << bit_offset;
}

#[inline(always)]
pub const fn clear_bit(dst: &mut u32, bit: u32) {
    *dst &= !(1u32 << bit);
}

#[must_use]
#[inline(always)]
pub const fn test_bit(src: u32, bit: u32) -> bool {
    src & (1u32 << bit) != 0
}

#[must_use]
#[inline(always)]
pub const fn get_bit_right_aligned(src: u32, bit: u32) -> u32 {
    (src >> bit) & 1
}

#[must_use]
#[inline(always)]
pub const fn get_bit_unaligned(src: u32, bit: u32) -> u32 {
    src & (1u32 << bit)
}

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

#[inline(always)]
pub const fn clear_bits(dst: &mut u32, from_bit: u32, num_bits: u32) {
    let mask = ((1 << num_bits) - 1) << from_bit;
    *dst &= !mask;
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
pub const fn sign_extend_16(src: u32) -> u32 {
    let mut value = src & 0x0000ffff;
    sign_extend(&mut value, 16);

    value
}

#[must_use]
#[inline(always)]
pub const fn sign_extend_8(src: u32) -> u32 {
    let mut value = src & 0x000000ff;
    sign_extend(&mut value, 8);

    value
}

#[must_use]
#[inline(always)]
pub const fn zero_extend_16(src: u32) -> u32 {
    src & 0x0000ffff
}

#[must_use]
#[inline(always)]
pub const fn zero_extend_8(src: u32) -> u32 {
    src & 0x000000ff
}

#[must_use]
#[inline(always)]
pub const fn get_formal_rs1(src: u32) -> u32 {
    get_bits_and_align_right(src, 15, 5)
}

#[must_use]
#[inline(always)]
pub const fn get_formal_rs2(src: u32) -> u32 {
    get_bits_and_align_right(src, 20, 5)
}
