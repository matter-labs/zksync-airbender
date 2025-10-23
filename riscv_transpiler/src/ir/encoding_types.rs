use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UTypeOpcode;

impl UTypeOpcode {
    #[must_use]
    #[inline(always)]
    pub const fn imm(src: u32) -> u32 {
        get_bits_and_shift_right(src, 12, 20, 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JTypeOpcode;

impl JTypeOpcode {
    #[must_use]
    #[inline(always)]
    pub const fn imm(src: u32) -> u32 {
        get_bits_and_shift_right(src, 21, 10, 21 - 1)
            | get_bits_and_shift_right(src, 20, 1, 20 - 11)
            | get_bits_and_shift_right(src, 12, 8, 0)
            | get_bits_and_shift_right(src, 31, 1, 31 - 20)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BTypeOpcode;

impl BTypeOpcode {
    #[must_use]
    #[inline(always)]
    pub const fn rs1(src: u32) -> u32 {
        get_bits_and_align_right(src, 15, 5)
    }

    #[must_use]
    #[inline(always)]
    pub const fn rs2(src: u32) -> u32 {
        get_bits_and_align_right(src, 20, 5)
    }

    #[must_use]
    #[inline(always)]
    pub const fn funct3(src: u32) -> u32 {
        get_bits_and_align_right(src, 12, 3)
    }

    #[must_use]
    #[inline(always)]
    pub const fn imm(src: u32) -> u32 {
        get_bits_and_shift_right(src, 8, 4, 8 - 1)
            | get_bits_and_shift_right(src, 25, 6, 25 - 5)
            | get_bits_and_shift_left(src, 7, 1, 11 - 7)
            | get_bits_and_shift_right(src, 31, 1, 31 - 12)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ITypeOpcode;

impl ITypeOpcode {
    #[must_use]
    #[inline(always)]
    pub const fn rs1(src: u32) -> u32 {
        get_bits_and_align_right(src, 15, 5)
    }

    #[must_use]
    #[inline(always)]
    pub const fn funct3(src: u32) -> u32 {
        get_bits_and_align_right(src, 12, 3)
    }

    #[must_use]
    #[inline(always)]
    pub const fn imm(src: u32) -> u32 {
        get_bits_and_align_right(src, 20, 12)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct STypeOpcode;

impl STypeOpcode {
    #[must_use]
    #[inline(always)]
    pub const fn rs1(src: u32) -> u32 {
        get_bits_and_align_right(src, 15, 5)
    }

    #[must_use]
    #[inline(always)]
    pub const fn rs2(src: u32) -> u32 {
        get_bits_and_align_right(src, 20, 5)
    }

    #[must_use]
    #[inline(always)]
    pub const fn funct3(src: u32) -> u32 {
        get_bits_and_align_right(src, 12, 3)
    }

    #[must_use]
    #[inline(always)]
    pub const fn imm(src: u32) -> u32 {
        get_bits_and_align_right(src, 7, 5) | get_bits_and_shift_right(src, 25, 7, 25 - 5)
    }
}
