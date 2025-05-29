pub const OP_AND_FUNCT3_MASK: u32 = 0x7f | 0x7 << (7 + 5);
pub const OP_AND_FUNCT3_AND_FUNCT7_MASK: u32 = 0x7f | 0x7 << (7 + 5) | 0x7f << (32 - 7);

pub const OP_IMM_SUBMASK: u8 = 0b0010011;
pub const OP_SUBMASK: u8 = 0b0110011;

pub const OPCODE_LUI: u8 = 0b0110111;
pub const OPCODE_AUIPC: u8 = 0b0010111;
pub const OPCODE_JAL: u8 = 0b1101111;
pub const OPCODE_JALR: u8 = 0b1100111;
pub const OPCODE_BRANCH: u8 = 0b1100011;
pub const OPCODE_LOAD: u8 = 0b0000011;
pub const OPCODE_STORE: u8 = 0b0100011;
pub const OPCODE_SYSTEM: u8 = 0b1110011;

pub(crate) const SUB_FUNCT7: u8 = 0b0100000;
pub(crate) const SLL_FUNCT7: u8 = 0;
pub(crate) const SRL_FUNCT7: u8 = 0;
pub(crate) const SRA_FUNCT7: u8 = 0b0100000;
pub(crate) const ROT_FUNCT7: u8 = 0b0110000;
pub(crate) const M_EXT_FUNCT7: u8 = 0b0000001;

pub const ADDI_MASK: u32 = (OP_IMM_SUBMASK as u32) | (0b000 << (7 + 5));
pub const SLLI_MASK: u32 = (OP_IMM_SUBMASK as u32) | (0b001 << (7 + 5));
pub const SRLI_MASK: u32 = (OP_IMM_SUBMASK as u32) | (0b101 << (7 + 5));
pub const SRAI_MASK: u32 = (OP_IMM_SUBMASK as u32) | (0b101 << (7 + 5));

#[must_use]
#[inline(always)]
pub const fn funct3_bits(src: u32) -> u8 {
    use crate::utils::get_bits_and_align_right;
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
