// R-type: funct7 | rs2 | rs1 | funct3 | rd | 0110011
pub const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

// R-type with SYSTEM opcode 0x73 — used for the Mersenne MOP family
// (ADDMOD/SUBMOD/MULMOD).
pub const fn encode_r_system(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x73
}

// I-type (ALU/immediate, opcode 0x13): imm[11:0] | rs1 | funct3 | rd | 0010011
pub const fn encode_i(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

// I-type immediate-shift: funct7 occupies the high 7 bits of imm[11:5].
pub const fn encode_i_shift(funct3: u32, funct7: u32, rd: u32, rs1: u32, shamt: u32) -> u32 {
    (funct7 << 25) | (shamt << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

// U-type: imm[31:12] | rd | opcode (LUI = 0x37, AUIPC = 0x17).
pub const fn encode_u(opcode: u32, rd: u32, imm_upper: u32) -> u32 {
    (imm_upper << 12) | (rd << 7) | opcode
}

// B-type: imm[12|10:5] | rs2 | rs1 | funct3 | imm[4:1|11] | 1100011
pub const fn encode_b(funct3: u32, rs1: u32, rs2: u32, imm: u32) -> u32 {
    let imm_12 = (imm >> 12) & 1;
    let imm_10_5 = (imm >> 5) & 0x3F;
    let imm_4_1 = (imm >> 1) & 0xF;
    let imm_11 = (imm >> 11) & 1;
    (imm_12 << 31)
        | (imm_10_5 << 25)
        | (rs2 << 20)
        | (rs1 << 15)
        | (funct3 << 12)
        | (imm_4_1 << 8)
        | (imm_11 << 7)
        | 0x63
}

// J-type (JAL): imm[20|10:1|11|19:12] | rd | 1101111
pub const fn encode_j(rd: u32, imm: u32) -> u32 {
    let imm_20 = (imm >> 20) & 0x1;
    let imm_10_1 = (imm >> 1) & 0x3FF;
    let imm_11 = (imm >> 11) & 0x1;
    let imm_19_12 = (imm >> 12) & 0xFF;
    (imm_20 << 31) | (imm_10_1 << 21) | (imm_11 << 20) | (imm_19_12 << 12) | (rd << 7) | 0x6F
}

// I-type JALR: imm[11:0] | rs1 | 000 | rd | 1100111
pub const fn encode_jalr(rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (rd << 7) | 0x67
}

// CSRRW (I-type for CSR): csr[11:0] | rs1 | funct3=001 | rd | 1110011
pub const fn encode_csrrw(rd: u32, rs1: u32, csr: u32) -> u32 {
    ((csr & 0xFFF) << 20) | (rs1 << 15) | (0b001 << 12) | (rd << 7) | 0x73
}

// I-type LOAD (opcode 0x03): imm[11:0] | rs1 | funct3 | rd | 0000011
pub const fn encode_load(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x03
}

// S-type STORE (opcode 0x23): imm[11:5] | rs2 | rs1 | funct3 | imm[4:0] | 0100011
pub const fn encode_store(funct3: u32, rs1: u32, rs2: u32, imm: u32) -> u32 {
    let imm_11_5 = (imm >> 5) & 0x7F;
    let imm_4_0 = imm & 0x1F;
    (imm_11_5 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm_4_0 << 7) | 0x23
}
