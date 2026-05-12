use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Mnemonic {
    // U-type
    Lui,
    Auipc,
    // J-type
    Jal,
    // I-type jumps
    Jalr,
    // B-type branches (funct3-disambiguated)
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
    // I-type loads
    Lb,
    Lh,
    Lw,
    Lbu,
    Lhu,
    // S-type stores
    Sb,
    Sh,
    Sw,
    // I-type arithmetic / shift-immediate
    Addi,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
    Slli,
    Srli,
    Srai,
    Roli,
    Rori,
    // R-type arithmetic / shift / logical
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Rol,
    Ror,
    // M extension
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
    // System / CSR
    Ecall,
    Ebreak,
    Csrrw,
    Csrrs,
    Csrrc,
    Csrrwi,
    Csrrsi,
    Csrrci,
    // Custom MOP extension on OPCODE_SYSTEM funct3=0b100,
    // funct7 ∈ {0b1000001 (ADDMOD), 0b1000011 (SUBMOD), 0b1000101 (MULMOD)}.
    Addmod,
    Submod,
    Mulmod,
    // Fence
    Fence,
    FenceI,
    // Anything else: keep raw bits so the report can show them as-is.
    Unknown {
        opcode: u8,
        funct3: u8,
        funct7: u8,
    },
}

const OPCODE_LUI: u8 = 0b0110111;
const OPCODE_AUIPC: u8 = 0b0010111;
const OPCODE_JAL: u8 = 0b1101111;
const OPCODE_JALR: u8 = 0b1100111;
const OPCODE_BRANCH: u8 = 0b1100011;
const OPCODE_LOAD: u8 = 0b0000011;
const OPCODE_STORE: u8 = 0b0100011;
const OPCODE_OP_IMM: u8 = 0b0010011;
const OPCODE_OP: u8 = 0b0110011;
const OPCODE_SYSTEM: u8 = 0b1110011;
const OPCODE_MISC_MEM: u8 = 0b0001111;

/// Classify a 32-bit instruction word into a `Mnemonic`.
pub fn classify(word: u32) -> Mnemonic {
    let opcode = (word & 0x7f) as u8;
    let funct3 = ((word >> 12) & 0x7) as u8;
    let funct7 = ((word >> 25) & 0x7f) as u8;

    let unknown = Mnemonic::Unknown {
        opcode,
        funct3,
        funct7,
    };

    match opcode {
        OPCODE_LUI => Mnemonic::Lui,
        OPCODE_AUIPC => Mnemonic::Auipc,
        OPCODE_JAL => Mnemonic::Jal,
        OPCODE_JALR => match funct3 {
            0b000 => Mnemonic::Jalr,
            _ => unknown,
        },
        OPCODE_BRANCH => match funct3 {
            0b000 => Mnemonic::Beq,
            0b001 => Mnemonic::Bne,
            0b100 => Mnemonic::Blt,
            0b101 => Mnemonic::Bge,
            0b110 => Mnemonic::Bltu,
            0b111 => Mnemonic::Bgeu,
            _ => unknown,
        },
        OPCODE_LOAD => match funct3 {
            0b000 => Mnemonic::Lb,
            0b001 => Mnemonic::Lh,
            0b010 => Mnemonic::Lw,
            0b100 => Mnemonic::Lbu,
            0b101 => Mnemonic::Lhu,
            _ => unknown,
        },
        OPCODE_STORE => match funct3 {
            0b000 => Mnemonic::Sb,
            0b001 => Mnemonic::Sh,
            0b010 => Mnemonic::Sw,
            _ => unknown,
        },
        OPCODE_OP_IMM => match funct3 {
            0b000 => Mnemonic::Addi,
            0b010 => Mnemonic::Slti,
            0b011 => Mnemonic::Sltiu,
            0b100 => Mnemonic::Xori,
            0b110 => Mnemonic::Ori,
            0b111 => Mnemonic::Andi,
            0b001 => match funct7 {
                0b0000000 => Mnemonic::Slli,
                0b0110000 => Mnemonic::Roli,
                _ => unknown,
            },
            0b101 => match funct7 {
                0b0000000 => Mnemonic::Srli,
                0b0100000 => Mnemonic::Srai,
                0b0110000 => Mnemonic::Rori,
                _ => unknown,
            },
            _ => unknown,
        },
        OPCODE_OP => match (funct3, funct7) {
            (0b000, 0b0000000) => Mnemonic::Add,
            (0b000, 0b0100000) => Mnemonic::Sub,
            (0b000, 0b0000001) => Mnemonic::Mul,
            (0b001, 0b0000000) => Mnemonic::Sll,
            (0b001, 0b0000001) => Mnemonic::Mulh,
            (0b001, 0b0110000) => Mnemonic::Rol,
            (0b010, 0b0000000) => Mnemonic::Slt,
            (0b010, 0b0000001) => Mnemonic::Mulhsu,
            (0b011, 0b0000000) => Mnemonic::Sltu,
            (0b011, 0b0000001) => Mnemonic::Mulhu,
            (0b100, 0b0000000) => Mnemonic::Xor,
            (0b100, 0b0000001) => Mnemonic::Div,
            (0b101, 0b0000000) => Mnemonic::Srl,
            (0b101, 0b0100000) => Mnemonic::Sra,
            (0b101, 0b0000001) => Mnemonic::Divu,
            (0b101, 0b0110000) => Mnemonic::Ror,
            (0b110, 0b0000000) => Mnemonic::Or,
            (0b110, 0b0000001) => Mnemonic::Rem,
            (0b111, 0b0000000) => Mnemonic::And,
            (0b111, 0b0000001) => Mnemonic::Remu,
            _ => unknown,
        },
        OPCODE_SYSTEM => match (funct3, funct7) {
            (0b000, 0b0000000) => {
                // ECALL = imm[11:0] = 0; EBREAK = imm[11:0] = 1.
                let imm = (word >> 20) & 0xfff;
                match imm {
                    0 => Mnemonic::Ecall,
                    1 => Mnemonic::Ebreak,
                    _ => unknown,
                }
            }
            (0b001, _) => Mnemonic::Csrrw,
            (0b010, _) => Mnemonic::Csrrs,
            (0b011, _) => Mnemonic::Csrrc,
            (0b101, _) => Mnemonic::Csrrwi,
            (0b110, _) => Mnemonic::Csrrsi,
            (0b111, _) => Mnemonic::Csrrci,
            // MOP extension: funct3=0b100 with custom funct7 codes.
            (0b100, 0b1000001) => Mnemonic::Addmod,
            (0b100, 0b1000011) => Mnemonic::Submod,
            (0b100, 0b1000101) => Mnemonic::Mulmod,
            _ => unknown,
        },
        OPCODE_MISC_MEM => match funct3 {
            0b000 => Mnemonic::Fence,
            0b001 => Mnemonic::FenceI,
            _ => unknown,
        },
        _ => unknown,
    }
}

/// Histogram a slice of 4-byte-aligned little-endian RISC-V instructions.
///
/// Input must be a multiple of 4 bytes. Trailing bytes are silently ignored
/// (so an objcopy `.text` dump that's not 4-byte aligned still produces
/// output for the aligned prefix).
pub fn histogram(text_bytes: &[u8]) -> BTreeMap<Mnemonic, u64> {
    let mut counts: BTreeMap<Mnemonic, u64> = BTreeMap::new();
    for chunk in text_bytes.chunks_exact(4) {
        let word = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        *counts.entry(classify(word)).or_insert(0) += 1;
    }
    counts
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r_type(opcode: u8, rd: u8, funct3: u8, rs1: u8, rs2: u8, funct7: u8) -> u32 {
        (opcode as u32)
            | ((rd as u32) << 7)
            | ((funct3 as u32) << 12)
            | ((rs1 as u32) << 15)
            | ((rs2 as u32) << 20)
            | ((funct7 as u32) << 25)
    }

    fn i_type(opcode: u8, rd: u8, funct3: u8, rs1: u8, imm: u32) -> u32 {
        (opcode as u32)
            | ((rd as u32) << 7)
            | ((funct3 as u32) << 12)
            | ((rs1 as u32) << 15)
            | ((imm & 0xfff) << 20)
    }

    fn j_type(opcode: u8, rd: u8, imm: u32) -> u32 {
        // Reassemble J-type imm: imm[20|10:1|11|19:12].
        let imm20 = (imm >> 20) & 0x1;
        let imm10_1 = (imm >> 1) & 0x3ff;
        let imm11 = (imm >> 11) & 0x1;
        let imm19_12 = (imm >> 12) & 0xff;
        (opcode as u32)
            | ((rd as u32) << 7)
            | (imm19_12 << 12)
            | (imm11 << 20)
            | (imm10_1 << 21)
            | (imm20 << 31)
    }

    #[test]
    fn histogram_counts_addi_add_lw_jal() {
        let mut bytes: Vec<u8> = Vec::new();
        // addi x1, x0, 5
        bytes.extend(i_type(OPCODE_OP_IMM, 1, 0b000, 0, 5).to_le_bytes());
        // add x3, x1, x2
        bytes.extend(r_type(OPCODE_OP, 3, 0b000, 1, 2, 0b0000000).to_le_bytes());
        // lw x4, 8(x5)
        bytes.extend(i_type(OPCODE_LOAD, 4, 0b010, 5, 8).to_le_bytes());
        // jal x0, 0
        bytes.extend(j_type(OPCODE_JAL, 0, 0).to_le_bytes());

        let h = histogram(&bytes);

        let expected: BTreeMap<Mnemonic, u64> = [
            (Mnemonic::Addi, 1),
            (Mnemonic::Add, 1),
            (Mnemonic::Lw, 1),
            (Mnemonic::Jal, 1),
        ]
        .into_iter()
        .collect();

        assert_eq!(h, expected, "got {:?}", h);
    }
}
