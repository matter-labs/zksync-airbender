use super::*;
use super::compliance_vectors;

use cs::machine::ops::unrolled::decoder::ShiftBinaryCsrrwDecoder;
use cs::machine::ops::unrolled::shift_binary_csr::*;

const FAMILY_IDX: u8 = common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(ShiftBinaryCsrrwDecoder), FAMILY_IDX, &[])
}

fn check(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    run_non_mem_circuit_test(
        decoder_data,
        shift_binop_csrrw_table_addition_fn,
        shift_binop_csrrw_circuit_with_preprocessed_bytecode,
        case,
    );
}

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        shift_binop_csrrw_table_addition_fn,
        shift_binop_csrrw_circuit_with_preprocessed_bytecode,
        case,
    );
    assert_eq!(
        circuit_regs[3], case.rd,
        "{}: circuit wrote {:#010X} to x3 but expected {:#010X}",
        case.label, circuit_regs[3], case.rd
    );
}

// -- Encoding helpers --
const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const fn encode_i_shift(funct3: u32, funct7: u32, rd: u32, rs1: u32, shamt: u32) -> u32 {
    (funct7 << 25) | (shamt << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

const fn encode_i(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

// ==================== R-type: SLL ====================

const SLL: u32 = encode_r(0b001, 0b0000000, 3, 1, 2);

#[test]
fn test_sll() {
    skip_if_ci!();
    let dd = decoder_for(SLL);
    for &(rs1, rs2, rd) in compliance_vectors::SLL_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "SLL", rs1, rs2, rd });
    }
}

// ==================== R-type: SRL ====================

const SRL: u32 = encode_r(0b101, 0b0000000, 3, 1, 2);

#[test]
fn test_srl() {
    skip_if_ci!();
    let dd = decoder_for(SRL);
    for &(rs1, rs2, rd) in compliance_vectors::SRL_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "SRL", rs1, rs2, rd });
    }
}

// ==================== R-type: SRA ====================

const SRA: u32 = encode_r(0b101, 0b0100000, 3, 1, 2);

#[test]
fn test_sra() {
    skip_if_ci!();
    let dd = decoder_for(SRA);
    for &(rs1, rs2, rd) in compliance_vectors::SRA_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "SRA", rs1, rs2, rd });
    }
}

// ==================== R-type: XOR ====================

const XOR: u32 = encode_r(0b100, 0b0000000, 3, 1, 2);

#[test]
fn test_xor() {
    skip_if_ci!();
    let dd = decoder_for(XOR);
    for &(rs1, rs2, rd) in compliance_vectors::XOR_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "XOR", rs1, rs2, rd });
    }
}

// ==================== R-type: AND ====================

const AND: u32 = encode_r(0b111, 0b0000000, 3, 1, 2);

#[test]
fn test_and() {
    skip_if_ci!();
    let dd = decoder_for(AND);
    for &(rs1, rs2, rd) in compliance_vectors::AND_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "AND", rs1, rs2, rd });
    }
}

// ==================== R-type: OR ====================

const OR: u32 = encode_r(0b110, 0b0000000, 3, 1, 2);

#[test]
fn test_or() {
    skip_if_ci!();
    let dd = decoder_for(OR);
    for &(rs1, rs2, rd) in compliance_vectors::OR_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "OR", rs1, rs2, rd });
    }
}

// ==================== I-type shift: SLLI ====================

#[test]
fn test_slli() {
    skip_if_ci!();
    for &(rs1, shamt, rd) in compliance_vectors::SLLI_VECTORS {
        let encoding = encode_i_shift(0b001, 0b0000000, 3, 1, shamt & 0x1F);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label: "SLLI", rs1, rs2: 0, rd });
    }
}

// ==================== I-type shift: SRLI ====================

#[test]
fn test_srli() {
    skip_if_ci!();
    for &(rs1, shamt, rd) in compliance_vectors::SRLI_VECTORS {
        let encoding = encode_i_shift(0b101, 0b0000000, 3, 1, shamt & 0x1F);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label: "SRLI", rs1, rs2: 0, rd });
    }
}

// ==================== I-type shift: SRAI ====================

#[test]
fn test_srai() {
    skip_if_ci!();
    for &(rs1, shamt, rd) in compliance_vectors::SRAI_VECTORS {
        let encoding = encode_i_shift(0b101, 0b0100000, 3, 1, shamt & 0x1F);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label: "SRAI", rs1, rs2: 0, rd });
    }
}

// ==================== I-type logic: XORI ====================

#[test]
fn test_xori() {
    skip_if_ci!();
    for &(rs1, imm, rd) in compliance_vectors::XORI_VECTORS {
        let encoding = encode_i(0b100, 3, 1, imm & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label: "XORI", rs1, rs2: 0, rd });
    }
}

// ==================== I-type logic: ANDI ====================

#[test]
fn test_andi() {
    skip_if_ci!();
    for &(rs1, imm, rd) in compliance_vectors::ANDI_VECTORS {
        let encoding = encode_i(0b111, 3, 1, imm & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label: "ANDI", rs1, rs2: 0, rd });
    }
}

// ==================== I-type logic: ORI ====================

#[test]
fn test_ori() {
    skip_if_ci!();
    for &(rs1, imm, rd) in compliance_vectors::ORI_VECTORS {
        let encoding = encode_i(0b110, 3, 1, imm & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label: "ORI", rs1, rs2: 0, rd });
    }
}
