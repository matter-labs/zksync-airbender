use super::*;

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

const SLL: u32 = encode_r(0b001, 0b0000000, 3, 1, 2);
const SRL: u32 = encode_r(0b101, 0b0000000, 3, 1, 2);
const SRA: u32 = encode_r(0b101, 0b0100000, 3, 1, 2);
const XOR: u32 = encode_r(0b100, 0b0000000, 3, 1, 2);
const AND: u32 = encode_r(0b111, 0b0000000, 3, 1, 2);
const OR: u32 = encode_r(0b110, 0b0000000, 3, 1, 2);
const SLLI_4: u32 = encode_i_shift(0b001, 0b0000000, 3, 1, 4);
const SRLI_4: u32 = encode_i_shift(0b101, 0b0000000, 3, 1, 4);
const SRAI_4: u32 = encode_i_shift(0b101, 0b0100000, 3, 1, 4);
const XORI: u32 = encode_i(0b100, 3, 1, 0xFF);
const ANDI: u32 = encode_i(0b111, 3, 1, 0xFF);
const ORI: u32 = encode_i(0b110, 3, 1, 0xFF);

// ==================== SLL ====================

#[test]
fn test_sll() {
    skip_if_ci!();
    let dd = decoder_for(SLL);
    check(&dd, &NonMemTestCase { label: "SLL", rs1: 1, rs2: 4, rd: 16 });
    check(&dd, &NonMemTestCase { label: "SLL", rs1: 0xFF, rs2: 8, rd: 0xFF00 });
    check(&dd, &NonMemTestCase { label: "SLL", rs1: 42, rs2: 0, rd: 42 });
}

// ==================== SRL ====================

#[test]
fn test_srl() {
    skip_if_ci!();
    let dd = decoder_for(SRL);
    check(&dd, &NonMemTestCase { label: "SRL", rs1: 256, rs2: 4, rd: 16 });
    check(&dd, &NonMemTestCase {
        label: "SRL",
        rs1: 0x80000000, rs2: 1, rd: 0x40000000,
    });
}

// ==================== SRA ====================

#[test]
fn test_sra() {
    skip_if_ci!();
    let dd = decoder_for(SRA);
    check(&dd, &NonMemTestCase {
        label: "SRA",
        rs1: (-16i32) as u32, rs2: 2, rd: (-4i32) as u32,
    });
    check(&dd, &NonMemTestCase { label: "SRA", rs1: 16, rs2: 2, rd: 4 });
}

// ==================== XOR ====================

#[test]
fn test_xor() {
    skip_if_ci!();
    let dd = decoder_for(XOR);
    check(&dd, &NonMemTestCase { label: "XOR", rs1: 0xFF, rs2: 0x0F, rd: 0xF0 });
    check(&dd, &NonMemTestCase { label: "XOR", rs1: 42, rs2: 42, rd: 0 });
}

// ==================== AND ====================

#[test]
fn test_and() {
    skip_if_ci!();
    let dd = decoder_for(AND);
    check(&dd, &NonMemTestCase { label: "AND", rs1: 0xFF, rs2: 0x0F, rd: 0x0F });
}

// ==================== OR ====================

#[test]
fn test_or() {
    skip_if_ci!();
    let dd = decoder_for(OR);
    check(&dd, &NonMemTestCase { label: "OR", rs1: 0xF0, rs2: 0x0F, rd: 0xFF });
}

// ==================== Immediate variants ====================

#[test]
fn test_slli() {
    skip_if_ci!();
    let dd = decoder_for(SLLI_4);
    check(&dd, &NonMemTestCase { label: "SLLI", rs1: 1, rs2: 0, rd: 16 });
}

#[test]
fn test_srli() {
    skip_if_ci!();
    let dd = decoder_for(SRLI_4);
    check(&dd, &NonMemTestCase { label: "SRLI", rs1: 256, rs2: 0, rd: 16 });
}

#[test]
fn test_srai() {
    skip_if_ci!();
    let dd = decoder_for(SRAI_4);
    check(&dd, &NonMemTestCase {
        label: "SRAI",
        rs1: (-256i32) as u32, rs2: 0, rd: (-16i32) as u32,
    });
}

#[test]
fn test_xori() {
    skip_if_ci!();
    let dd = decoder_for(XORI);
    check(&dd, &NonMemTestCase { label: "XORI", rs1: 0xFF00, rs2: 0, rd: 0xFF00 ^ 0xFF });
}

#[test]
fn test_andi() {
    skip_if_ci!();
    let dd = decoder_for(ANDI);
    // ANDI: imm is sign-extended from 12 bits. 0xFF = 255, sign-extended = 0x000000FF
    check(&dd, &NonMemTestCase { label: "ANDI", rs1: 0xABCD, rs2: 0, rd: 0xCD });
}

#[test]
fn test_ori() {
    skip_if_ci!();
    let dd = decoder_for(ORI);
    check(&dd, &NonMemTestCase { label: "ORI", rs1: 0xAB00, rs2: 0, rd: 0xABFF });
}
