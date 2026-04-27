use super::*;
use super::compliance_vectors;

use cs::machine::ops::unrolled::decoder::ShiftBinaryCsrrwDecoder;
use cs::machine::ops::unrolled::shift_binary_csr::*;

const FAMILY_IDX: u8 = common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(ShiftBinaryCsrrwDecoder), FAMILY_IDX, &[])
}

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        shift_binop_csrrw_table_addition_fn,
        shift_binop_csrrw_circuit_with_preprocessed_bytecode,
        case,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
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

fn run_rr_test(
    label: &'static str,
    funct3: u32,
    funct7: u32,
    vectors: &[(u8, u8, u8, u32, u32, u32)],
) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding = encode_r(funct3, funct7, rd_reg as u32, rs1_reg as u32, rs2_reg as u32);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label, rs1, rs2, rd }, rd_reg);
    }
}

fn run_ishift_test(
    label: &'static str,
    funct3: u32,
    funct7: u32,
    vectors: &[(u8, u8, u8, u32, u32)],
) {
    for &(rd_reg, rs1_reg, shamt, rs1, rd) in vectors {
        let encoding = encode_i_shift(
            funct3,
            funct7,
            rd_reg as u32,
            rs1_reg as u32,
            (shamt as u32) & 0x1F,
        );
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label, rs1, rs2: 0, rd }, rd_reg);
    }
}

fn run_ilog_test(
    label: &'static str,
    funct3: u32,
    vectors: &[(u8, u8, u16, u32, u32)],
) {
    for &(rd_reg, rs1_reg, imm, rs1, rd) in vectors {
        let encoding = encode_i(funct3, rd_reg as u32, rs1_reg as u32, (imm as u32) & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label, rs1, rs2: 0, rd }, rd_reg);
    }
}

#[test]
fn test_sll() {
    skip_if_ci!();
    run_rr_test("SLL", 0b001, 0b0000000, compliance_vectors::SLL_VECTORS);
}

#[test]
fn test_srl() {
    skip_if_ci!();
    run_rr_test("SRL", 0b101, 0b0000000, compliance_vectors::SRL_VECTORS);
}

#[test]
fn test_sra() {
    skip_if_ci!();
    run_rr_test("SRA", 0b101, 0b0100000, compliance_vectors::SRA_VECTORS);
}

#[test]
fn test_xor() {
    skip_if_ci!();
    run_rr_test("XOR", 0b100, 0b0000000, compliance_vectors::XOR_VECTORS);
}

#[test]
fn test_and() {
    skip_if_ci!();
    run_rr_test("AND", 0b111, 0b0000000, compliance_vectors::AND_VECTORS);
}

#[test]
fn test_or() {
    skip_if_ci!();
    run_rr_test("OR", 0b110, 0b0000000, compliance_vectors::OR_VECTORS);
}

#[test]
fn test_slli() {
    skip_if_ci!();
    run_ishift_test("SLLI", 0b001, 0b0000000, compliance_vectors::SLLI_VECTORS);
}

#[test]
fn test_srli() {
    skip_if_ci!();
    run_ishift_test("SRLI", 0b101, 0b0000000, compliance_vectors::SRLI_VECTORS);
}

#[test]
fn test_srai() {
    skip_if_ci!();
    run_ishift_test("SRAI", 0b101, 0b0100000, compliance_vectors::SRAI_VECTORS);
}

#[test]
fn test_xori() {
    skip_if_ci!();
    run_ilog_test("XORI", 0b100, compliance_vectors::XORI_VECTORS);
}

#[test]
fn test_andi() {
    skip_if_ci!();
    run_ilog_test("ANDI", 0b111, compliance_vectors::ANDI_VECTORS);
}

#[test]
fn test_ori() {
    skip_if_ci!();
    run_ilog_test("ORI", 0b110, compliance_vectors::ORI_VECTORS);
}
