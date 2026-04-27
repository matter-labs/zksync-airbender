use super::*;
use super::compliance_vectors;

use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
use cs::machine::ops::unrolled::decoder::AddSubLuiAuipcMopDecoder;

const FAMILY_IDX: u8 = common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(AddSubLuiAuipcMopDecoder), FAMILY_IDX, &[])
}


fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        add_sub_lui_auipc_mop_table_addition_fn,
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode,
        case,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
    );
}

const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const fn encode_i(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

const fn encode_u(opcode: u32, rd: u32, imm_upper: u32) -> u32 {
    (imm_upper << 12) | (rd << 7) | opcode
}

// ==================== ADD  ====================

#[test]
fn test_add_compliance() {
    skip_if_ci!();
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in compliance_vectors::ADD_VECTORS {
        let encoding = encode_r(
            0b000,
            0b0000000,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase { label: "ADD", rs1, rs2, rd },
            rd_reg,
        );
    }
}

// ==================== SUB (compliance) ====================

#[test]
fn test_sub_compliance() {
    skip_if_ci!();
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in compliance_vectors::SUB_VECTORS {
        let encoding = encode_r(
            0b000,
            0b0100000,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase { label: "SUB", rs1, rs2, rd },
            rd_reg,
        );
    }
}

// ==================== ADDI (compliance) ====================

#[test]
fn test_addi_compliance() {
    skip_if_ci!();
    for &(rd_reg, rs1_reg, imm, rs1, rd) in compliance_vectors::ADDI_VECTORS {
        let encoding = encode_i(0b000, rd_reg as u32, rs1_reg as u32, imm as u32 & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase { label: "ADDI", rs1, rs2: 0, rd },
            rd_reg,
        );
    }
}

// ==================== LUI (compliance) ====================

#[test]
fn test_lui_compliance() {
    skip_if_ci!();
    for &(rd_reg, imm_upper, rd) in compliance_vectors::LUI_VECTORS {
        let encoding = encode_u(0x37, rd_reg as u32, imm_upper & 0xFFFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase { label: "LUI", rs1: 0, rs2: 0, rd },
            rd_reg,
        );
    }
}

// ==================== AUIPC (compliance) ====================

#[test]
fn test_auipc_compliance() {
    skip_if_ci!();
    for &(rd_reg, imm_upper, rd) in compliance_vectors::AUIPC_VECTORS {
        let encoding = encode_u(0x17, rd_reg as u32, imm_upper & 0xFFFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase { label: "AUIPC", rs1: 0, rs2: 0, rd },
            rd_reg,
        );
    }
}

// ==================== MOP (Mersenne field ops, p = 2^31 - 1) ====================

// R-type encoding with OPERATION_SYSTEM opcode (0x73)
const fn encode_r_system(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x73
}

fn run_mop_test(label: &'static str, funct7: u32, vectors: &[(u8, u8, u8, u32, u32, u32)]) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding = encode_r_system(
            0b100,
            funct7,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase { label, rs1, rs2, rd },
            rd_reg,
        );
    }
}

#[test]
fn test_addmod_compliance() {
    skip_if_ci!();
    run_mop_test("ADDMOD", 0b1000001, compliance_vectors::ADDMOD_VECTORS);
}

#[test]
fn test_submod_compliance() {
    skip_if_ci!();
    run_mop_test("SUBMOD", 0b1000011, compliance_vectors::SUBMOD_VECTORS);
}

#[test]
fn test_mulmod_compliance() {
    skip_if_ci!();
    run_mop_test("MULMOD", 0b1000101, compliance_vectors::MULMOD_VECTORS);
}
