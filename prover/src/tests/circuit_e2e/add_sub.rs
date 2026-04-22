use super::*;
use super::compliance_vectors;

use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
use cs::machine::ops::unrolled::decoder::AddSubLuiAuipcMopDecoder;

const FAMILY_IDX: u8 = common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(AddSubLuiAuipcMopDecoder), FAMILY_IDX, &[])
}


fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        add_sub_lui_auipc_mop_table_addition_fn,
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode,
        case,
    );
    assert_eq!(
        circuit_regs[3], case.rd,
        "{}: circuit wrote {:#010X} to x3 but expected {:#010X}",
        case.label, circuit_regs[3], case.rd
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

const ADD: u32 = encode_r(0b000, 0b0000000, 3, 1, 2);

#[test]
fn test_add_compliance() {
    skip_if_ci!();
    let dd = decoder_for(ADD);
    for &(rs1, rs2, rd) in compliance_vectors::ADD_VECTORS {
        check_rd(&dd, &NonMemTestCase {
            label: "ADD",
            rs1,
            rs2,
            rd,
        });
    }
}

// ==================== SUB (compliance) ====================

const SUB: u32 = encode_r(0b000, 0b0100000, 3, 1, 2);

#[test]
fn test_sub_compliance() {
    skip_if_ci!();
    let dd = decoder_for(SUB);
    for &(rs1, rs2, rd) in compliance_vectors::SUB_VECTORS {
        check_rd(&dd, &NonMemTestCase {
            label: "SUB",
            rs1,
            rs2,
            rd,
        });
    }
}

// ==================== ADDI (compliance) ====================

#[test]
fn test_addi_compliance() {
    skip_if_ci!();
    for &(rs1, imm, rd) in compliance_vectors::ADDI_VECTORS {
        let encoding = encode_i(0b000, 3, 1, imm & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase {
            label: "ADDI",
            rs1,
            rs2: 0,
            rd,
        });
    }
}

// ==================== LUI (compliance) ====================

#[test]
fn test_lui_compliance() {
    skip_if_ci!();
    for &(imm_upper, rd) in compliance_vectors::LUI_VECTORS {
        let encoding = encode_u(0x37, 3, imm_upper & 0xFFFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase {
            label: "LUI",
            rs1: 0,
            rs2: 0,
            rd,
        });
    }
}

// ==================== AUIPC (compliance) ====================

#[test]
fn test_auipc_compliance() {
    skip_if_ci!();
    for &(imm_upper, rd) in compliance_vectors::AUIPC_VECTORS {
        let encoding = encode_u(0x17, 3, imm_upper & 0xFFFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase {
            label: "AUIPC",
            rs1: 0,
            rs2: 0,
            rd,
        });
    }
}

// ==================== MOP (Mersenne field ops, p = 2^31 - 1) ====================

// R-type encoding with OPERATION_SYSTEM opcode (0x73)
const fn encode_r_system(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x73
}

// ADDMOD x3, x1, x2  (funct3=0b100, funct7=0b1000001)
const ADDMOD: u32 = encode_r_system(0b100, 0b1000001, 3, 1, 2);
// SUBMOD x3, x1, x2  (funct3=0b100, funct7=0b1000011)
const SUBMOD: u32 = encode_r_system(0b100, 0b1000011, 3, 1, 2);
// MULMOD x3, x1, x2  (funct3=0b100, funct7=0b1000101)
const MULMOD: u32 = encode_r_system(0b100, 0b1000101, 3, 1, 2);

#[test]
fn test_addmod_compliance() {
    skip_if_ci!();
    let dd = decoder_for(ADDMOD);
    for &(rs1, rs2, rd) in compliance_vectors::ADDMOD_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "ADDMOD", rs1, rs2, rd });
    }
}

#[test]
fn test_submod_compliance() {
    skip_if_ci!();
    let dd = decoder_for(SUBMOD);
    for &(rs1, rs2, rd) in compliance_vectors::SUBMOD_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "SUBMOD", rs1, rs2, rd });
    }
}

#[test]
fn test_mulmod_compliance() {
    skip_if_ci!();
    let dd = decoder_for(MULMOD);
    for &(rs1, rs2, rd) in compliance_vectors::MULMOD_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "MULMOD", rs1, rs2, rd });
    }
}
