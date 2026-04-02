use super::*;

use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
use cs::machine::ops::unrolled::decoder::AddSubLuiAuipcMopDecoder;

const FAMILY_IDX: u8 = common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(AddSubLuiAuipcMopDecoder), FAMILY_IDX, &[])
}

fn check(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    run_non_mem_circuit_test(
        decoder_data,
        add_sub_lui_auipc_mop_table_addition_fn,
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode,
        case,
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

const ADD: u32 = encode_r(0b000, 0b0000000, 3, 1, 2);
const SUB: u32 = encode_r(0b000, 0b0100000, 3, 1, 2);
// ADDI x3, x1, 10
const ADDI_10: u32 = encode_i(0b000, 3, 1, 10);
// LUI x3, 0x12345
const LUI: u32 = encode_u(0x37, 3, 0x12345);

// ==================== ADD ====================

#[test]
fn test_add_basic() {
    skip_if_ci!();
    let dd = decoder_for(ADD);
    check(&dd, &NonMemTestCase { label: "ADD", rs1: 10, rs2: 20, rd: 30 });
    check(&dd, &NonMemTestCase { label: "ADD", rs1: 0, rs2: 0, rd: 0 });
    check(&dd, &NonMemTestCase {
        label: "ADD",
        rs1: u32::MAX, rs2: 1, rd: 0,
    });
}

#[test]
fn test_add_signed() {
    skip_if_ci!();
    let dd = decoder_for(ADD);
    check(&dd, &NonMemTestCase {
        label: "ADD",
        rs1: u32::MAX, rs2: 1, rd: 0,
    });
    check(&dd, &NonMemTestCase {
        label: "ADD",
        rs1: u32::MAX, rs2: u32::MAX, rd: u32::MAX - 1,
    });
}

// ==================== SUB ====================

#[test]
fn test_sub_basic() {
    skip_if_ci!();
    let dd = decoder_for(SUB);
    check(&dd, &NonMemTestCase { label: "SUB", rs1: 30, rs2: 20, rd: 10 });
    check(&dd, &NonMemTestCase {
        label: "SUB",
        rs1: 0, rs2: 1, rd: u32::MAX,
    });
}

// ==================== ADDI ====================

#[test]
fn test_addi() {
    skip_if_ci!();
    let dd = decoder_for(ADDI_10);
    // For I-type, rs2 is not used by the circuit for the operation,
    // but the oracle still needs it. The immediate comes from the decoder.
    check(&dd, &NonMemTestCase { label: "ADDI", rs1: 5, rs2: 0, rd: 15 });
    check(&dd, &NonMemTestCase { label: "ADDI", rs1: 0, rs2: 0, rd: 10 });
}

// ==================== LUI ====================

#[test]
fn test_lui() {
    skip_if_ci!();
    let dd = decoder_for(LUI);
    // LUI loads upper 20 bits: rd = imm << 12
    check(&dd, &NonMemTestCase {
        label: "LUI",
        rs1: 0, rs2: 0, rd: 0x12345000,
    });
}

// ==================== AUIPC ====================

// AUIPC x3, 0x12345 -> rd = PC + (imm << 12). With initial_pc=0, rd = 0x12345000.
const AUIPC: u32 = encode_u(0x17, 3, 0x12345);

#[test]
fn test_auipc() {
    skip_if_ci!();
    let dd = decoder_for(AUIPC);
    // AUIPC adds upper immediate to PC. With PC=0, result is just imm << 12.
    check(&dd, &NonMemTestCase {
        label: "AUIPC",
        rs1: 0, rs2: 0, rd: 0x12345000,
    });
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
fn test_addmod() {
    skip_if_ci!();
    let dd = decoder_for(ADDMOD);
    // ADDMOD: (10 + 20) mod (2^31 - 1) = 30
    check(&dd, &NonMemTestCase {
        label: "ADDMOD",
        rs1: 10, rs2: 20, rd: 30,
    });
}

#[test]
fn test_submod() {
    skip_if_ci!();
    let dd = decoder_for(SUBMOD);
    // SUBMOD: (30 - 20) mod (2^31 - 1) = 10
    check(&dd, &NonMemTestCase {
        label: "SUBMOD",
        rs1: 30, rs2: 20, rd: 10,
    });
}

// NOTE: MULMOD requires degree-2 witness resolution (quadratic constraint from
// field multiplication) which the BasicAssembly debug evaluator cannot solve.
// MULMOD is tested via the full witness evaluator path in the prover pipeline.
// #[test]
// fn test_mulmod() { ... }
