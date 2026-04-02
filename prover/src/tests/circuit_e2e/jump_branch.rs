use super::*;

use cs::machine::ops::unrolled::decoder::JumpSltBranchDecoder;
use cs::machine::ops::unrolled::jump_branch_slt::*;

const FAMILY_IDX: u8 = common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(
        encoding,
        Box::new(JumpSltBranchDecoder::<true>),
        FAMILY_IDX,
        &[],
    )
}

fn check(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    // jump/branch/SLT circuit needs default_pc_value_in_padding=0 because
    // in padding rows all opcode flags are 0, so the PC constraint multiplies
    // by 0 and forces cycle_end_state.pc = 0.
    run_non_mem_circuit_test_with_pc_padding(
        decoder_data,
        jump_branch_slt_table_addition_fn,
        jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
        0, // default_pc_value_in_padding
    );
}

// -- Encoding helpers --
const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const fn encode_i(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

// SLT x3, x1, x2 (signed set-less-than)
const SLT: u32 = encode_r(0b010, 0b0000000, 3, 1, 2);
// SLTU x3, x1, x2 (unsigned set-less-than)
const SLTU: u32 = encode_r(0b011, 0b0000000, 3, 1, 2);
// SLTI x3, x1, 10 (signed set-less-than immediate)
const SLTI_10: u32 = encode_i(0b010, 3, 1, 10);
// SLTIU x3, x1, 10 (unsigned set-less-than immediate)
const SLTIU_10: u32 = encode_i(0b011, 3, 1, 10);

// ==================== SLT ====================

#[test]
fn test_slt_basic() {
    skip_if_ci!();
    let dd = decoder_for(SLT);
    check(&dd, &NonMemTestCase { label: "SLT", rs1: 5, rs2: 10, rd: 1 });
    check(&dd, &NonMemTestCase { label: "SLT", rs1: 10, rs2: 5, rd: 0 });
    check(&dd, &NonMemTestCase { label: "SLT", rs1: 7, rs2: 7, rd: 0 });
}

#[test]
fn test_slt_signed() {
    skip_if_ci!();
    let dd = decoder_for(SLT);
    check(&dd, &NonMemTestCase {
        label: "SLT",
        rs1: (-1i32) as u32, rs2: 0, rd: 1,
    });
    check(&dd, &NonMemTestCase {
        label: "SLT",
        rs1: 0, rs2: (-1i32) as u32, rd: 0,
    });
    check(&dd, &NonMemTestCase {
        label: "SLT",
        rs1: i32::MIN as u32, rs2: i32::MAX as u32, rd: 1,
    });
}

// ==================== SLTU ====================

#[test]
fn test_sltu_basic() {
    skip_if_ci!();
    let dd = decoder_for(SLTU);
    check(&dd, &NonMemTestCase { label: "SLTU", rs1: 5, rs2: 10, rd: 1 });
    check(&dd, &NonMemTestCase { label: "SLTU", rs1: 10, rs2: 5, rd: 0 });
    check(&dd, &NonMemTestCase {
        label: "SLTU",
        rs1: 0, rs2: u32::MAX, rd: 1,
    });
    check(&dd, &NonMemTestCase {
        label: "SLTU",
        rs1: u32::MAX, rs2: 0, rd: 0,
    });
}

// ==================== SLTI ====================

#[test]
fn test_slti() {
    skip_if_ci!();
    let dd = decoder_for(SLTI_10);
    // SLTI: rd = (rs1 < sign_extend(imm)) ? 1 : 0
    check(&dd, &NonMemTestCase { label: "SLTI", rs1: 5, rs2: 0, rd: 1 });
    check(&dd, &NonMemTestCase { label: "SLTI", rs1: 10, rs2: 0, rd: 0 });
    check(&dd, &NonMemTestCase { label: "SLTI", rs1: 15, rs2: 0, rd: 0 });
    check(&dd, &NonMemTestCase {
        label: "SLTI",
        rs1: (-1i32) as u32, rs2: 0, rd: 1,
    });
}

// ==================== SLTIU ====================

#[test]
fn test_sltiu() {
    skip_if_ci!();
    let dd = decoder_for(SLTIU_10);
    check(&dd, &NonMemTestCase { label: "SLTIU", rs1: 5, rs2: 0, rd: 1 });
    check(&dd, &NonMemTestCase { label: "SLTIU", rs1: 10, rs2: 0, rd: 0 });
    check(&dd, &NonMemTestCase { label: "SLTIU", rs1: 15, rs2: 0, rd: 0 });
}
