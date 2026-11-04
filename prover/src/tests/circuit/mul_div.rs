use super::compliance_vectors;
use super::*;

use cs::machine::ops::unrolled::decoder::DivMulDecoder;
use cs::machine::ops::unrolled::mul_div::*;

const FAMILY_IDX: u8 = common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(DivMulDecoder::<true>), FAMILY_IDX, &[])
}

fn decoder_unsigned(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(DivMulDecoder::<false>), FAMILY_IDX, &[])
}

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
    );
}

fn check_unsigned_rd(
    decoder_data: &[ExecutorFamilyDecoderData],
    case: &NonMemTestCase,
    rd_reg: u8,
) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, false>,
        case,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
    );
}

fn run_rr_test<const SIGNED: bool>(
    label: &'static str,
    funct3: u32,
    vectors: &[(u8, u8, u8, u32, u32, u32)],
) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding = encode_r(
            funct3,
            0b0000001,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = if SIGNED {
            decoder_for(encoding)
        } else {
            decoder_unsigned(encoding)
        };
        let case = NonMemTestCase {
            label,
            rs1,
            rs2,
            rd,
        };
        if SIGNED {
            check_rd(&dd, &case, rd_reg);
        } else {
            check_unsigned_rd(&dd, &case, rd_reg);
        }
    }
}

use super::encoding::encode_r;

const MUL_FUNCT3: u32 = 0b000;
const MULH_FUNCT3: u32 = 0b001;
const MULHSU_FUNCT3: u32 = 0b010;
const MULHU_FUNCT3: u32 = 0b011;
const DIV_FUNCT3: u32 = 0b100;
const DIVU_FUNCT3: u32 = 0b101;
const REM_FUNCT3: u32 = 0b110;
const REMU_FUNCT3: u32 = 0b111;

// ==================== Compliance vector tests ====================

#[test]
fn test_mul_compliance() {
    run_rr_test::<true>("MUL", MUL_FUNCT3, compliance_vectors::MUL_VECTORS);
}

#[test]
fn test_mulh_compliance() {
    run_rr_test::<true>("MULH", MULH_FUNCT3, compliance_vectors::MULH_VECTORS);
}

#[test]
fn test_mulhsu_compliance() {
    run_rr_test::<true>("MULHSU", MULHSU_FUNCT3, compliance_vectors::MULHSU_VECTORS);
}

#[test]
fn test_mulhu_compliance() {
    run_rr_test::<true>("MULHU", MULHU_FUNCT3, compliance_vectors::MULHU_VECTORS);
}

#[test]
fn test_div_compliance() {
    run_rr_test::<true>("DIV", DIV_FUNCT3, compliance_vectors::DIV_VECTORS);
}

#[test]
fn test_divu_compliance() {
    run_rr_test::<true>("DIVU", DIVU_FUNCT3, compliance_vectors::DIVU_VECTORS);
}

#[test]
fn test_rem_compliance() {
    run_rr_test::<true>("REM", REM_FUNCT3, compliance_vectors::REM_VECTORS);
}

#[test]
fn test_remu_compliance() {
    run_rr_test::<true>("REMU", REMU_FUNCT3, compliance_vectors::REMU_VECTORS);
}

// ==================== Unsigned-only circuit ====================

#[test]
fn test_divu_unsigned_circuit() {
    run_rr_test::<false>("DIVU", DIVU_FUNCT3, compliance_vectors::DIVU_VECTORS);
}

#[test]
fn test_remu_unsigned_circuit() {
    run_rr_test::<false>("REMU", REMU_FUNCT3, compliance_vectors::REMU_VECTORS);
}
