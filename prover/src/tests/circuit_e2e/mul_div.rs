use super::*;
use super::compliance_vectors;

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

fn check_unsigned_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
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
        let encoding = encode_r(funct3, 0b0000001, rd_reg as u32, rs1_reg as u32, rs2_reg as u32);
        let dd = if SIGNED {
            decoder_for(encoding)
        } else {
            decoder_unsigned(encoding)
        };
        let case = NonMemTestCase { label, rs1, rs2, rd };
        if SIGNED {
            check_rd(&dd, &case, rd_reg);
        } else {
            check_unsigned_rd(&dd, &case, rd_reg);
        }
    }
}

// -- RISC-V R-type encoding helpers --
// opcode=0x33, funct7=0x01 (M extension)
const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const MUL_FUNCT3: u32 = 0b000;
const MULH_FUNCT3: u32 = 0b001;
const MULHSU_FUNCT3: u32 = 0b010;
const MULHU_FUNCT3: u32 = 0b011;
const DIV_FUNCT3: u32 = 0b100;
const DIVU_FUNCT3: u32 = 0b101;
const REM_FUNCT3: u32 = 0b110;
const REMU_FUNCT3: u32 = 0b111;

// Kept for the heavy prover tests below.
const DIV_ENCODING: u32 = (0b0000001 << 25) | (2 << 20) | (1 << 15) | (DIV_FUNCT3 << 12) | (3 << 7) | 0x33;
const MUL_ENCODING: u32 = (0b0000001 << 25) | (2 << 20) | (1 << 15) | (MUL_FUNCT3 << 12) | (3 << 7) | 0x33;

// ==================== Compliance vector tests ====================

#[test]
fn test_mul_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("MUL", MUL_FUNCT3, compliance_vectors::MUL_VECTORS);
}

#[test]
fn test_mulh_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("MULH", MULH_FUNCT3, compliance_vectors::MULH_VECTORS);
}

#[test]
fn test_mulhsu_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("MULHSU", MULHSU_FUNCT3, compliance_vectors::MULHSU_VECTORS);
}

#[test]
fn test_mulhu_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("MULHU", MULHU_FUNCT3, compliance_vectors::MULHU_VECTORS);
}

#[test]
fn test_div_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("DIV", DIV_FUNCT3, compliance_vectors::DIV_VECTORS);
}

#[test]
fn test_divu_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("DIVU", DIVU_FUNCT3, compliance_vectors::DIVU_VECTORS);
}

#[test]
fn test_rem_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("REM", REM_FUNCT3, compliance_vectors::REM_VECTORS);
}

#[test]
fn test_remu_compliance() {
    skip_if_ci!();
    run_rr_test::<true>("REMU", REMU_FUNCT3, compliance_vectors::REMU_VECTORS);
}

// ==================== Unsigned-only circuit ====================

#[test]
fn test_divu_unsigned_circuit() {
    skip_if_ci!();
    run_rr_test::<false>("DIVU", DIVU_FUNCT3, compliance_vectors::DIVU_VECTORS);
}

#[test]
fn test_remu_unsigned_circuit() {
    skip_if_ci!();
    run_rr_test::<false>("REMU", REMU_FUNCT3, compliance_vectors::REMU_VECTORS);
}

// ==================== Full Prover Tests ====================
// These run witness generation + constraint checking + full ZK proof generation.
// They are slow (~seconds each) due to 2^24 trace FFTs.

fn compile_mul_div_signed(trace_len_log2: usize) -> CompiledCircuitArtifact<Mersenne31Field> {
    use cs::machine::ops::unrolled::compile_unrolled_circuit_state_transition;
    compile_unrolled_circuit_state_transition::<Mersenne31Field>(
        &|cs| mul_div_table_addition_fn(cs),
        &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
        1 << 20,
        trace_len_log2,
    )
}

#[test]
#[ignore = "heavy: runs full prover with 2^24 trace"]
fn test_prove_div_signed_overflow() {
    skip_if_ci!();
    run_non_mem_prove_test(
        DIV_ENCODING,
        Box::new(DivMulDecoder::<true>),
        FAMILY_IDX,
        mul_div_table_addition_fn,
        mul_div_table_driver_fn,
        &compile_mul_div_signed,
        crate::tests::unrolled::mul_div::witness_eval_fn,
        &NonMemTestCase {
            label: "DIV",
            rs1: i32::MIN as u32,
            rs2: (-1i32) as u32,
            rd: i32::MIN as u32,
        },
        &[],
    );
}

#[test]
#[ignore = "heavy: runs full prover with 2^24 trace"]
fn test_prove_div_by_zero() {
    skip_if_ci!();
    run_non_mem_prove_test(
        DIV_ENCODING,
        Box::new(DivMulDecoder::<true>),
        FAMILY_IDX,
        mul_div_table_addition_fn,
        mul_div_table_driver_fn,
        &compile_mul_div_signed,
        crate::tests::unrolled::mul_div::witness_eval_fn,
        &NonMemTestCase {
            label: "DIV",
            rs1: 42,
            rs2: 0,
            rd: 0xFFFF_FFFF,
        },
        &[],
    );
}

#[test]
#[ignore = "heavy: runs full prover with 2^24 trace"]
fn test_prove_mul_basic() {
    skip_if_ci!();
    run_non_mem_prove_test(
        MUL_ENCODING,
        Box::new(DivMulDecoder::<true>),
        FAMILY_IDX,
        mul_div_table_addition_fn,
        mul_div_table_driver_fn,
        &compile_mul_div_signed,
        crate::tests::unrolled::mul_div::witness_eval_fn,
        &NonMemTestCase {
            label: "MUL",
            rs1: 6,
            rs2: 7,
            rd: 42,
        },
        &[],
    );
}
