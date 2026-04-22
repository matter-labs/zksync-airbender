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

fn check(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
    );
}

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
    );
    assert_eq!(
        circuit_regs[3], case.rd,
        "{}: circuit wrote {:#010X} to x3 but expected {:#010X}",
        case.label, circuit_regs[3], case.rd
    );
}

fn check_unsigned(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, false>,
        case,
    );
}

fn check_unsigned_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, false>,
        case,
    );
    assert_eq!(
        circuit_regs[3], case.rd,
        "{}: circuit wrote {:#010X} to x3 but expected {:#010X}",
        case.label, circuit_regs[3], case.rd
    );
}

// -- RISC-V R-type encoding helpers --
// opcode=0x33, funct7=0x01 (M extension)
const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const MUL: u32 = encode_r(0b000, 0b0000001, 3, 1, 2);
const MULH: u32 = encode_r(0b001, 0b0000001, 3, 1, 2);
const MULHSU: u32 = encode_r(0b010, 0b0000001, 3, 1, 2);
const MULHU: u32 = encode_r(0b011, 0b0000001, 3, 1, 2);
const DIV: u32 = encode_r(0b100, 0b0000001, 3, 1, 2);
const DIVU: u32 = encode_r(0b101, 0b0000001, 3, 1, 2);
const REM: u32 = encode_r(0b110, 0b0000001, 3, 1, 2);
const REMU: u32 = encode_r(0b111, 0b0000001, 3, 1, 2);

// ==================== Compliance vector tests ====================

#[test]
fn test_mul_compliance() {
    skip_if_ci!();
    let dd = decoder_for(MUL);
    for &(rs1, rs2, rd) in compliance_vectors::MUL_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "MUL", rs1, rs2, rd });
    }
}

#[test]
fn test_mulh_compliance() {
    skip_if_ci!();
    let dd = decoder_for(MULH);
    for &(rs1, rs2, rd) in compliance_vectors::MULH_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "MULH", rs1, rs2, rd });
    }
}

#[test]
fn test_mulhsu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(MULHSU);
    for &(rs1, rs2, rd) in compliance_vectors::MULHSU_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "MULHSU", rs1, rs2, rd });
    }
}

#[test]
fn test_mulhu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(MULHU);
    for &(rs1, rs2, rd) in compliance_vectors::MULHU_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "MULHU", rs1, rs2, rd });
    }
}

#[test]
fn test_div_compliance() {
    skip_if_ci!();
    let dd = decoder_for(DIV);
    for &(rs1, rs2, rd) in compliance_vectors::DIV_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "DIV", rs1, rs2, rd });
    }
}

#[test]
fn test_divu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(DIVU);
    for &(rs1, rs2, rd) in compliance_vectors::DIVU_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "DIVU", rs1, rs2, rd });
    }
}

#[test]
fn test_rem_compliance() {
    skip_if_ci!();
    let dd = decoder_for(REM);
    for &(rs1, rs2, rd) in compliance_vectors::REM_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "REM", rs1, rs2, rd });
    }
}

#[test]
fn test_remu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(REMU);
    for &(rs1, rs2, rd) in compliance_vectors::REMU_VECTORS {
        check_rd(&dd, &NonMemTestCase { label: "REMU", rs1, rs2, rd });
    }
}

// ==================== Unsigned-only circuit ====================

#[test]
fn test_divu_unsigned_circuit() {
    skip_if_ci!();
    let dd = decoder_unsigned(DIVU);
    for &(rs1, rs2, rd) in compliance_vectors::DIVU_VECTORS.iter() {
        check_unsigned_rd(&dd, &NonMemTestCase { label: "DIVU", rs1, rs2, rd });
    }
}

#[test]
fn test_remu_unsigned_circuit() {
    skip_if_ci!();
    let dd = decoder_unsigned(REMU);
    for &(rs1, rs2, rd) in compliance_vectors::REMU_VECTORS.iter() {
        check_unsigned_rd(&dd, &NonMemTestCase { label: "REMU", rs1, rs2, rd });
    }
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
        DIV,
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
        DIV,
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
        MUL,
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
