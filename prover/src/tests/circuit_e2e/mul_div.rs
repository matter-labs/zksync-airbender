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

fn check(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    run_non_mem_circuit_test(
        decoder_data,
        mul_div_table_addition_fn,
        mul_div_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
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

// ==================== MUL ====================

#[test]
fn test_mul_basic() {
    skip_if_ci!();
    let dd = decoder_for(MUL);
    check(&dd, &NonMemTestCase { label: "MUL", rs1: 6, rs2: 7, rd: 42 });
    check(&dd, &NonMemTestCase { label: "MUL", rs1: 0, rs2: 100, rd: 0 });
    check(&dd, &NonMemTestCase {
        label: "MUL",
        rs1: u32::MAX, rs2: u32::MAX,
        rd: 1, // low 32 bits of (-1)*(-1) = 1
    });
}

// ==================== MULHU ====================

#[test]
fn test_mulhu() {
    skip_if_ci!();
    let dd = decoder_for(MULHU);
    check(&dd, &NonMemTestCase {
        label: "MULHU",
        rs1: u32::MAX, rs2: u32::MAX,
        rd: 0xFFFFFFFE, // high 32 bits of (2^32-1)^2
    });
    check(&dd, &NonMemTestCase { label: "MULHU", rs1: 1, rs2: 1, rd: 0 });
}

// ==================== MULH (signed high) ====================

#[test]
fn test_mulh_basic() {
    skip_if_ci!();
    let dd = decoder_for(MULH);
    check(&dd, &NonMemTestCase {
        label: "MULH",
        rs1: 6, rs2: 7, rd: 0,
    });
    check(&dd, &NonMemTestCase {
        label: "MULH",
        rs1: u32::MAX, rs2: u32::MAX, rd: 0,
    });
    check(&dd, &NonMemTestCase {
        label: "MULH",
        rs1: 0x7FFF_FFFF, rs2: 2, rd: 0,
    });
    check(&dd, &NonMemTestCase {
        label: "MULH",
        rs1: u32::MAX, rs2: 0x7FFF_FFFF, rd: 0xFFFF_FFFF,
    });
}

// ==================== MULHSU (signed*unsigned high) ====================

#[test]
fn test_mulhsu_basic() {
    skip_if_ci!();
    let dd = decoder_for(MULHSU);
    check(&dd, &NonMemTestCase {
        label: "MULHSU",
        rs1: u32::MAX, rs2: 1, rd: 0xFFFF_FFFF,
    });
    check(&dd, &NonMemTestCase {
        label: "MULHSU",
        rs1: 1, rs2: 0xFFFF_FFFF, rd: 0,
    });
}

// ==================== DIV (signed) ====================

#[test]
fn test_div_signed_overflow() {
    skip_if_ci!();
    let dd = decoder_for(DIV);
    // INT_MIN / -1 = INT_MIN (overflow wraps)
    check(&dd, &NonMemTestCase {
        label: "DIV",
        rs1: i32::MIN as u32, rs2: (-1i32) as u32, rd: i32::MIN as u32,
    });
}

#[test]
fn test_div_signed_by_zero() {
    skip_if_ci!();
    let dd = decoder_for(DIV);
    check(&dd, &NonMemTestCase {
        label: "DIV",
        rs1: 42, rs2: 0, rd: 0xFFFF_FFFF,
    });
}

#[test]
fn test_div_signed_basic() {
    skip_if_ci!();
    let dd = decoder_for(DIV);
    check(&dd, &NonMemTestCase { label: "DIV", rs1: 20, rs2: 6, rd: 3 });
    check(&dd, &NonMemTestCase {
        label: "DIV",
        rs1: (-20i32) as u32, rs2: 6, rd: (-3i32) as u32,
    });
    check(&dd, &NonMemTestCase {
        label: "DIV",
        rs1: (-20i32) as u32, rs2: (-6i32) as u32, rd: 3,
    });
}

// ==================== REM (signed) ====================

#[test]
fn test_rem_signed_overflow() {
    skip_if_ci!();
    let dd = decoder_for(REM);
    check(&dd, &NonMemTestCase {
        label: "REM",
        rs1: i32::MIN as u32, rs2: (-1i32) as u32, rd: 0,
    });
}

#[test]
fn test_rem_signed_by_zero() {
    skip_if_ci!();
    let dd = decoder_for(REM);
    check(&dd, &NonMemTestCase {
        label: "REM",
        rs1: 42, rs2: 0, rd: 42,
    });
}

#[test]
fn test_rem_signed_basic() {
    skip_if_ci!();
    let dd = decoder_for(REM);
    check(&dd, &NonMemTestCase { label: "REM", rs1: 20, rs2: 6, rd: 2 });
    check(&dd, &NonMemTestCase {
        label: "REM",
        rs1: (-20i32) as u32, rs2: 6, rd: (-2i32) as u32,
    });
}

// ==================== DIVU (unsigned) ====================

#[test]
fn test_divu_basic() {
    skip_if_ci!();
    let dd = decoder_for(DIVU);
    check(&dd, &NonMemTestCase { label: "DIVU", rs1: 20, rs2: 6, rd: 3 });
    check(&dd, &NonMemTestCase {
        label: "DIVU",
        rs1: u32::MAX, rs2: 1, rd: u32::MAX,
    });
}

#[test]
fn test_divu_by_zero() {
    skip_if_ci!();
    let dd = decoder_for(DIVU);
    check(&dd, &NonMemTestCase {
        label: "DIVU",
        rs1: 42, rs2: 0, rd: 0xFFFF_FFFF,
    });
}

// ==================== REMU (unsigned) ====================

#[test]
fn test_remu_basic() {
    skip_if_ci!();
    let dd = decoder_for(REMU);
    check(&dd, &NonMemTestCase { label: "REMU", rs1: 20, rs2: 6, rd: 2 });
}

#[test]
fn test_remu_by_zero() {
    skip_if_ci!();
    let dd = decoder_for(REMU);
    check(&dd, &NonMemTestCase {
        label: "REMU",
        rs1: 42, rs2: 0, rd: 42,
    });
}

// ==================== Unsigned-only circuit ====================

#[test]
fn test_divu_unsigned_circuit() {
    skip_if_ci!();
    let dd = decoder_unsigned(DIVU);
    check_unsigned(&dd, &NonMemTestCase { label: "DIVU", rs1: 20, rs2: 6, rd: 3 });
    check_unsigned(&dd, &NonMemTestCase {
        label: "DIVU",
        rs1: 42, rs2: 0, rd: 0xFFFF_FFFF,
    });
}

#[test]
fn test_remu_unsigned_circuit() {
    skip_if_ci!();
    let dd = decoder_unsigned(REMU);
    check_unsigned(&dd, &NonMemTestCase { label: "REMU", rs1: 20, rs2: 6, rd: 2 });
    check_unsigned(&dd, &NonMemTestCase {
        label: "REMU",
        rs1: 42, rs2: 0, rd: 42,
    });
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
