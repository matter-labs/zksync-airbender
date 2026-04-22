use super::*;
use super::compliance_vectors;

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

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
    let circuit_regs = run_non_mem_circuit_test_with_pc_padding(
        decoder_data,
        jump_branch_slt_table_addition_fn,
        jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
        0,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
    );
}

fn check_with_pc(
    decoder_data: &[ExecutorFamilyDecoderData],
    case: &NonMemTestCase,
    initial_pc: u32,
    new_pc: u32,
) {
    let trace_data = make_trace_data_with_pc(case, initial_pc, new_pc);
    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
        default_pc_value_in_padding: 0,
    };
    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );
    jump_branch_slt_table_addition_fn(&mut cs);
    jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(&mut cs);
    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );
}

// -- Encoding helpers --
const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const fn encode_i(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

const fn encode_b(funct3: u32, rs1: u32, rs2: u32, imm: u32) -> u32 {
    let imm_12 = (imm >> 12) & 1;
    let imm_10_5 = (imm >> 5) & 0x3F;
    let imm_4_1 = (imm >> 1) & 0xF;
    let imm_11 = (imm >> 11) & 1;
    (imm_12 << 31)
        | (imm_10_5 << 25)
        | (rs2 << 20)
        | (rs1 << 15)
        | (funct3 << 12)
        | (imm_4_1 << 8)
        | (imm_11 << 7)
        | 0x63
}

fn run_slt_rr_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u8, u32, u32, u32)]) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding = encode_r(funct3, 0b0000000, rd_reg as u32, rs1_reg as u32, rs2_reg as u32);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label, rs1, rs2, rd }, rd_reg);
    }
}

fn run_slt_imm_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u16, u32, u32)]) {
    for &(rd_reg, rs1_reg, imm, rs1, rd) in vectors {
        let encoding = encode_i(funct3, rd_reg as u32, rs1_reg as u32, (imm as u32) & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(&dd, &NonMemTestCase { label, rs1, rs2: 0, rd }, rd_reg);
    }
}

fn run_branch_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u32, u32, bool)]) {
    for &(rs1_reg, rs2_reg, rs1, rs2, taken) in vectors {
        let encoding = encode_b(funct3, rs1_reg as u32, rs2_reg as u32, 8);
        let dd = decoder_for(encoding);
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase { label, rs1, rs2, rd: 0 },
            0,
            new_pc,
        );
    }
}

// ==================== SLT family ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_slt_compliance() {
    skip_if_ci!();
    run_slt_rr_test("SLT", 0b010, compliance_vectors::SLT_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_sltu_compliance() {
    skip_if_ci!();
    run_slt_rr_test("SLTU", 0b011, compliance_vectors::SLTU_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_slti_compliance() {
    skip_if_ci!();
    run_slt_imm_test("SLTI", 0b010, compliance_vectors::SLTI_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_sltiu_compliance() {
    skip_if_ci!();
    run_slt_imm_test("SLTIU", 0b011, compliance_vectors::SLTIU_VECTORS);
}

// ==================== Branches ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_beq_compliance() {
    skip_if_ci!();
    run_branch_test("BEQ", 0b000, compliance_vectors::BEQ_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bne_compliance() {
    skip_if_ci!();
    run_branch_test("BNE", 0b001, compliance_vectors::BNE_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_blt_compliance() {
    skip_if_ci!();
    run_branch_test("BLT", 0b100, compliance_vectors::BLT_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bge_compliance() {
    skip_if_ci!();
    run_branch_test("BGE", 0b101, compliance_vectors::BGE_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bltu_compliance() {
    skip_if_ci!();
    run_branch_test("BLTU", 0b110, compliance_vectors::BLTU_VECTORS);
}

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bgeu_compliance() {
    skip_if_ci!();
    run_branch_test("BGEU", 0b111, compliance_vectors::BGEU_VECTORS);
}
