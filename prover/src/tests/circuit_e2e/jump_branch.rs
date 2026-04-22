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

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase) {
    let circuit_regs = run_non_mem_circuit_test_with_pc_padding(
        decoder_data,
        jump_branch_slt_table_addition_fn,
        jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>,
        case,
        0,
    );
    assert_eq!(
        circuit_regs[3], case.rd,
        "{}: circuit wrote {:#010X} to x3 but expected {:#010X}",
        case.label, circuit_regs[3], case.rd
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

// SLT x3, x1, x2
const SLT: u32 = encode_r(0b010, 0b0000000, 3, 1, 2);
// SLTU x3, x1, x2
const SLTU: u32 = encode_r(0b011, 0b0000000, 3, 1, 2);

// Branch encodings: branch offset = 8 (imm=8), rs1=x1, rs2=x2
const BEQ: u32 = encode_b(0b000, 1, 2, 8);
const BNE: u32 = encode_b(0b001, 1, 2, 8);
const BLT: u32 = encode_b(0b100, 1, 2, 8);
const BGE: u32 = encode_b(0b101, 1, 2, 8);
const BLTU: u32 = encode_b(0b110, 1, 2, 8);
const BGEU: u32 = encode_b(0b111, 1, 2, 8);

// ==================== SLT ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_slt_compliance() {
    skip_if_ci!();
    let dd = decoder_for(SLT);
    for &(rs1, rs2, rd) in compliance_vectors::SLT_VECTORS {
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "SLT",
                rs1,
                rs2,
                rd,
            },
        );
    }
}

// ==================== SLTU ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_sltu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(SLTU);
    for &(rs1, rs2, rd) in compliance_vectors::SLTU_VECTORS {
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "SLTU",
                rs1,
                rs2,
                rd,
            },
        );
    }
}

// ==================== SLTI ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_slti_compliance() {
    skip_if_ci!();
    for &(rs1, imm, rd) in compliance_vectors::SLTI_VECTORS {
        let encoding = encode_i(0b010, 3, 1, imm & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "SLTI",
                rs1,
                rs2: 0,
                rd,
            },
        );
    }
}

// ==================== SLTIU ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_sltiu_compliance() {
    skip_if_ci!();
    for &(rs1, imm, rd) in compliance_vectors::SLTIU_VECTORS {
        let encoding = encode_i(0b011, 3, 1, imm & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "SLTIU",
                rs1,
                rs2: 0,
                rd,
            },
        );
    }
}

// ==================== BEQ ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_beq_compliance() {
    skip_if_ci!();
    let dd = decoder_for(BEQ);
    for &(rs1, rs2, taken) in compliance_vectors::BEQ_VECTORS {
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label: "BEQ",
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
        );
    }
}

// ==================== BNE ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bne_compliance() {
    skip_if_ci!();
    let dd = decoder_for(BNE);
    for &(rs1, rs2, taken) in compliance_vectors::BNE_VECTORS {
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label: "BNE",
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
        );
    }
}

// ==================== BLT ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_blt_compliance() {
    skip_if_ci!();
    let dd = decoder_for(BLT);
    for &(rs1, rs2, taken) in compliance_vectors::BLT_VECTORS {
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label: "BLT",
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
        );
    }
}

// ==================== BGE ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bge_compliance() {
    skip_if_ci!();
    let dd = decoder_for(BGE);
    for &(rs1, rs2, taken) in compliance_vectors::BGE_VECTORS {
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label: "BGE",
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
        );
    }
}

// ==================== BLTU ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bltu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(BLTU);
    for &(rs1, rs2, taken) in compliance_vectors::BLTU_VECTORS {
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label: "BLTU",
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
        );
    }
}

// ==================== BGEU ====================

#[test]
#[ignore = "BasicAssembly cannot resolve jump/branch/SLT witness variables"]
fn test_bgeu_compliance() {
    skip_if_ci!();
    let dd = decoder_for(BGEU);
    for &(rs1, rs2, taken) in compliance_vectors::BGEU_VECTORS {
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label: "BGEU",
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
        );
    }
}
