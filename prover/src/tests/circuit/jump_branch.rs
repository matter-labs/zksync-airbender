use super::compliance_vectors;
use super::*;

use cs::machine::ops::unrolled::decoder::JumpSltBranchDecoder;
use cs::machine::ops::unrolled::jump_branch_slt::*;

const FAMILY_IDX: u8 = common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32, initial_pc: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data_at_pc(
        encoding,
        initial_pc,
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
    rd_reg: u8,
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

    // Branches and JAL/JALR-to-x0 don't write a register; x0 is hardwired so
    // the shuffle-RAM read-back will always be 0 and a check would be vacuous.
    if rd_reg != 0 {
        let regs = extract_circuit_registers(&cs);
        assert_eq!(
            regs[rd_reg as usize], case.rd,
            "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
            case.label, regs[rd_reg as usize], rd_reg, case.rd
        );
    }
}

use super::encoding::{encode_b, encode_i, encode_j, encode_jalr, encode_r};

fn run_slt_rr_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u8, u32, u32, u32)]) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding = encode_r(
            funct3,
            0b0000000,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = decoder_for(encoding, 0);
        check_rd(
            &dd,
            &NonMemTestCase {
                label,
                rs1,
                rs2,
                rd,
            },
            rd_reg,
        );
    }
}

fn run_slt_imm_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u16, u32, u32)]) {
    for &(rd_reg, rs1_reg, imm, rs1, rd) in vectors {
        let encoding = encode_i(funct3, rd_reg as u32, rs1_reg as u32, (imm as u32) & 0xFFF);
        let dd = decoder_for(encoding, 0);
        check_rd(
            &dd,
            &NonMemTestCase {
                label,
                rs1,
                rs2: 0,
                rd,
            },
            rd_reg,
        );
    }
}

fn run_branch_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u32, u32, bool)]) {
    for &(rs1_reg, rs2_reg, rs1, rs2, taken) in vectors {
        let encoding = encode_b(funct3, rs1_reg as u32, rs2_reg as u32, 8);
        let dd = decoder_for(encoding, 0);
        let new_pc = if taken { 8 } else { 4 };
        check_with_pc(
            &dd,
            &NonMemTestCase {
                label,
                rs1,
                rs2,
                rd: 0,
            },
            0,
            new_pc,
            0,
        );
    }
}

fn rejects_with_pc(
    label: &'static str,
    encoding: u32,
    rs1: u32,
    rs2: u32,
    rd: u32,
    initial_pc: u32,
    new_pc: u32,
) {
    let dd = decoder_for(encoding, initial_pc);
    let trace_data = make_trace_data_with_pc(
        &NonMemTestCase {
            label,
            rs1,
            rs2,
            rd,
        },
        initial_pc,
        new_pc,
    );
    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &dd,
        default_pc_value_in_padding: 0,
    };
    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        dd.to_vec(),
    );
    jump_branch_slt_table_addition_fn(&mut cs);
    jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(&mut cs);
    assert!(!cs.is_satisfied(), "{} unexpectedly satisfied", label);
}

#[test]
fn test_jump_and_taken_branch_reject_halfword_aligned_target() {
    rejects_with_pc("JAL halfword-aligned target", encode_j(1, 6), 0, 0, 4, 0, 6);
    rejects_with_pc(
        "JALR halfword-aligned target",
        encode_jalr(1, 2, 0),
        6,
        0,
        4,
        0,
        6,
    );
    rejects_with_pc(
        "BEQ halfword-aligned target",
        encode_b(0b000, 1, 2, 6),
        5,
        5,
        0,
        0,
        6,
    );
}

// ==================== SLT family ====================

#[test]
fn test_slt_compliance() {
    run_slt_rr_test("SLT", 0b010, compliance_vectors::SLT_VECTORS);
}

#[test]
fn test_sltu_compliance() {
    run_slt_rr_test("SLTU", 0b011, compliance_vectors::SLTU_VECTORS);
}

#[test]
fn test_slti_compliance() {
    run_slt_imm_test("SLTI", 0b010, compliance_vectors::SLTI_VECTORS);
}

#[test]
fn test_sltiu_compliance() {
    run_slt_imm_test("SLTIU", 0b011, compliance_vectors::SLTIU_VECTORS);
}

// ==================== Branches ====================

#[test]
fn test_beq_compliance() {
    run_branch_test("BEQ", 0b000, compliance_vectors::BEQ_VECTORS);
}

#[test]
fn test_bne_compliance() {
    run_branch_test("BNE", 0b001, compliance_vectors::BNE_VECTORS);
}

#[test]
fn test_blt_compliance() {
    run_branch_test("BLT", 0b100, compliance_vectors::BLT_VECTORS);
}

#[test]
fn test_bge_compliance() {
    run_branch_test("BGE", 0b101, compliance_vectors::BGE_VECTORS);
}

#[test]
fn test_bltu_compliance() {
    run_branch_test("BLTU", 0b110, compliance_vectors::BLTU_VECTORS);
}

#[test]
fn test_bgeu_compliance() {
    run_branch_test("BGEU", 0b111, compliance_vectors::BGEU_VECTORS);
}

// ==================== JAL ====================

fn run_jal_case(label: &'static str, rd_reg: u8, imm: u32, initial_pc: u32) {
    let encoding = encode_j(rd_reg as u32, imm);
    let dd = decoder_for(encoding, initial_pc);
    let expected_new_pc = initial_pc.wrapping_add(imm);
    // x0 always reads as 0 even though the circuit computes pc+4.
    let expected_rd = if rd_reg == 0 {
        0
    } else {
        initial_pc.wrapping_add(4)
    };
    check_with_pc(
        &dd,
        &NonMemTestCase {
            label,
            rs1: 0,
            rs2: 0,
            rd: expected_rd,
        },
        initial_pc,
        expected_new_pc,
        rd_reg,
    );
}

#[test]
fn test_jal_forward_jump() {
    // jal x1, +8 from pc=0: rd=4, new_pc=8
    run_jal_case("JAL forward", 1, 8, 0);
}

#[test]
fn test_jal_nonzero_initial_pc() {
    // jal x5, +0x14 from pc=4: rd=8, new_pc=0x18
    run_jal_case("JAL nonzero pc", 5, 0x14, 4);
}

#[test]
fn test_jal_link_to_x0() {
    // jal x0, +8 (the `j` pseudo-op): rd=0 because x0 is hardwired
    run_jal_case("JAL x0 (j pseudo)", 0, 8, 0);
}

// ==================== JALR ====================

fn run_jalr_case(
    label: &'static str,
    rd_reg: u8,
    rs1_reg: u8,
    imm: u32,
    rs1_value: u32,
    initial_pc: u32,
) {
    let encoding = encode_jalr(rd_reg as u32, rs1_reg as u32, imm);
    let dd = decoder_for(encoding, initial_pc);
    // sign-extend 12-bit immediate
    let sext_imm = if imm & 0x800 != 0 {
        imm | 0xFFFF_F000
    } else {
        imm & 0xFFF
    };
    let expected_new_pc = rs1_value.wrapping_add(sext_imm) & !1;
    let expected_rd = if rd_reg == 0 {
        0
    } else {
        initial_pc.wrapping_add(4)
    };
    check_with_pc(
        &dd,
        &NonMemTestCase {
            label,
            rs1: rs1_value,
            rs2: 0,
            rd: expected_rd,
        },
        initial_pc,
        expected_new_pc,
        rd_reg,
    );
}

#[test]
fn test_jalr_zero_imm() {
    // jalr x1, x2, 0 with x2=0x100, pc=0: rd=4, new_pc=0x100
    run_jalr_case("JALR imm=0", 1, 2, 0, 0x100, 0);
}

#[test]
fn test_jalr_positive_imm() {
    // jalr x1, x2, 0x10 with x2=0x100, pc=0: rd=4, new_pc=0x110
    run_jalr_case("JALR +imm", 1, 2, 0x10, 0x100, 0);
}

#[test]
fn test_jalr_link_to_x0() {
    // jalr x0, x2, 0 (the `jr` pseudo-op): rd=0
    run_jalr_case("JALR x0 (jr pseudo)", 0, 2, 0, 0x200, 0);
}

#[test]
fn test_jalr_clears_low_target_bit() {
    // RISC-V JALR clears bit 0 before committing the target PC.
    run_jalr_case("JALR odd target", 1, 2, 0, 0x101, 0);
}

// ==================== JAL / JALR compliance ====================

fn run_jal_compliance(label: &'static str, vectors: &[(u8, u32, u32)]) {
    for &(rd_reg, imm, initial_pc) in vectors {
        run_jal_case(label, rd_reg, imm, initial_pc);
    }
}

fn run_jalr_compliance(label: &'static str, vectors: &[(u8, u8, u32, u32, u32)]) {
    for &(rd_reg, rs1_reg, imm, rs1_val, initial_pc) in vectors {
        run_jalr_case(label, rd_reg, rs1_reg, imm, rs1_val, initial_pc);
    }
}

#[test]
fn test_jal_compliance() {
    run_jal_compliance("JAL", compliance_vectors::JAL_VECTORS);
}

#[test]
fn test_jalr_compliance() {
    run_jalr_compliance("JALR", compliance_vectors::JALR_VECTORS);
}

// ==================== Immediate / PC coverage ====================

#[test]
fn test_branch_nonzero_pc() {
    // BEQ x1, x1, +12 from pc=0x100 ->target = 0x10C
    let encoding = encode_b(0b000, 1, 1, 12);
    let dd = decoder_for(encoding, 0x100);
    check_with_pc(
        &dd,
        &NonMemTestCase {
            label: "BEQ pc=0x100 +12",
            rs1: 5,
            rs2: 5,
            rd: 0,
        },
        0x100,
        0x10C,
        0,
    );
}

#[test]
fn test_branch_backward() {
    // BEQ x1, x1, -4 from pc=0x100 ->target = 0xFC
    let encoding = encode_b(0b000, 1, 1, 0xFFFF_FFFC);
    let dd = decoder_for(encoding, 0x100);
    check_with_pc(
        &dd,
        &NonMemTestCase {
            label: "BEQ backward -4",
            rs1: 7,
            rs2: 7,
            rd: 0,
        },
        0x100,
        0xFC,
        0,
    );
}

#[test]
fn test_branch_crosses_16bit_limb_boundary() {
    // BEQ x1, x1, +8 from pc=0xFFFC ->target = 0x10004 (crosses 16-bit limb)
    let encoding = encode_b(0b000, 1, 1, 8);
    let dd = decoder_for(encoding, 0xFFFC);
    check_with_pc(
        &dd,
        &NonMemTestCase {
            label: "BEQ pc=0xFFFC +8 (crosses limb)",
            rs1: 9,
            rs2: 9,
            rd: 0,
        },
        0xFFFC,
        0x1_0004,
        0,
    );
}

#[test]
fn test_jal_backward_jump() {
    // jal x1, -4 from pc=0x100: rd=0x104, new_pc=0xFC
    run_jal_case("JAL backward -4", 1, 0xFFFF_FFFC, 0x100);
}

#[test]
fn test_jalr_negative_imm() {
    // jalr x1, x2, -4 with x2=0x100: target = (0x100 - 4) & !1 = 0xFC
    run_jalr_case("JALR -imm", 1, 2, 0xFFC, 0x100, 0);
}

#[test]
fn test_jalr_nonzero_initial_pc_link() {
    // jalr x5, x2, +0x10 with x2=0x100, pc=0x200: rd=0x204, new_pc=0x110
    run_jalr_case("JALR nonzero pc link", 5, 2, 0x10, 0x100, 0x200);
}
