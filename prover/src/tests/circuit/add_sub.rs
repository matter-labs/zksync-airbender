use super::compliance_vectors;
use super::*;

use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
use cs::machine::ops::unrolled::decoder::{
    process_binary_into_separate_tables_ext, AddSubLuiAuipcMopDecoder,
};
use std::alloc::Global;

const FAMILY_IDX: u8 = common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(
        encoding,
        Box::new(AddSubLuiAuipcMopDecoder),
        FAMILY_IDX,
        &[],
    )
}

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        add_sub_lui_auipc_mop_table_addition_fn,
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode,
        case,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
    );
}

use super::encoding::{encode_i, encode_r, encode_r_system, encode_u};

// ==================== ADD  ====================

#[test]
fn test_add_compliance() {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in compliance_vectors::ADD_VECTORS {
        let encoding = encode_r(
            0b000,
            0b0000000,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "ADD",
                rs1,
                rs2,
                rd,
            },
            rd_reg,
        );
    }
}

// ==================== SUB (compliance) ====================

#[test]
fn test_sub_compliance() {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in compliance_vectors::SUB_VECTORS {
        let encoding = encode_r(
            0b000,
            0b0100000,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "SUB",
                rs1,
                rs2,
                rd,
            },
            rd_reg,
        );
    }
}

// ==================== ADDI (compliance) ====================

#[test]
fn test_addi_compliance() {
    for &(rd_reg, rs1_reg, imm, rs1, rd) in compliance_vectors::ADDI_VECTORS {
        let encoding = encode_i(0b000, rd_reg as u32, rs1_reg as u32, imm as u32 & 0xFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "ADDI",
                rs1,
                rs2: 0,
                rd,
            },
            rd_reg,
        );
    }
}

// ==================== LUI (compliance) ====================

#[test]
fn test_lui_compliance() {
    for &(rd_reg, imm_upper, rd) in compliance_vectors::LUI_VECTORS {
        let encoding = encode_u(0x37, rd_reg as u32, imm_upper & 0xFFFFF);
        let dd = decoder_for(encoding);
        check_rd(
            &dd,
            &NonMemTestCase {
                label: "LUI",
                rs1: 0,
                rs2: 0,
                rd,
            },
            rd_reg,
        );
    }
}

// ==================== AUIPC ====================
//
// AUIPC computes rd = pc + (imm_upper << 12). The compliance vectors used for
// LUI etc. all pin pc = 0, which collapses AUIPC into LUI and cannot detect a
// circuit that ignored the PC operand. Instead we drive AUIPC from
// `AUIPC_WITH_PC_VECTORS`, which carries an explicit non-zero PC per case.

// Builds a bytecode large enough to span `initial_pc`, places the AUIPC
// encoding at index `pc / 4` (where the circuit looks it up via
// `spec_decoder_relation`), runs the circuit and checks rd.
fn check_auipc_at_pc(rd_reg: u8, imm_upper: u32, initial_pc: u32, expected_rd: u32) {
    assert!(initial_pc % 4 == 0, "PC must be 4-byte aligned");
    let encoding = encode_u(0x17, rd_reg as u32, imm_upper);

    let pc_idx = (initial_pc / 4) as usize;
    let bytecode_words = (pc_idx + 1).next_power_of_two().max(1024);
    let mut bytecode = vec![0u32; bytecode_words];
    bytecode[pc_idx] = encoding;

    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[Box::new(AddSubLuiAuipcMopDecoder)],
        bytecode_words,
        &[],
    );
    let (_, decoder_data) = t.remove(&FAMILY_IDX).expect("decoder data");

    let case = NonMemTestCase {
        label: "AUIPC",
        rs1: 0,
        rs2: 0,
        rd: expected_rd,
    };
    let trace_data = make_trace_data_with_pc(&case, initial_pc, initial_pc.wrapping_add(4));

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &decoder_data,
        default_pc_value_in_padding: 4,
    };
    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );
    add_sub_lui_auipc_mop_table_addition_fn(&mut cs);
    add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(&mut cs);

    assert!(
        cs.is_satisfied(),
        "AUIPC constraints NOT satisfied: pc=0x{:08X}, imm=0x{:05X}, expected rd=0x{:08X}",
        initial_pc,
        imm_upper,
        expected_rd
    );
    let regs = extract_circuit_registers(&cs);
    assert_eq!(
        regs[rd_reg as usize], expected_rd,
        "AUIPC: circuit wrote {:#010X} to x{} but expected {:#010X} (pc=0x{:08X}, imm=0x{:05X})",
        regs[rd_reg as usize], rd_reg, expected_rd, initial_pc, imm_upper
    );
}

#[test]
fn test_auipc_compliance() {
    for &(rd_reg, imm_upper, initial_pc, rd) in compliance_vectors::AUIPC_WITH_PC_VECTORS {
        check_auipc_at_pc(rd_reg, imm_upper & 0xFFFFF, initial_pc, rd);
    }
}

// ==================== MOP (Mersenne field ops, p = 2^31 - 1) ====================

fn run_mop_test(label: &'static str, funct7: u32, vectors: &[(u8, u8, u8, u32, u32, u32)]) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding =
            encode_r_system(0b100, funct7, rd_reg as u32, rs1_reg as u32, rs2_reg as u32);
        let dd = decoder_for(encoding);
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

#[test]
fn test_addmod_compliance() {
    run_mop_test("ADDMOD", 0b1000001, compliance_vectors::ADDMOD_VECTORS);
}

#[test]
fn test_submod_compliance() {
    run_mop_test("SUBMOD", 0b1000011, compliance_vectors::SUBMOD_VECTORS);
}

#[test]
fn test_mulmod_compliance() {
    run_mop_test("MULMOD", 0b1000101, compliance_vectors::MULMOD_VECTORS);
}

// -- Named MOP edge cases (Mersenne prime p = 2^31 - 1) --
const P: u32 = 0x7FFF_FFFF;

const ADDMOD_FUNCT7: u32 = 0b1000001;
const SUBMOD_FUNCT7: u32 = 0b1000011;
const MULMOD_FUNCT7: u32 = 0b1000101;

#[test]
fn test_addmod_p_minus_1_plus_1_wraps_to_zero() {
    // (p-1) + 1 == p ≡ 0  (mod p)
    run_mop_test("ADDMOD (p-1)+1=0", ADDMOD_FUNCT7, &[(3, 1, 2, P - 1, 1, 0)]);
}

#[test]
fn test_addmod_p_minus_2_plus_3_wraps_to_one() {
    // (p-2) + 3 == p+1 ≡ 1  (mod p)
    run_mop_test("ADDMOD (p-2)+3=1", ADDMOD_FUNCT7, &[(3, 1, 2, P - 2, 3, 1)]);
}

#[test]
fn test_submod_zero_minus_one_wraps_to_p_minus_one() {
    // 0 - 1 ≡ p-1  (mod p)
    run_mop_test("SUBMOD 0-1=p-1", SUBMOD_FUNCT7, &[(3, 1, 2, 0, 1, P - 1)]);
}

#[test]
fn test_submod_one_minus_p_minus_one_wraps_to_two() {
    // 1 - (p-1) == 2 - p ≡ 2  (mod p)
    run_mop_test("SUBMOD 1-(p-1)=2", SUBMOD_FUNCT7, &[(3, 1, 2, 1, P - 1, 2)]);
}

#[test]
fn test_mulmod_p_minus_1_squared_is_one() {
    // (p-1)^2 == p^2 - 2p + 1 ≡ 1  (mod p)
    run_mop_test(
        "MULMOD (p-1)*(p-1)=1",
        MULMOD_FUNCT7,
        &[(3, 1, 2, P - 1, P - 1, 1)],
    );
}

#[test]
fn test_mulmod_p_minus_1_times_two_is_p_minus_two() {
    // 2*(p-1) == 2p - 2 ≡ -2 ≡ p-2  (mod p)
    run_mop_test(
        "MULMOD (p-1)*2=p-2",
        MULMOD_FUNCT7,
        &[(3, 1, 2, P - 1, 2, P - 2)],
    );
}

// ==================== x0 destination (write masking) ====================
// x0 is hardwired to zero in RISC-V. The circuit detects rd == x0 and masks
// the shuffle-RAM write value to 0 regardless of what the op produced. These
// tests pin that intent explicitly: each runs an instruction whose ALU output
// would be non-zero, but with rd encoded as x0, and expects the committed x0
// value to be 0. A circuit that forgot to mask would write the computed value
// into x0 and fail the assertion.

#[test]
fn test_add_writes_zero_to_x0() {
    // ADD x0, x1, x2 with rs1=10, rs2=20 → ALU = 30, but x0 stays 0.
    let encoding = encode_r(0b000, 0b0000000, 0, 1, 2);
    let dd = decoder_for(encoding);
    check_rd(
        &dd,
        &NonMemTestCase {
            label: "ADD x0",
            rs1: 10,
            rs2: 20,
            rd: 0,
        },
        0,
    );
}

#[test]
fn test_sub_writes_zero_to_x0() {
    // SUB x0, x1, x2 with rs1=50, rs2=20 → ALU = 30, but x0 stays 0.
    let encoding = encode_r(0b000, 0b0100000, 0, 1, 2);
    let dd = decoder_for(encoding);
    check_rd(
        &dd,
        &NonMemTestCase {
            label: "SUB x0",
            rs1: 50,
            rs2: 20,
            rd: 0,
        },
        0,
    );
}

#[test]
fn test_addi_writes_zero_to_x0() {
    // ADDI x0, x1, 42 with rs1=100 → ALU = 142, but x0 stays 0.
    let encoding = encode_i(0b000, 0, 1, 42);
    let dd = decoder_for(encoding);
    check_rd(
        &dd,
        &NonMemTestCase {
            label: "ADDI x0",
            rs1: 100,
            rs2: 0,
            rd: 0,
        },
        0,
    );
}

#[test]
fn test_lui_writes_zero_to_x0() {
    // LUI x0, 0x12345 → ALU = 0x12345000, but x0 stays 0.
    let encoding = encode_u(0x37, 0, 0x12345);
    let dd = decoder_for(encoding);
    check_rd(
        &dd,
        &NonMemTestCase {
            label: "LUI x0",
            rs1: 0,
            rs2: 0,
            rd: 0,
        },
        0,
    );
}

#[test]
fn test_auipc_writes_zero_to_x0() {
    // AUIPC x0, 0x2 at pc=0x1000 → ALU = 0x3000, but x0 stays 0.
    check_auipc_at_pc(0, 0x2, 0x1000, 0);
}

#[test]
fn test_addmod_writes_zero_to_x0() {
    // ADDMOD x0, x1, x2 with rs1=10, rs2=20 → ALU = 30 mod p, x0 stays 0.
    run_mop_test("ADDMOD x0", ADDMOD_FUNCT7, &[(0, 1, 2, 10, 20, 0)]);
}

#[test]
fn test_submod_writes_zero_to_x0() {
    // SUBMOD x0, x1, x2 with rs1=10, rs2=20 → ALU = (10 - 20) mod p
    // = p - 10 (a large non-zero value), but x0 stays 0.
    run_mop_test("SUBMOD x0", SUBMOD_FUNCT7, &[(0, 1, 2, 10, 20, 0)]);
}

#[test]
fn test_mulmod_writes_zero_to_x0() {
    // MULMOD x0, x1, x2 with rs1=10, rs2=20 → ALU = 200 mod p = 200, x0 stays 0.
    run_mop_test("MULMOD x0", MULMOD_FUNCT7, &[(0, 1, 2, 10, 20, 0)]);
}
