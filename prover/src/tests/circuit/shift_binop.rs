use super::compliance_vectors;
use super::*;

use cs::machine::machine_configurations::create_csr_table_for_delegation;
use cs::machine::ops::unrolled::decoder::ShiftBinaryCsrrwDecoder;
use cs::machine::ops::unrolled::shift_binary_csr::*;
use cs::machine::NON_DETERMINISM_CSR;
use cs::tables::{LookupWrapper, TableType};

const FAMILY_IDX: u8 = common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;

fn decoder_for(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    prepare_decoder_data(encoding, Box::new(ShiftBinaryCsrrwDecoder), FAMILY_IDX, &[])
}

fn check_rd(decoder_data: &[ExecutorFamilyDecoderData], case: &NonMemTestCase, rd_reg: u8) {
    let circuit_regs = run_non_mem_circuit_test(
        decoder_data,
        shift_binop_csrrw_table_addition_fn,
        shift_binop_csrrw_circuit_with_preprocessed_bytecode,
        case,
    );
    assert_eq!(
        circuit_regs[rd_reg as usize], case.rd,
        "{}: circuit wrote {:#010X} to x{} but expected {:#010X}",
        case.label, circuit_regs[rd_reg as usize], rd_reg, case.rd
    );
}

use super::encoding::{encode_csrrw, encode_i, encode_i_shift, encode_r};

fn run_rr_test(
    label: &'static str,
    funct3: u32,
    funct7: u32,
    vectors: &[(u8, u8, u8, u32, u32, u32)],
) {
    for &(rd_reg, rs1_reg, rs2_reg, rs1, rs2, rd) in vectors {
        let encoding = encode_r(
            funct3,
            funct7,
            rd_reg as u32,
            rs1_reg as u32,
            rs2_reg as u32,
        );
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

fn run_ishift_test(
    label: &'static str,
    funct3: u32,
    funct7: u32,
    vectors: &[(u8, u8, u8, u32, u32)],
) {
    for &(rd_reg, rs1_reg, shamt, rs1, rd) in vectors {
        let encoding = encode_i_shift(
            funct3,
            funct7,
            rd_reg as u32,
            rs1_reg as u32,
            (shamt as u32) & 0x1F,
        );
        let dd = decoder_for(encoding);
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

fn run_ilog_test(label: &'static str, funct3: u32, vectors: &[(u8, u8, u16, u32, u32)]) {
    for &(rd_reg, rs1_reg, imm, rs1, rd) in vectors {
        let encoding = encode_i(funct3, rd_reg as u32, rs1_reg as u32, (imm as u32) & 0xFFF);
        let dd = decoder_for(encoding);
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

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_sll() {
    run_rr_test("SLL", 0b001, 0b0000000, compliance_vectors::SLL_VECTORS);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_srl() {
    run_rr_test("SRL", 0b101, 0b0000000, compliance_vectors::SRL_VECTORS);
}

#[test]
fn test_sra() {
    run_rr_test("SRA", 0b101, 0b0100000, compliance_vectors::SRA_VECTORS);
}

#[test]
fn test_xor() {
    run_rr_test("XOR", 0b100, 0b0000000, compliance_vectors::XOR_VECTORS);
}

#[test]
fn test_and() {
    run_rr_test("AND", 0b111, 0b0000000, compliance_vectors::AND_VECTORS);
}

#[test]
fn test_or() {
    run_rr_test("OR", 0b110, 0b0000000, compliance_vectors::OR_VECTORS);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_slli() {
    run_ishift_test("SLLI", 0b001, 0b0000000, compliance_vectors::SLLI_VECTORS);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_srli() {
    run_ishift_test("SRLI", 0b101, 0b0000000, compliance_vectors::SRLI_VECTORS);
}

#[test]
fn test_srai() {
    run_ishift_test("SRAI", 0b101, 0b0100000, compliance_vectors::SRAI_VECTORS);
}

#[test]
fn test_xori() {
    run_ilog_test("XORI", 0b100, compliance_vectors::XORI_VECTORS);
}

#[test]
fn test_andi() {
    run_ilog_test("ANDI", 0b111, compliance_vectors::ANDI_VECTORS);
}

#[test]
fn test_ori() {
    run_ilog_test("ORI", 0b110, compliance_vectors::ORI_VECTORS);
}

// ==================== CSRRW ====================

/// Run the CSRRW circuit on a single-cycle trace.
/// `f` is invoked with the constructed cs to perform the satisfiability check.
/// trace_data is kept alive on this stack frame so the oracle's reference
/// stays valid for the duration of `f` (including any re-evaluation done by
/// is_satisfied).
fn with_csrrw_cs<R>(
    rd_reg: u8,
    rs1_reg: u8,
    csr: u16,
    rd_value_in_trace: u32,
    delegation_type_in_trace: u16,
    f: impl FnOnce(BasicAssembly<Mersenne31Field>) -> R,
) -> R {
    let encoding = encode_csrrw(rd_reg as u32, rs1_reg as u32, csr as u32);
    let dd = prepare_decoder_data(
        encoding,
        Box::new(ShiftBinaryCsrrwDecoder),
        FAMILY_IDX,
        &[csr],
    );

    let trace_data = vec![NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 0,
            rs2_value: 0,
            rd_old_value: 0,
            rd_value: rd_value_in_trace,
            new_pc: 4,
            delegation_type: delegation_type_in_trace,
        },
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_read_timestamp: TimestampData::from_scalar(0),
        rd_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }];

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &dd,
        default_pc_value_in_padding: 4,
    };
    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        dd.to_vec(),
    );

    shift_binop_csrrw_table_addition_fn(&mut cs);
    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        &[],
        TableType::SpecialCSRProperties.to_table_id(),
    );
    cs.add_table_with_content(
        TableType::SpecialCSRProperties,
        LookupWrapper::Dimensional3(csr_table),
    );

    shift_binop_csrrw_circuit_with_preprocessed_bytecode(&mut cs);
    let result = f(cs);
    drop(trace_data);
    drop(dd);
    result
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_csrrw_non_determinism_read() {
    let rd_reg: u8 = 1;
    let rs1_reg: u8 = 0;
    let oracle_value: u32 = 0xCAFE_BABE;

    with_csrrw_cs(
        rd_reg,
        rs1_reg,
        NON_DETERMINISM_CSR,
        oracle_value,
        NON_DETERMINISM_CSR,
        |mut cs| {
            assert!(
                cs.is_satisfied(),
                "CSRRW(non-determinism) constraints not satisfied"
            );

            let regs = extract_circuit_registers(&cs);
            assert_eq!(
                regs[rd_reg as usize], oracle_value,
                "CSRRW: rd write does not match oracle value, got {:#010X}",
                regs[rd_reg as usize]
            );
        },
    );
}

#[test]
fn test_csrrw_rejects_unsupported_csr() {
    const UNSUPPORTED_CSR: u16 = 0xC00; // RV32I cycle CSR

    let rd_reg: u8 = 1;
    let rs1_reg: u8 = 0;

    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_csrrw_cs(
            rd_reg,
            rs1_reg,
            UNSUPPORTED_CSR,
            0,
            // not a non-determinism cycle, so the oracle returns 0 and the rd
            // field is irrelevant - what we want to trip is the CSR table
            // lookup, not value flow.
            0,
            |mut cs| !cs.is_satisfied(),
        )
    }));

    match outcome {
        Ok(rejected) => {
            assert!(
                rejected,
                "CSRRW on an unsupported CSR must be rejected, either by \
                 unsatisfied constraints or by an add-time debug panic"
            );
        }
        Err(_) => {
            // The add-time debug constraint checker may reject this intentionally
            // invalid case via a panic before is_satisfied() runs.
        }
    }
}
