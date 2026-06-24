use super::compliance_vectors;
use super::*;

use cs::machine::ops::unrolled::decoder::SubwordOnlyMemoryFamilyDecoder;
use cs::machine::ops::unrolled::load_store::create_load_store_special_tables;
use cs::machine::ops::unrolled::load_store_subword_only::*;

const FAMILY_IDX: u8 =
    common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
const RAM_ADDR: u32 = common_constants::rom::ROM_BYTE_SIZE as u32;

use super::encoding::{encode_load, encode_store};

// LB x3, 0(x1)  funct3=000
const LB: u32 = encode_load(0b000, 3, 1, 0);
// LH x3, 0(x1)  funct3=001
const LH: u32 = encode_load(0b001, 3, 1, 0);
// LBU x3, 0(x1) funct3=100
const LBU: u32 = encode_load(0b100, 3, 1, 0);
// LHU x3, 0(x1) funct3=101
const LHU: u32 = encode_load(0b101, 3, 1, 0);
// SB x2, 0(x1)  funct3=000
const SB: u32 = encode_store(0b000, 1, 2, 0);
// SH x2, 0(x1)  funct3=001
const SH: u32 = encode_store(0b001, 1, 2, 0);

fn decoder_for_subword(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[Box::new(SubwordOnlyMemoryFamilyDecoder)],
        rom_word_size,
        &[],
    );
    let (_, decoder_data) = t.remove(&FAMILY_IDX).expect("decoder data");
    decoder_data
}

fn check_subword_load(encoding: u32, ram_value: u32, rd_value: u32) {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let dd = decoder_for_subword(encoding);

    let trace_data = vec![MemoryOpcodeTracingDataWithTimestamp {
        opcode_data: LoadOpcodeTracingData {
            initial_pc: 0,
            rs1_value: RAM_ADDR,
            aligned_ram_address: RAM_ADDR,
            aligned_ram_read_value: ram_value,
            rd_old_value: 0,
            rd_value,
        },
        discr: MEM_LOAD_TRACE_DATA_MARKER,
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
        rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }];

    let oracle = MemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &dd,
    };
    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        dd.to_vec(),
    );

    subword_only_load_store_table_addition_fn(&mut cs);
    let extra_tables = create_load_store_special_tables::<
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&bytecode);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    subword_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&mut cs);

    assert!(cs.is_satisfied(), "Subword load constraints NOT satisfied");
}

fn check_subword_store(encoding: u32, old_ram_value: u32, rs2_value: u32, new_ram_value: u32) {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let dd = decoder_for_subword(encoding);

    let store_data = StoreOpcodeTracingData {
        initial_pc: 0,
        rs1_value: RAM_ADDR,
        aligned_ram_address: RAM_ADDR,
        aligned_ram_old_value: old_ram_value,
        rs2_value,
        aligned_ram_write_value: new_ram_value,
    };

    let trace_data = vec![MemoryOpcodeTracingDataWithTimestamp {
        opcode_data: unsafe { core::mem::transmute(store_data) },
        discr: MEM_STORE_TRACE_DATA_MARKER,
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
        rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }];

    let oracle = MemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &dd,
    };
    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        dd.to_vec(),
    );

    subword_only_load_store_table_addition_fn(&mut cs);
    let extra_tables = create_load_store_special_tables::<
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&bytecode);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    subword_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&mut cs);

    assert!(cs.is_satisfied(), "Subword store constraints NOT satisfied");
}

// ==================== LB (load byte, sign-extend) ====================

// These direct one-row satisfiability checks do not exercise the same witness
// path as the end-to-end unrolled/transpiler tests for subword loads.
#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lb_positive_byte() {
    check_subword_load(LB, 0x00000012, 0x00000012);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lb_sign_extend_0x80() {
    check_subword_load(LB, 0x00000080, 0xFFFFFF80);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lb_sign_extend_0xff() {
    check_subword_load(LB, 0x000000FF, 0xFFFFFFFF);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lb_extracts_low_byte() {
    check_subword_load(LB, 0x12345678, 0x00000078);
}

// ==================== LBU (load byte, zero-extend) ====================

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lbu_ff() {
    check_subword_load(LBU, 0x000000FF, 0x000000FF);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lbu_no_sign_extend() {
    check_subword_load(LBU, 0x00000080, 0x00000080);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lbu_extracts_low_byte() {
    check_subword_load(LBU, 0x12345678, 0x00000078);
}

// ==================== LH (load halfword, sign-extend) ====================

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lh_positive_halfword() {
    check_subword_load(LH, 0x00001234, 0x00001234);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lh_sign_extend_0x8000() {
    check_subword_load(LH, 0x00008000, 0xFFFF8000);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lh_sign_extend_0xffff() {
    check_subword_load(LH, 0x0000FFFF, 0xFFFFFFFF);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lh_extracts_low_halfword() {
    check_subword_load(LH, 0x12345678, 0x00005678);
}

// ==================== LHU (load halfword, zero-extend) ====================

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lhu_ffff() {
    check_subword_load(LHU, 0x0000FFFF, 0x0000FFFF);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lhu_no_sign_extend() {
    check_subword_load(LHU, 0x00008000, 0x00008000);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lhu_extracts_low_halfword() {
    check_subword_load(LHU, 0x12345678, 0x00005678);
}

// ==================== SB (store byte) ====================

#[test]
fn test_sb_into_nonzero_word() {
    check_subword_store(SB, 0x12345678, 0xAB, 0x123456AB);
}

#[test]
fn test_sb_ff_into_zero() {
    check_subword_store(SB, 0x00000000, 0xFF, 0x000000FF);
}

#[test]
fn test_sb_zero_into_ones() {
    check_subword_store(SB, 0xFFFFFFFF, 0x00, 0xFFFFFF00);
}

// ==================== SH (store halfword) ====================

#[test]
fn test_sh_into_nonzero_word() {
    check_subword_store(SH, 0x12345678, 0xABCD, 0x1234ABCD);
}

#[test]
fn test_sh_ffff_into_zero() {
    check_subword_store(SH, 0x00000000, 0xFFFF, 0x0000FFFF);
}

#[test]
fn test_sh_zero_into_ones() {
    check_subword_store(SH, 0xFFFFFFFF, 0x0000, 0xFFFF0000);
}

// ==================== Compliance vector tests ====================

fn run_load_compliance(funct3: u32, vectors: &[(u8, u8, u32, u32)]) {
    for &(rd_reg, rs1_reg, ram, rd) in vectors {
        let encoding = encode_load(funct3, rd_reg as u32, rs1_reg as u32, 0);
        check_subword_load(encoding, ram, rd);
    }
}

fn run_store_compliance(funct3: u32, vectors: &[(u8, u8, u32, u32, u32)]) {
    for &(rs1_reg, rs2_reg, old, rs2_val, new) in vectors {
        let encoding = encode_store(funct3, rs1_reg as u32, rs2_reg as u32, 0);
        check_subword_store(encoding, old, rs2_val, new);
    }
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lb_compliance() {
    run_load_compliance(0b000, compliance_vectors::LB_VECTORS);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lbu_compliance() {
    run_load_compliance(0b100, compliance_vectors::LBU_VECTORS);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lh_compliance() {
    run_load_compliance(0b001, compliance_vectors::LH_VECTORS);
}

#[test]
#[ignore = "covered by with_transpiler end-to-end tests"]
fn test_lhu_compliance() {
    run_load_compliance(0b101, compliance_vectors::LHU_VECTORS);
}

#[test]
fn test_sb_compliance() {
    run_store_compliance(0b000, compliance_vectors::SB_VECTORS);
}

#[test]
fn test_sh_compliance() {
    run_store_compliance(0b001, compliance_vectors::SH_VECTORS);
}
