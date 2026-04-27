use super::*;
use super::compliance_vectors;

use cs::machine::ops::unrolled::decoder::WordOnlyMemoryFamilyDecoder;
use cs::machine::ops::unrolled::load_store_word_only::*;

const FAMILY_IDX: u8 = common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;

// RAM addresses must be >= ROM_BYTE_SIZE (0x400000) to be treated as RAM, not ROM.
const RAM_ADDR: u32 = 0x0040_0000;

fn decoder_for_word(encoding: u32) -> Vec<ExecutorFamilyDecoderData> {
    // Word load/store bytecode needs to be ROM_WORD_SIZE entries for the RomRead table.
    let mut bytecode = vec![encoding];
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    bytecode.resize(rom_word_size, 0);

    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[Box::new(WordOnlyMemoryFamilyDecoder)],
        rom_word_size,
        &[],
    );
    let (_, decoder_data) = t.remove(&FAMILY_IDX).expect("decoder data");
    decoder_data
}

fn check_word(
    bytecode: &[u32],
    decoder_data: &[ExecutorFamilyDecoderData],
    case: &MemTestCase,
) {
    let trace_data = vec![case.data];

    let oracle = MemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
    };

    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );

    word_only_load_store_table_addition_fn(&mut cs);
    // Add ROM-specific tables
    let extra_tables = create_word_only_load_store_special_tables::<
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(bytecode);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }

    word_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&mut cs);

    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );
}

// -- Encoding helpers --
// LW x3, imm(x1): opcode=0000011, funct3=010
const fn encode_load(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x03
}

// SW x2, imm(x1): opcode=0100011, funct3=010
const fn encode_store(funct3: u32, rs1: u32, rs2: u32, imm: u32) -> u32 {
    let imm_11_5 = (imm >> 5) & 0x7F;
    let imm_4_0 = imm & 0x1F;
    (imm_11_5 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm_4_0 << 7) | 0x23
}

// LW x3, 0(x1)
const LW: u32 = encode_load(0b010, 3, 1, 0);
// SW x2, 0(x1)
const SW: u32 = encode_store(0b010, 1, 2, 0);

// ==================== LW (load word) ====================

#[test]
fn test_lw_basic() {
    skip_if_ci!();
    let mut bytecode = vec![LW];
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    bytecode.resize(rom_word_size, 0);

    let dd = decoder_for_word(LW);

    check_word(&bytecode, &dd, &MemTestCase {
        label: "LW",
        data: MemoryOpcodeTracingDataWithTimestamp {
            opcode_data: LoadOpcodeTracingData {
                initial_pc: 0,
                rs1_value: RAM_ADDR,         // x1 = RAM base
                aligned_ram_address: RAM_ADDR,
                aligned_ram_read_value: 42,   // memory[RAM_ADDR] = 42
                rd_old_value: 0,
                rd_value: 42,                 // x3 = 42
            },
            discr: MEM_LOAD_TRACE_DATA_MARKER,
            rs1_read_timestamp: TimestampData::from_scalar(0),
            rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
            rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
            cycle_timestamp: TimestampData::from_scalar(4),
        },
    });
}

#[test]
fn test_lw_zero() {
    skip_if_ci!();
    let mut bytecode = vec![LW];
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    bytecode.resize(rom_word_size, 0);

    let dd = decoder_for_word(LW);

    check_word(&bytecode, &dd, &MemTestCase {
        label: "LW",
        data: MemoryOpcodeTracingDataWithTimestamp {
            opcode_data: LoadOpcodeTracingData {
                initial_pc: 0,
                rs1_value: RAM_ADDR,
                aligned_ram_address: RAM_ADDR,
                aligned_ram_read_value: 0,
                rd_old_value: 0,
                rd_value: 0,
            },
            discr: MEM_LOAD_TRACE_DATA_MARKER,
            rs1_read_timestamp: TimestampData::from_scalar(0),
            rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
            rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
            cycle_timestamp: TimestampData::from_scalar(4),
        },
    });
}

// ==================== SW (store word) ====================

#[test]
fn test_sw_basic() {
    skip_if_ci!();
    let mut bytecode = vec![SW];
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    bytecode.resize(rom_word_size, 0);

    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[Box::new(WordOnlyMemoryFamilyDecoder)],
        rom_word_size,
        &[],
    );
    let (_, dd) = t.remove(&FAMILY_IDX).expect("decoder data");

    // SW stores rs2 to memory[rs1 + imm]
    // For StoreOpcodeTracingData, the fields are reinterpreted via transmute:
    // LoadOpcodeTracingData { initial_pc, rs1_value, aligned_ram_address, aligned_ram_read_value, rd_old_value, rd_value }
    // maps to StoreOpcodeTracingData { initial_pc, rs1_value, aligned_ram_address, aligned_ram_old_value, rs2_value, aligned_ram_write_value }
    let store_data = StoreOpcodeTracingData {
        initial_pc: 0,
        rs1_value: RAM_ADDR,
        aligned_ram_address: RAM_ADDR,
        aligned_ram_old_value: 0,       // old memory value
        rs2_value: 99,                   // x2 = 99 (value to store)
        aligned_ram_write_value: 99,     // new memory value = 99
    };

    let data = MemoryOpcodeTracingDataWithTimestamp {
        opcode_data: unsafe { core::mem::transmute(store_data) },
        discr: MEM_STORE_TRACE_DATA_MARKER,
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
        rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    };

    check_word(&bytecode, &dd, &MemTestCase {
        label: "SW",
        data,
    });
}

// ==================== Compliance vector tests ====================

fn check_lw(rd_reg: u8, rs1_reg: u8, ram: u32, rd: u32) {
    let encoding = encode_load(0b010, rd_reg as u32, rs1_reg as u32, 0);
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);
    let dd = decoder_for_word(encoding);
    check_word(
        &bytecode,
        &dd,
        &MemTestCase {
            label: "LW",
            data: MemoryOpcodeTracingDataWithTimestamp {
                opcode_data: LoadOpcodeTracingData {
                    initial_pc: 0,
                    rs1_value: RAM_ADDR,
                    aligned_ram_address: RAM_ADDR,
                    aligned_ram_read_value: ram,
                    rd_old_value: 0,
                    rd_value: rd,
                },
                discr: MEM_LOAD_TRACE_DATA_MARKER,
                rs1_read_timestamp: TimestampData::from_scalar(0),
                rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
                rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
                cycle_timestamp: TimestampData::from_scalar(4),
            },
        },
    );
}

fn check_sw(rs1_reg: u8, rs2_reg: u8, old: u32, rs2_val: u32, new: u32) {
    let encoding = encode_store(0b010, rs1_reg as u32, rs2_reg as u32, 0);
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);
    let dd = decoder_for_word(encoding);

    let store_data = StoreOpcodeTracingData {
        initial_pc: 0,
        rs1_value: RAM_ADDR,
        aligned_ram_address: RAM_ADDR,
        aligned_ram_old_value: old,
        rs2_value: rs2_val,
        aligned_ram_write_value: new,
    };

    check_word(
        &bytecode,
        &dd,
        &MemTestCase {
            label: "SW",
            data: MemoryOpcodeTracingDataWithTimestamp {
                opcode_data: unsafe { core::mem::transmute(store_data) },
                discr: MEM_STORE_TRACE_DATA_MARKER,
                rs1_read_timestamp: TimestampData::from_scalar(0),
                rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
                rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
                cycle_timestamp: TimestampData::from_scalar(4),
            },
        },
    );
}

#[test]
fn test_lw_compliance() {
    skip_if_ci!();
    for &(rd_reg, rs1_reg, ram, rd) in compliance_vectors::LW_VECTORS {
        check_lw(rd_reg, rs1_reg, ram, rd);
    }
}

#[test]
fn test_sw_compliance() {
    skip_if_ci!();
    for &(rs1_reg, rs2_reg, old, rs2_val, new) in compliance_vectors::SW_VECTORS {
        check_sw(rs1_reg, rs2_reg, old, rs2_val, new);
    }
}
