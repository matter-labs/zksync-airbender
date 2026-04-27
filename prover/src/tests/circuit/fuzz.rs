use super::*;

use cs::cs::oracle::ExecutorFamilyDecoderData;
use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
use cs::machine::ops::unrolled::decoder::{
    AddSubLuiAuipcMopDecoder, DivMulDecoder, JumpSltBranchDecoder,
    ShiftBinaryCsrrwDecoder, SubwordOnlyMemoryFamilyDecoder, WordOnlyMemoryFamilyDecoder,
    process_binary_into_separate_tables_ext,
};
use cs::machine::ops::unrolled::jump_branch_slt::*;
use cs::machine::ops::unrolled::load_store_subword_only::*;
use cs::machine::ops::unrolled::load_store_word_only::*;
use cs::machine::ops::unrolled::load_store::create_load_store_special_tables;
use cs::machine::ops::unrolled::mul_div::*;
use cs::machine::ops::unrolled::shift_binary_csr::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::alloc::Global;

// ==================== RISC-V Encoding Helpers ====================

const fn encode_r(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x33
}

const fn encode_r_system(funct3: u32, funct7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x73
}

const fn encode_u(opcode: u32, rd: u32, imm_upper: u32) -> u32 {
    (imm_upper << 12) | (rd << 7) | opcode
}

const fn encode_i(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

const fn encode_i_shift(funct3: u32, funct7: u32, rd: u32, rs1: u32, shamt: u32) -> u32 {
    (funct7 << 25) | (shamt << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x13
}

fn sign_extend_12(imm: u32) -> u32 {
    if imm & 0x800 != 0 {
        imm | 0xFFFFF000
    } else {
        imm
    }
}

// ==================== Instruction Definitions ====================

struct InstrDef {
    name: &'static str,
    encoding: u32,
    family: Family,
    eval: fn(u32, u32) -> u32,
}

struct ITypeInstrDef {
    name: &'static str,
    family: Family,
    /// Build the encoding given a 12-bit immediate (or 5-bit shamt for shifts).
    encode: fn(u32) -> u32,
    /// Evaluate: (rs1, sign-extended-imm-or-shamt) -> rd
    eval: fn(u32, u32) -> u32,
    /// true for SLLI/SRLI/SRAI where the operand is a 5-bit shamt
    is_shift: bool,
}

struct UTypeInstrDef {
    name: &'static str,
    family: Family,
    /// Build the encoding given a 20-bit upper immediate.
    encode: fn(u32) -> u32,
    /// Evaluate: (imm_upper) -> rd. For LUI: rd = imm << 12. For AUIPC: rd = PC + (imm << 12).
    /// PC is always 0 in our test harness, so AUIPC also gives imm << 12.
    eval: fn(u32) -> u32,
}

#[derive(Clone, Copy)]
enum Family {
    AddSub,
    JumpSlt,
    ShiftBinop,
    MulDiv,
    LoadStoreWord,
    LoadStoreSubword,
}

const P: u64 = (1u64 << 31) - 1;

fn add_sub_instructions() -> Vec<InstrDef> {
    vec![
        InstrDef {
            name: "ADD",
            encoding: encode_r(0b000, 0b0000000, 3, 1, 2),
            family: Family::AddSub,
            eval: |a, b| a.wrapping_add(b),
        },
        InstrDef {
            name: "SUB",
            encoding: encode_r(0b000, 0b0100000, 3, 1, 2),
            family: Family::AddSub,
            eval: |a, b| a.wrapping_sub(b),
        },
        InstrDef {
            name: "ADDMOD",
            encoding: encode_r_system(0b100, 0b1000001, 3, 1, 2),
            family: Family::AddSub,
            eval: |a, b| ((a as u64 + b as u64) % P) as u32,
        },
        InstrDef {
            name: "SUBMOD",
            encoding: encode_r_system(0b100, 0b1000011, 3, 1, 2),
            family: Family::AddSub,
            eval: |a, b| ((a as u64 + P - (b as u64 % P)) % P) as u32,
        },
    ]
}

fn slt_instructions() -> Vec<InstrDef> {
    vec![
        InstrDef {
            name: "SLT",
            encoding: encode_r(0b010, 0b0000000, 3, 1, 2),
            family: Family::JumpSlt,
            eval: |a, b| if (a as i32) < (b as i32) { 1 } else { 0 },
        },
        InstrDef {
            name: "SLTU",
            encoding: encode_r(0b011, 0b0000000, 3, 1, 2),
            family: Family::JumpSlt,
            eval: |a, b| if a < b { 1 } else { 0 },
        },
    ]
}

fn shift_binop_instructions() -> Vec<InstrDef> {
    vec![
        InstrDef {
            name: "SLL",
            encoding: encode_r(0b001, 0b0000000, 3, 1, 2),
            family: Family::ShiftBinop,
            eval: |a, b| a << (b & 0x1F),
        },
        InstrDef {
            name: "SRL",
            encoding: encode_r(0b101, 0b0000000, 3, 1, 2),
            family: Family::ShiftBinop,
            eval: |a, b| a >> (b & 0x1F),
        },
        InstrDef {
            name: "SRA",
            encoding: encode_r(0b101, 0b0100000, 3, 1, 2),
            family: Family::ShiftBinop,
            eval: |a, b| ((a as i32) >> (b & 0x1F)) as u32,
        },
        InstrDef {
            name: "XOR",
            encoding: encode_r(0b100, 0b0000000, 3, 1, 2),
            family: Family::ShiftBinop,
            eval: |a, b| a ^ b,
        },
        InstrDef {
            name: "AND",
            encoding: encode_r(0b111, 0b0000000, 3, 1, 2),
            family: Family::ShiftBinop,
            eval: |a, b| a & b,
        },
        InstrDef {
            name: "OR",
            encoding: encode_r(0b110, 0b0000000, 3, 1, 2),
            family: Family::ShiftBinop,
            eval: |a, b| a | b,
        },
    ]
}

fn mul_div_instructions() -> Vec<InstrDef> {
    vec![
        InstrDef {
            name: "MUL",
            encoding: encode_r(0b000, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| a.wrapping_mul(b),
        },
        InstrDef {
            name: "MULH",
            encoding: encode_r(0b001, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| ((a as i32 as i64).wrapping_mul(b as i32 as i64) >> 32) as u32,
        },
        InstrDef {
            name: "MULHSU",
            encoding: encode_r(0b010, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| ((a as i32 as i64).wrapping_mul(b as u64 as i64) >> 32) as u32,
        },
        InstrDef {
            name: "MULHU",
            encoding: encode_r(0b011, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| ((a as u64).wrapping_mul(b as u64) >> 32) as u32,
        },
        InstrDef {
            name: "DIV",
            encoding: encode_r(0b100, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| {
                let (a_s, b_s) = (a as i32, b as i32);
                if b_s == 0 {
                    0xFFFF_FFFF
                } else if a_s == i32::MIN && b_s == -1 {
                    i32::MIN as u32
                } else {
                    a_s.wrapping_div(b_s) as u32
                }
            },
        },
        InstrDef {
            name: "DIVU",
            encoding: encode_r(0b101, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| if b == 0 { 0xFFFF_FFFF } else { a / b },
        },
        InstrDef {
            name: "REM",
            encoding: encode_r(0b110, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| {
                let (a_s, b_s) = (a as i32, b as i32);
                if b_s == 0 {
                    a
                } else if a_s == i32::MIN && b_s == -1 {
                    0
                } else {
                    a_s.wrapping_rem(b_s) as u32
                }
            },
        },
        InstrDef {
            name: "REMU",
            encoding: encode_r(0b111, 0b0000001, 3, 1, 2),
            family: Family::MulDiv,
            eval: |a, b| if b == 0 { a } else { a % b },
        },
    ]
}

fn i_type_instructions() -> Vec<ITypeInstrDef> {
    vec![
        ITypeInstrDef {
            name: "ADDI",
            family: Family::AddSub,
            encode: |imm| encode_i(0b000, 3, 1, imm),
            eval: |a, imm| a.wrapping_add(imm),
            is_shift: false,
        },
        ITypeInstrDef {
            name: "XORI",
            family: Family::ShiftBinop,
            encode: |imm| encode_i(0b100, 3, 1, imm),
            eval: |a, imm| a ^ imm,
            is_shift: false,
        },
        ITypeInstrDef {
            name: "ORI",
            family: Family::ShiftBinop,
            encode: |imm| encode_i(0b110, 3, 1, imm),
            eval: |a, imm| a | imm,
            is_shift: false,
        },
        ITypeInstrDef {
            name: "ANDI",
            family: Family::ShiftBinop,
            encode: |imm| encode_i(0b111, 3, 1, imm),
            eval: |a, imm| a & imm,
            is_shift: false,
        },
        ITypeInstrDef {
            name: "SLLI",
            family: Family::ShiftBinop,
            encode: |shamt| encode_i_shift(0b001, 0b0000000, 3, 1, shamt),
            eval: |a, shamt| a << shamt,
            is_shift: true,
        },
        ITypeInstrDef {
            name: "SRLI",
            family: Family::ShiftBinop,
            encode: |shamt| encode_i_shift(0b101, 0b0000000, 3, 1, shamt),
            eval: |a, shamt| a >> shamt,
            is_shift: true,
        },
        ITypeInstrDef {
            name: "SRAI",
            family: Family::ShiftBinop,
            encode: |shamt| encode_i_shift(0b101, 0b0100000, 3, 1, shamt),
            eval: |a, shamt| ((a as i32) >> shamt) as u32,
            is_shift: true,
        },
    ]
}

// Instructions NOT fuzzed and why:
//
// Family 2 (JumpSltBranch) — ALL excluded:
//   SLT, SLTU, SLTI, SLTIU, JAL, JALR, BEQ, BNE, BLT, BGE, BLTU, BGEU
//   Reason: is_satisfied() panics on unresolved witness variables because the
//   jump/branch circuit sets up witness for all opcodes even when only one is used.
//   These can only be tested via the full witness evaluator + prover pipeline.
//
// Family 1 (AddSub):
//   MULMOD — excluded because BasicAssembly cannot resolve degree-2 witness
//   from modular multiplication. Must be tested via full prover pipeline.
//
// Family 3 (ShiftBinop):
//   CSRRW — excluded because it requires supported_csrs configuration and
//   interacts with special CSR state, not just register-to-register computation.

fn u_type_instructions() -> Vec<UTypeInstrDef> {
    vec![
        UTypeInstrDef {
            name: "LUI",
            family: Family::AddSub,
            encode: |imm_upper| encode_u(0x37, 3, imm_upper),
            eval: |imm_upper| imm_upper << 12,
        },
        UTypeInstrDef {
            name: "AUIPC",
            family: Family::AddSub,
            // PC is always 0 in our test harness, so rd = 0 + (imm << 12)
            encode: |imm_upper| encode_u(0x17, 3, imm_upper),
            eval: |imm_upper| imm_upper << 12,
        },
    ]
}

// ==================== Input Generation ====================

const INTERESTING_VALUES: [u32; 12] = [
    0,
    1,
    2,
    31,             // max shift amount
    32,             // shift amount boundary
    u32::MAX,
    u32::MAX - 1,
    0x8000_0000,    // i32::MIN
    0x7FFF_FFFF,    // i32::MAX
    0x0000_FFFF,
    0xFFFF_0000,
    0x4000_0000,    // bit 30, Mersenne prime boundary
];

/// ~30% chance of picking an edge case, ~70% fully random.
fn random_input(rng: &mut impl Rng) -> u32 {
    if rng.random_ratio(3, 10) {
        INTERESTING_VALUES[rng.random_range(0..INTERESTING_VALUES.len())]
    } else {
        rng.random()
    }
}

fn random_mersenne_input(rng: &mut impl Rng) -> u32 {
    rng.random_range(0..((1u32 << 31) - 1))
}

// ==================== Seed Configuration ====================

fn get_fuzz_seed(default: u64) -> u64 {
    std::env::var("FUZZ_SEED")
        .ok()
        .and_then(|s| {
            s.strip_prefix("0x")
                .map(|hex| u64::from_str_radix(hex, 16).ok())
                .unwrap_or_else(|| s.parse().ok())
        })
        .unwrap_or(default)
}

// ==================== Per-Family Circuit Runners ====================

struct CachedDecoder {
    decoder_data: Vec<ExecutorFamilyDecoderData>,
    family: Family,
}

fn build_decoder(instr: &InstrDef) -> CachedDecoder {
    let encoding = instr.encoding;
    build_decoder_for_family(encoding, instr.family)
}

fn build_decoder_for_family(encoding: u32, family: Family) -> CachedDecoder {
    match family {
        Family::LoadStoreWord | Family::LoadStoreSubword => {
            build_mem_decoder(encoding, family)
        }
        _ => {
            let (decoder, family_idx): (
                Box<dyn cs::machine::ops::unrolled::decoder::OpcodeFamilyDecoder>,
                u8,
            ) = match family {
                Family::AddSub => (
                    Box::new(AddSubLuiAuipcMopDecoder),
                    common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
                ),
                Family::MulDiv => (
                    Box::new(DivMulDecoder::<true>),
                    common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX,
                ),
                Family::ShiftBinop => (
                    Box::new(ShiftBinaryCsrrwDecoder),
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX,
                ),
                Family::JumpSlt => (
                    Box::new(JumpSltBranchDecoder::<true>),
                    common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
                ),
                _ => unreachable!(),
            };
            let decoder_data = prepare_decoder_data(encoding, decoder, family_idx, &[]);
            CachedDecoder {
                decoder_data,
                family,
            }
        }
    }
}

/// Memory families need ROM-sized bytecode for the decoder preprocessing.
fn build_mem_decoder(encoding: u32, family: Family) -> CachedDecoder {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let (decoder, family_idx): (
        Box<dyn cs::machine::ops::unrolled::decoder::OpcodeFamilyDecoder>,
        u8,
    ) = match family {
        Family::LoadStoreWord => (
            Box::new(WordOnlyMemoryFamilyDecoder),
            common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
        ),
        Family::LoadStoreSubword => (
            Box::new(SubwordOnlyMemoryFamilyDecoder),
            common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
        ),
        _ => unreachable!(),
    };

    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[decoder],
        rom_word_size,
        &[],
    );
    let (_, decoder_data) = t.remove(&family_idx).expect("decoder data");
    CachedDecoder {
        decoder_data,
        family,
    }
}

/// Run the circuit and return whether constraints are satisfied.
/// Does NOT panic on unsatisfied -- returns false instead.
fn check_case_satisfied(cached: &CachedDecoder, case: &NonMemTestCase) -> bool {
    let trace_data = make_trace_data(case);

    let default_pc_value_in_padding = match cached.family {
        Family::JumpSlt => 0,
        _ => 4,
    };

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &cached.decoder_data,
        default_pc_value_in_padding,
    };

    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        cached.decoder_data.to_vec(),
    );

    match cached.family {
        Family::AddSub => {
            add_sub_lui_auipc_mop_table_addition_fn(&mut cs);
            add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(&mut cs);
        }
        Family::MulDiv => {
            mul_div_table_addition_fn(&mut cs);
            mul_div_circuit_with_preprocessed_bytecode::<_, _, true>(&mut cs);
        }
        Family::ShiftBinop => {
            shift_binop_csrrw_table_addition_fn(&mut cs);
            shift_binop_csrrw_circuit_with_preprocessed_bytecode(&mut cs);
        }
        Family::JumpSlt => {
            jump_branch_slt_table_addition_fn(&mut cs);
            jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(&mut cs);
        }
        Family::LoadStoreWord | Family::LoadStoreSubword => {
            unreachable!("use check_mem_case_satisfied for memory families");
        }
    }

    cs.is_satisfied()
}

// RAM addresses must be >= ROM_BYTE_SIZE to be treated as RAM, not ROM.
const RAM_ADDR: u32 = common_constants::rom::ROM_BYTE_SIZE as u32;

/// Run a load-word circuit and return whether constraints are satisfied.
fn check_lw_satisfied(encoding: u32, value: u32) -> bool {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let cached = build_mem_decoder(encoding, Family::LoadStoreWord);

    let trace_data = vec![MemoryOpcodeTracingDataWithTimestamp {
        opcode_data: LoadOpcodeTracingData {
            initial_pc: 0,
            rs1_value: RAM_ADDR,
            aligned_ram_address: RAM_ADDR,
            aligned_ram_read_value: value,
            rd_old_value: 0,
            rd_value: value,
        },
        discr: MEM_LOAD_TRACE_DATA_MARKER,
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_or_ram_read_timestamp: TimestampData::from_scalar(0),
        rd_or_ram_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }];

    let oracle = MemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &cached.decoder_data,
    };

    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        cached.decoder_data.to_vec(),
    );

    word_only_load_store_table_addition_fn(&mut cs);
    let extra_tables = create_word_only_load_store_special_tables::<
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&bytecode);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    word_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&mut cs);

    cs.is_satisfied()
}

/// Run a store-word circuit and return whether constraints are satisfied.
fn check_sw_satisfied(encoding: u32, old_value: u32, new_value: u32) -> bool {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let cached = build_mem_decoder(encoding, Family::LoadStoreWord);

    let store_data = StoreOpcodeTracingData {
        initial_pc: 0,
        rs1_value: RAM_ADDR,
        aligned_ram_address: RAM_ADDR,
        aligned_ram_old_value: old_value,
        rs2_value: new_value,
        aligned_ram_write_value: new_value,
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
        decoder_table: &cached.decoder_data,
    };

    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        cached.decoder_data.to_vec(),
    );

    word_only_load_store_table_addition_fn(&mut cs);
    let extra_tables = create_word_only_load_store_special_tables::<
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&bytecode);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    word_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&mut cs);

    cs.is_satisfied()
}

/// Run a subword load circuit and return whether constraints are satisfied.
fn check_subword_load_satisfied(
    encoding: u32,
    ram_value: u32,
    rd_value: u32,
) -> bool {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let cached = build_mem_decoder(encoding, Family::LoadStoreSubword);

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
        decoder_table: &cached.decoder_data,
    };

    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        cached.decoder_data.to_vec(),
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

    cs.is_satisfied()
}

/// Run a subword store circuit and return whether constraints are satisfied.
fn check_subword_store_satisfied(
    encoding: u32,
    old_ram_value: u32,
    rs2_value: u32,
    new_ram_value: u32,
) -> bool {
    let rom_word_size = common_constants::rom::ROM_BYTE_SIZE / 4;
    let mut bytecode = vec![encoding];
    bytecode.resize(rom_word_size, 0);

    let cached = build_mem_decoder(encoding, Family::LoadStoreSubword);

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
        decoder_table: &cached.decoder_data,
    };

    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        cached.decoder_data.to_vec(),
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

    cs.is_satisfied()
}

// ==================== Fuzz Tests ====================
//
// All fuzz tests run forever until they hit a failure.
// Run with: cargo test -p prover --features "prover,cs_debug" -- fuzz_ --nocapture

fn fuzz_r_type_instructions(instructions: &[InstrDef], seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    eprintln!("fuzz seed: 0x{:016X}", seed);

    let mut iteration: u64 = 0;
    loop {
        for instr in instructions {
            let cached = build_decoder(instr);
            let is_mersenne_op = instr.name == "ADDMOD" || instr.name == "SUBMOD";
            let rs1 = if is_mersenne_op {
                random_mersenne_input(&mut rng)
            } else {
                random_input(&mut rng)
            };
            let rs2 = if is_mersenne_op {
                random_mersenne_input(&mut rng)
            } else {
                random_input(&mut rng)
            };
            let rd = (instr.eval)(rs1, rs2);

            let case = NonMemTestCase {
                label: instr.name,
                rs1,
                rs2,
                rd,
            };
            assert!(
                check_case_satisfied(&cached, &case),
                "FUZZ POSITIVE FAILURE: {} iteration {}\n  \
                 rs1 = 0x{:08X} (signed: {})\n  \
                 rs2 = 0x{:08X} (signed: {})\n  \
                 expected rd = 0x{:08X} (signed: {})\n  \
                 Reproduce: FUZZ_SEED=0x{:016X}",
                instr.name,
                iteration,
                rs1,
                rs1 as i32,
                rs2,
                rs2 as i32,
                rd,
                rd as i32,
                seed,
            );
        }
        iteration += 1;
        if iteration % 1000 == 0 {
            eprintln!("[fuzz_r_type] {} iterations completed", iteration);
        }
    }
}

/// Positive fuzz for ADD/SUB/ADDMOD/SUBMOD (Family 1 R-type).
#[test]
fn fuzz_add_sub() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0001);
    fuzz_r_type_instructions(&add_sub_instructions(), seed);
}

/// Positive fuzz for SLT/SLTU (Family 2 - JumpSlt).
///
/// NOTE: The jump/branch/SLT circuit has unresolved witness variables that cause
/// `is_satisfied()` to panic (not just return false). This is because the circuit
/// sets up witness for all jump/branch logic even when only SLT is used.
/// SLT/SLTU can only be soundness-tested via the full witness evaluator path.
#[test]
#[ignore = "JumpSltBranch circuit has unresolvable witness variables in BasicAssembly debug evaluator"]
fn fuzz_slt() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0002);
    fuzz_r_type_instructions(&slt_instructions(), seed);
}

/// Positive fuzz for SLL/SRL/SRA/XOR/AND/OR (Family 3 R-type).
#[test]
fn fuzz_shift_binop() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0003);
    fuzz_r_type_instructions(&shift_binop_instructions(), seed);
}

/// Positive fuzz for MUL/MULH/MULHSU/MULHU/DIV/DIVU/REM/REMU (Family 4).
#[test]
fn fuzz_mul_div() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0004);
    fuzz_r_type_instructions(&mul_div_instructions(), seed);
}

/// Positive fuzz for I-type immediate instructions: ADDI, XORI, ORI, ANDI,
/// SLLI, SRLI, SRAI.
///
/// For each random immediate, we re-encode the instruction and rebuild the
/// decoder, since the immediate is embedded in the instruction encoding and
/// thus baked into the preprocessed decoder table.
#[test]
fn fuzz_i_type() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0005);
    let mut rng = StdRng::seed_from_u64(seed);
    eprintln!("fuzz seed: 0x{:016X}", seed);

    let instructions = i_type_instructions();

    let mut iteration: u64 = 0;
    loop {
        for instr in &instructions {
            let rs1 = random_input(&mut rng);

            let (raw_imm, eval_operand) = if instr.is_shift {
                let shamt = rng.random_range(0..32u32);
                (shamt, shamt)
            } else {
                let imm12 = rng.random_range(0..0x1000u32);
                (imm12, sign_extend_12(imm12))
            };

            let encoding = (instr.encode)(raw_imm);
            let cached = build_decoder_for_family(encoding, instr.family);

            let rd = (instr.eval)(rs1, eval_operand);

            let case = NonMemTestCase {
                label: instr.name,
                rs1,
                rs2: 0,
                rd,
            };
            assert!(
                check_case_satisfied(&cached, &case),
                "FUZZ I-TYPE POSITIVE FAILURE: {} iteration {}\n  \
                 rs1 = 0x{:08X} (signed: {})\n  \
                 imm/shamt = 0x{:03X} (sign-extended: 0x{:08X})\n  \
                 expected rd = 0x{:08X} (signed: {})\n  \
                 Reproduce: FUZZ_SEED=0x{:016X}",
                instr.name,
                iteration,
                rs1,
                rs1 as i32,
                raw_imm,
                eval_operand,
                rd,
                rd as i32,
                seed,
            );
        }
        iteration += 1;
        if iteration % 1000 == 0 {
            eprintln!("[fuzz_i_type] {} iterations completed", iteration);
        }
    }
}

/// Positive fuzz for U-type instructions: LUI, AUIPC.
///
/// These use a 20-bit upper immediate. For each iteration we generate a random
/// upper immediate, encode it, rebuild the decoder, and check the circuit.
/// rs1 and rs2 are unused (set to 0) since U-type only writes rd = imm << 12.
#[test]
fn fuzz_u_type() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0006);
    let mut rng = StdRng::seed_from_u64(seed);
    eprintln!("fuzz seed: 0x{:016X}", seed);

    let instructions = u_type_instructions();

    let mut iteration: u64 = 0;
    loop {
        for instr in &instructions {
            let imm_upper = rng.random_range(0..(1u32 << 20));
            let encoding = (instr.encode)(imm_upper);
            let cached = build_decoder_for_family(encoding, instr.family);

            let rd = (instr.eval)(imm_upper);

            let case = NonMemTestCase {
                label: instr.name,
                rs1: 0,
                rs2: 0,
                rd,
            };
            assert!(
                check_case_satisfied(&cached, &case),
                "FUZZ U-TYPE POSITIVE FAILURE: {} iteration {}\n  \
                 imm_upper = 0x{:05X}\n  \
                 expected rd = 0x{:08X}\n  \
                 Reproduce: FUZZ_SEED=0x{:016X}",
                instr.name,
                iteration,
                imm_upper,
                rd,
                seed,
            );
        }
        iteration += 1;
        if iteration % 1000 == 0 {
            eprintln!("[fuzz_u_type] {} iterations completed", iteration);
        }
    }
}

// ==================== Load/Store Encoding Helpers ====================

const fn encode_load(funct3: u32, rd: u32, rs1: u32, imm: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0x03
}

const fn encode_store(funct3: u32, rs1: u32, rs2: u32, imm: u32) -> u32 {
    let imm_11_5 = (imm >> 5) & 0x7F;
    let imm_4_0 = imm & 0x1F;
    (imm_11_5 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm_4_0 << 7) | 0x23
}

// LW x3, 0(x1) / SW x2, 0(x1)
const LW_ENC: u32 = encode_load(0b010, 3, 1, 0);
const SW_ENC: u32 = encode_store(0b010, 1, 2, 0);

// Subword loads: LB, LH, LBU, LHU (all with imm=0, rd=x3, rs1=x1)
const LB_ENC: u32 = encode_load(0b000, 3, 1, 0);
const LH_ENC: u32 = encode_load(0b001, 3, 1, 0);
const LBU_ENC: u32 = encode_load(0b100, 3, 1, 0);
const LHU_ENC: u32 = encode_load(0b101, 3, 1, 0);

// Subword stores: SB, SH (all with imm=0, rs1=x1, rs2=x2)
const SB_ENC: u32 = encode_store(0b000, 1, 2, 0);
const SH_ENC: u32 = encode_store(0b001, 1, 2, 0);

/// Positive fuzz for LW and SW (Family 16 - word-only load/store).
///
/// LW: loads a 32-bit word from aligned RAM address into rd.
/// SW: stores a 32-bit word from rs2 into aligned RAM address.
#[test]
fn fuzz_load_store_word() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0007);
    let mut rng = StdRng::seed_from_u64(seed);
    eprintln!("fuzz seed: 0x{:016X}", seed);

    let mut iteration: u64 = 0;
    loop {
        // LW: random value loaded from memory
        let value: u32 = rng.random();
        assert!(
            check_lw_satisfied(LW_ENC, value),
            "FUZZ LW FAILURE iteration {}\n  value = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, value, seed,
        );

        // SW: random old value, random new value stored
        let old_value: u32 = rng.random();
        let new_value: u32 = rng.random();
        assert!(
            check_sw_satisfied(SW_ENC, old_value, new_value),
            "FUZZ SW FAILURE iteration {}\n  old = 0x{:08X}, new = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, old_value, new_value, seed,
        );

        iteration += 1;
        if iteration % 1000 == 0 {
            eprintln!("[fuzz_load_store_word] {} iterations completed", iteration);
        }
    }
}

/// Positive fuzz for LB, LH, LBU, LHU, SB, SH (Family 17 - subword load/store).
///
/// Subword loads read a full 32-bit word from aligned memory, then extract/sign-extend
/// the appropriate byte or halfword. Subword stores merge a byte/halfword into the
/// existing word at the aligned address.
///
/// All addresses are word-aligned (offset=0 within the word) for simplicity.
///
/// NOTE: The subword load/store circuit has complex witness resolution that the
/// BasicAssembly debug evaluator cannot fully resolve, causing constraint failures
/// even for correct inputs. Must be tested via the full witness evaluator path.
#[test]
#[ignore = "subword load/store circuit has unresolvable witness variables in BasicAssembly debug evaluator"]
fn fuzz_load_store_subword() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xDEAD_BEEF_CAFE_0008);
    let mut rng = StdRng::seed_from_u64(seed);
    eprintln!("fuzz seed: 0x{:016X}", seed);

    let mut iteration: u64 = 0;
    loop {
        let ram_value: u32 = rng.random();
        let rs2_value: u32 = rng.random();

        // Subword loads from byte offset 0 within the aligned word:
        // LB: sign-extend byte 0
        let lb_rd = ((ram_value & 0xFF) as i8) as u32;
        assert!(
            check_subword_load_satisfied(LB_ENC, ram_value, lb_rd),
            "FUZZ LB FAILURE iteration {}\n  ram = 0x{:08X}, rd = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, ram_value, lb_rd, seed,
        );

        // LBU: zero-extend byte 0
        let lbu_rd = ram_value & 0xFF;
        assert!(
            check_subword_load_satisfied(LBU_ENC, ram_value, lbu_rd),
            "FUZZ LBU FAILURE iteration {}\n  ram = 0x{:08X}, rd = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, ram_value, lbu_rd, seed,
        );

        // LH: sign-extend halfword 0
        let lh_rd = ((ram_value & 0xFFFF) as i16) as u32;
        assert!(
            check_subword_load_satisfied(LH_ENC, ram_value, lh_rd),
            "FUZZ LH FAILURE iteration {}\n  ram = 0x{:08X}, rd = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, ram_value, lh_rd, seed,
        );

        // LHU: zero-extend halfword 0
        let lhu_rd = ram_value & 0xFFFF;
        assert!(
            check_subword_load_satisfied(LHU_ENC, ram_value, lhu_rd),
            "FUZZ LHU FAILURE iteration {}\n  ram = 0x{:08X}, rd = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, ram_value, lhu_rd, seed,
        );

        // SB: store low byte of rs2, preserve rest of word
        let sb_new = (ram_value & 0xFFFFFF00) | (rs2_value & 0xFF);
        assert!(
            check_subword_store_satisfied(SB_ENC, ram_value, rs2_value, sb_new),
            "FUZZ SB FAILURE iteration {}\n  old = 0x{:08X}, rs2 = 0x{:08X}, new = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, ram_value, rs2_value, sb_new, seed,
        );

        // SH: store low halfword of rs2, preserve rest of word
        let sh_new = (ram_value & 0xFFFF0000) | (rs2_value & 0xFFFF);
        assert!(
            check_subword_store_satisfied(SH_ENC, ram_value, rs2_value, sh_new),
            "FUZZ SH FAILURE iteration {}\n  old = 0x{:08X}, rs2 = 0x{:08X}, new = 0x{:08X}\n  Reproduce: FUZZ_SEED=0x{:016X}",
            iteration, ram_value, rs2_value, sh_new, seed,
        );

        iteration += 1;
        if iteration % 1000 == 0 {
            eprintln!("[fuzz_load_store_subword] {} iterations completed", iteration);
        }
    }
}

/// Negative fuzz: wrong rd must cause constraint violation.
///
/// Validates circuit *soundness*: if a circuit accepts an incorrect
/// computation, a malicious prover could forge proofs. We provide correct
/// rs1/rs2 but a deliberately wrong rd, and assert the circuit rejects.
///
/// NOTE: BasicAssembly's debug evaluator skips constraints with unresolved
/// witness variables. This means some families (especially those with complex
/// witness derivation) may appear to "accept" wrong outputs at the debug level.
/// Full soundness testing requires the witness evaluator + prover pipeline.
#[test]
#[ignore = "requires full witness evaluator for soundness -- BasicAssembly debug evaluator has partial coverage"]
fn fuzz_negative_all_r_type() {
    skip_if_ci!();
    let seed = get_fuzz_seed(0xBAD_C0DE_1234);
    let mut rng = StdRng::seed_from_u64(seed);
    eprintln!("fuzz seed: 0x{:016X}", seed);

    let mut instructions = add_sub_instructions();
    instructions.extend(shift_binop_instructions());
    instructions.extend(mul_div_instructions());

    let mut iteration: u64 = 0;
    loop {
        for instr in &instructions {
            let cached = build_decoder(instr);
            let is_mersenne_op = instr.name == "ADDMOD" || instr.name == "SUBMOD";
            let rs1 = if is_mersenne_op {
                random_mersenne_input(&mut rng)
            } else {
                random_input(&mut rng)
            };
            let rs2 = if is_mersenne_op {
                random_mersenne_input(&mut rng)
            } else {
                random_input(&mut rng)
            };
            let correct_rd = (instr.eval)(rs1, rs2);

            // Flip a random bit in rd to make it wrong
            let bit = rng.random_range(0..32u32);
            let wrong_rd = correct_rd ^ (1u32 << bit);
            if wrong_rd == correct_rd {
                continue;
            }

            let case = NonMemTestCase {
                label: instr.name,
                rs1,
                rs2,
                rd: wrong_rd,
            };
            assert!(
                !check_case_satisfied(&cached, &case),
                "FUZZ NEGATIVE FAILURE (circuit accepted wrong output): {}\n  \
                 rs1 = 0x{:08X}\n  \
                 rs2 = 0x{:08X}\n  \
                 correct rd = 0x{:08X}\n  \
                 wrong rd   = 0x{:08X}\n  \
                 Reproduce: FUZZ_SEED=0x{:016X}",
                instr.name,
                rs1,
                rs2,
                correct_rd,
                wrong_rd,
                seed,
            );
        }
        iteration += 1;
        if iteration % 1000 == 0 {
            eprintln!("[fuzz_negative] {} iterations completed", iteration);
        }
    }
}
