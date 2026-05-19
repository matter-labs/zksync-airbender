//! Decoder-level negative tests.
//!
//! The per-family circuit tests in this directory all feed legal encodings
//! through process_binary_into_separate_tables_ext, then exercise the
//! resulting decoded data against the circuit constraints.  That proves the
//! circuit accepts what it should — but not that the decoder rejects what it
//! shouldn't.
//!
//! These tests poke each family's decoder with malformed encodings (wrong
//! opcode, bad funct3, bad funct7, bad SYSTEM custom-op funct7) and assert that
//! the decoder leaves the slot empty and produces the default witness data with opcode_family_bits == 0.
//! Both bytecode_preprocessor.rs:53 propagates an Err(()) from define_decoder_subspace.

use super::encoding::{encode_b, encode_i, encode_r, encode_r_system, encode_u};
use super::*;

use cs::machine::ops::unrolled::decoder::{
    process_binary_into_separate_tables_ext, AddSubLuiAuipcMopDecoder, DivMulDecoder,
    JumpSltBranchDecoder, OpcodeFamilyDecoder, ShiftBinaryCsrrwDecoder,
    SubwordOnlyMemoryFamilyDecoder, WordOnlyMemoryFamilyDecoder,
};
use std::alloc::Global;

fn assert_decoder_rejects(
    decoder: Box<dyn OpcodeFamilyDecoder>,
    family_idx: u8,
    encoding: u32,
    label: &str,
) {
    let bytecode = vec![encoding];
    let bytecode_size = 1024;
    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[decoder],
        bytecode_size,
        &[],
    );
    let (table, decoder_data) = t.remove(&family_idx).expect("family entry in result map");
    assert!(
        table[0].is_none(),
        "{}: decoder accepted invalid encoding 0x{:08X} (table entry was Some)",
        label,
        encoding
    );
    assert_eq!(
        decoder_data[0].opcode_family_bits, 0,
        "{}: decoder produced opcode_family_bits=0b{:08b} for invalid encoding 0x{:08X}",
        label, decoder_data[0].opcode_family_bits, encoding
    );
}

// Family-idx aliases to keep call sites tidy.
const ADD_SUB_IDX: u8 =
    common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
const JUMP_SLT_IDX: u8 = common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;
const SHIFT_IDX: u8 = common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;
const MUL_DIV_IDX: u8 = common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX;
const LSW_IDX: u8 = common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;
const LSSW_IDX: u8 = common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;

// AddSubLuiAuipcMop family
// Valid: ADD/SUB/ADDI/LUI/AUIPC + ADDMOD/SUBMOD/MULMOD via SYSTEM funct3=0b100

#[test]
fn test_add_sub_rejects_wrong_opcode() {
    // JAL (opcode 0x6F) — not in this family.
    let jal_encoding: u32 = (0 << 7) | 0x6F;
    assert_decoder_rejects(
        Box::new(AddSubLuiAuipcMopDecoder),
        ADD_SUB_IDX,
        jal_encoding,
        "AddSub: JAL opcode",
    );
}

#[test]
fn test_add_sub_rejects_invalid_funct3_for_op() {
    // OP (0x33) with funct3=0b001 is SLL — belongs to ShiftBinop, not AddSub.
    let enc = encode_r(0b001, 0b0000000, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(AddSubLuiAuipcMopDecoder),
        ADD_SUB_IDX,
        enc,
        "AddSub: OP funct3=0b001",
    );
}

#[test]
fn test_add_sub_rejects_invalid_funct7_for_add() {
    // OP funct3=0b000 is ADD/SUB; only funct7 in {0b0000000, 0b0100000} is valid.
    // funct7=0b0010000 is reserved.
    let enc = encode_r(0b000, 0b0010000, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(AddSubLuiAuipcMopDecoder),
        ADD_SUB_IDX,
        enc,
        "AddSub: ADD funct7=0b0010000",
    );
}

#[test]
fn test_add_sub_rejects_invalid_system_custom_op_funct7() {
    // SYSTEM funct3=0b100 only accepts ADDMOD/SUBMOD/MULMOD funct7s
    // (0b1000001, 0b1000011, 0b1000101). 0b1111111 is not assigned.
    let enc = encode_r_system(0b100, 0b1111111, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(AddSubLuiAuipcMopDecoder),
        ADD_SUB_IDX,
        enc,
        "AddSub: SYSTEM funct3=0b100 funct7=0b1111111",
    );
}

#[test]
fn test_add_sub_rejects_invalid_system_funct3() {
    // SYSTEM with funct3=0b000 is ECALL/EBREAK/MRET territory — not in this family.
    let enc = encode_r_system(0b000, 0b0000000, 0, 0, 0);
    assert_decoder_rejects(
        Box::new(AddSubLuiAuipcMopDecoder),
        ADD_SUB_IDX,
        enc,
        "AddSub: SYSTEM funct3=0b000",
    );
}

// JumpSltBranch family
// Valid: JAL, JALR, BEQ/BNE/BLT/BGE/BLTU/BGEU, SLT/SLTU/SLTI/SLTIU

#[test]
fn test_jump_branch_rejects_wrong_opcode() {
    // ADD (opcode 0x33, funct3=0b000, funct7=0) — belongs to AddSub.
    let enc = encode_r(0b000, 0b0000000, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(JumpSltBranchDecoder::<true>),
        JUMP_SLT_IDX,
        enc,
        "JumpBranch: ADD opcode",
    );
}

#[test]
fn test_jump_branch_rejects_reserved_branch_funct3() {
    // BRANCH opcode (0x63) only defines funct3 in {000,001,100,101,110,111}.
    // funct3=0b010 and 0b011 are reserved.
    let enc = encode_b(0b010, 1, 2, 8);
    assert_decoder_rejects(
        Box::new(JumpSltBranchDecoder::<true>),
        JUMP_SLT_IDX,
        enc,
        "JumpBranch: BRANCH funct3=0b010",
    );
}

#[test]
fn test_jump_branch_rejects_invalid_slt_funct7() {
    // SLT/SLTU are OP funct3=0b010 / 0b011 with funct7=0. funct7=0b0100000 is not assigned for these.
    let enc = encode_r(0b010, 0b0100000, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(JumpSltBranchDecoder::<true>),
        JUMP_SLT_IDX,
        enc,
        "JumpBranch: SLT funct7=0b0100000",
    );
}

// ShiftBinaryCsrrw family
// Valid: SLL/SRL/SRA/AND/OR/XOR (+ I-type variants) + CSRRW (SYSTEM funct3=0b001)

#[test]
fn test_shift_binop_rejects_wrong_opcode() {
    // LUI (0x37) — not in this family.
    let enc = encode_u(0x37, 3, 0xABCDE);
    assert_decoder_rejects(
        Box::new(ShiftBinaryCsrrwDecoder),
        SHIFT_IDX,
        enc,
        "Shift: LUI opcode",
    );
}

#[test]
fn test_shift_binop_rejects_invalid_shift_funct7() {
    // SLL (OP funct3=0b001) only allows funct7=0b0000000.
    // SRL/SRA (funct3=0b101) allow {0b0000000, 0b0100000}.
    // funct7=0b1000000 is invalid for SLL.
    let enc = encode_r(0b001, 0b1000000, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(ShiftBinaryCsrrwDecoder),
        SHIFT_IDX,
        enc,
        "Shift: SLL funct7=0b1000000",
    );
}

#[test]
fn test_shift_binop_rejects_invalid_csr_funct3() {
    // SYSTEM funct3=0b010 is CSRRS — only CSRRW (funct3=0b001) is in this family.
    let enc = encode_r_system(0b010, 0, 3, 1, 0);
    assert_decoder_rejects(
        Box::new(ShiftBinaryCsrrwDecoder),
        SHIFT_IDX,
        enc,
        "Shift: SYSTEM funct3=0b010 (CSRRS, not CSRRW)",
    );
}

// MulDiv family
// Valid: MUL/MULH/MULHSU/MULHU/DIV/DIVU/REM/REMU (OP funct7=0b0000001)

#[test]
fn test_mul_div_rejects_wrong_opcode() {
    // ADDI (opcode 0x13) — not in this family.
    let enc = encode_i(0b000, 3, 1, 7);
    assert_decoder_rejects(
        Box::new(DivMulDecoder::<true>),
        MUL_DIV_IDX,
        enc,
        "MulDiv: ADDI opcode",
    );
}

#[test]
fn test_mul_div_rejects_invalid_funct7() {
    // M-extension uses funct7=0b0000001 with opcode 0x33. funct7=0b0000010
    // is reserved.
    let enc = encode_r(0b000, 0b0000010, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(DivMulDecoder::<true>),
        MUL_DIV_IDX,
        enc,
        "MulDiv: OP funct7=0b0000010",
    );
}

#[test]
fn test_mul_div_unsigned_rejects_signed_op() {
    // DivMulDecoder<false> excludes signed M-ext ops (MULH/MULHSU/DIV/REM).
    // MULH = OP funct3=0b001 funct7=0b0000001.
    let enc = encode_r(0b001, 0b0000001, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(DivMulDecoder::<false>),
        MUL_DIV_IDX,
        enc,
        "MulDiv<unsigned>: MULH (signed) is rejected",
    );
}

// WordOnlyMemory family
// Valid: LW (LOAD funct3=0b010) and SW (STORE funct3=0b010)

#[test]
fn test_word_mem_rejects_wrong_opcode() {
    // ADD (0x33) — not in this family.
    let enc = encode_r(0b000, 0b0000000, 3, 1, 2);
    assert_decoder_rejects(
        Box::new(WordOnlyMemoryFamilyDecoder),
        LSW_IDX,
        enc,
        "WordMem: ADD opcode",
    );
}

#[test]
fn test_word_mem_rejects_subword_load_funct3() {
    // LB (LOAD funct3=0b000) belongs to the subword family, not word-only.
    let lb_enc = ((0u32 & 0xFFF) << 20) | (1 << 15) | (0b000 << 12) | (3 << 7) | 0x03;
    assert_decoder_rejects(
        Box::new(WordOnlyMemoryFamilyDecoder),
        LSW_IDX,
        lb_enc,
        "WordMem: LB funct3=0b000",
    );
}

#[test]
fn test_word_mem_rejects_reserved_load_funct3() {
    // LOAD funct3=0b011 is LD (RV64) — reserved on RV32, never word-only.
    let enc = ((0u32 & 0xFFF) << 20) | (1 << 15) | (0b011 << 12) | (3 << 7) | 0x03;
    assert_decoder_rejects(
        Box::new(WordOnlyMemoryFamilyDecoder),
        LSW_IDX,
        enc,
        "WordMem: LOAD funct3=0b011",
    );
}

// SubwordOnlyMemory family
// Valid: LB/LH/LBU/LHU + SB/SH

#[test]
fn test_subword_mem_rejects_wrong_opcode() {
    // ADDI (0x13) — not in this family.
    let enc = encode_i(0b000, 3, 1, 0);
    assert_decoder_rejects(
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        LSSW_IDX,
        enc,
        "SubwordMem: ADDI opcode",
    );
}

#[test]
fn test_subword_mem_rejects_word_load_funct3() {
    // LW (LOAD funct3=0b010) belongs to the word-only family.
    let lw_enc = ((0u32 & 0xFFF) << 20) | (1 << 15) | (0b010 << 12) | (3 << 7) | 0x03;
    assert_decoder_rejects(
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        LSSW_IDX,
        lw_enc,
        "SubwordMem: LW funct3=0b010",
    );
}

#[test]
fn test_subword_mem_rejects_reserved_store_funct3() {
    // STORE funct3 in {0b000=SB, 0b001=SH, 0b010=SW}; SW is in another family. funct3=0b101 is reserved.
    let enc = (0u32 << 25) | (2 << 20) | (1 << 15) | (0b101 << 12) | (0 << 7) | 0x23;
    assert_decoder_rejects(
        Box::new(SubwordOnlyMemoryFamilyDecoder),
        LSSW_IDX,
        enc,
        "SubwordMem: STORE funct3=0b101 (reserved)",
    );
}
