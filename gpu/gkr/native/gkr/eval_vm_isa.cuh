#pragma once

#include "common.cuh"

namespace airbender::gkr {

// --- ISA 16-bit lane layout ----------------------------------------------------
// Mirrors the Rust forward ISA and encoder in `gpu_gkr_compiler`.
//
// header:  arith [op:2][arity:7 @2][f0:1 @9][f1:1 @10][sign:1 @11][rsvd @12+]
//          mov   [op=3:2][dir:2 @2][field:1 @4][rsvd @5+]
// operand: [tag:2][payload:14]; tag 0=Source{[window:6 @2][column:7 @8]}
//          1=Smem{[cell @2]}
//          2=Ldc{[sub:2 @2][idx @4]} 3=Special{[desc @2]}
// dst:     [tag:1]; tag 0=Smem{[cell @1]} 1=GlobalMaterialize{[slot:4 @1][col @5]}

// opcode field (header bits [0..2))
constexpr u32 FWD_VM_OP_BITS = 2;
constexpr u32 FWD_VM_OP_MASK = (1u << FWD_VM_OP_BITS) - 1;
constexpr u32 FWD_VM_OP_ADD = 0;
constexpr u32 FWD_VM_OP_MUL = 1;
constexpr u32 FWD_VM_OP_FMA = 2;
constexpr u32 FWD_VM_OP_MOV = 3;

// arith header fields
constexpr u32 FWD_VM_HDR_ARITY_SHIFT = FWD_VM_OP_BITS; // 2
constexpr u32 FWD_VM_HDR_ARITY_BITS = 7;
constexpr u32 FWD_VM_HDR_ARITY_MASK = (1u << FWD_VM_HDR_ARITY_BITS) - 1;            // 0x7f
constexpr u32 FWD_VM_HDR_F0_SHIFT = FWD_VM_HDR_ARITY_SHIFT + FWD_VM_HDR_ARITY_BITS; // 9
constexpr u32 FWD_VM_HDR_F1_SHIFT = FWD_VM_HDR_F0_SHIFT + 1;                        // 10
constexpr u32 FWD_VM_HDR_SIGN_SHIFT = FWD_VM_HDR_F1_SHIFT + 1;                      // 11

// Mov header fields + dir values (dir 3 stays reserved)
constexpr u32 FWD_VM_MOV_DIR_SHIFT = FWD_VM_OP_BITS; // 2
constexpr u32 FWD_VM_MOV_DIR_BITS = 2;
constexpr u32 FWD_VM_MOV_DIR_MASK = (1u << FWD_VM_MOV_DIR_BITS) - 1;
constexpr u32 FWD_VM_MOV_FIELD_SHIFT = FWD_VM_MOV_DIR_SHIFT + FWD_VM_MOV_DIR_BITS; // 4
constexpr u32 FWD_VM_MOV_ACC_FROM_SRC = 0;
constexpr u32 FWD_VM_MOV_DST_FROM_ACC = 1;
constexpr u32 FWD_VM_MOV_DST_FROM_SRC = 2;

// operand lane
constexpr u32 FWD_VM_OPERAND_TAG_BITS = 2;
constexpr u32 FWD_VM_OPERAND_TAG_MASK = (1u << FWD_VM_OPERAND_TAG_BITS) - 1;
constexpr u32 FWD_VM_OPERAND_SOURCE = 0;
constexpr u32 FWD_VM_OPERAND_SMEM = 1;
constexpr u32 FWD_VM_OPERAND_LDC = 2;
constexpr u32 FWD_VM_OPERAND_SPECIAL = 3;
constexpr u32 FWD_VM_SOURCE_WINDOW_SHIFT = FWD_VM_OPERAND_TAG_BITS;
constexpr u32 FWD_VM_SOURCE_WINDOW_BITS = 6;
constexpr u32 FWD_VM_SOURCE_WINDOW_MASK = (1u << FWD_VM_SOURCE_WINDOW_BITS) - 1;
constexpr u32 FWD_VM_SOURCE_COLUMN_SHIFT = FWD_VM_SOURCE_WINDOW_SHIFT + FWD_VM_SOURCE_WINDOW_BITS;
constexpr u32 FWD_VM_SOURCE_COLUMN_BITS = 7;
constexpr u32 FWD_VM_SOURCE_COLUMN_MASK = (1u << FWD_VM_SOURCE_COLUMN_BITS) - 1;
constexpr u32 FWD_VM_OPERAND_CELL_SHIFT = FWD_VM_OPERAND_TAG_BITS; // 2
constexpr u32 FWD_VM_OPERAND_DESC_SHIFT = FWD_VM_OPERAND_TAG_BITS; // 2
constexpr u32 FWD_VM_LDC_SUB_SHIFT = FWD_VM_OPERAND_TAG_BITS;      // 2
constexpr u32 FWD_VM_LDC_SUB_BITS = 2;
constexpr u32 FWD_VM_LDC_SUB_MASK = (1u << FWD_VM_LDC_SUB_BITS) - 1;
constexpr u32 FWD_VM_LDC_IDX_SHIFT = FWD_VM_LDC_SUB_SHIFT + FWD_VM_LDC_SUB_BITS; // 4

// dst lane
constexpr u32 FWD_VM_DST_TAG_BITS = 1;
constexpr u32 FWD_VM_DST_TAG_MASK = (1u << FWD_VM_DST_TAG_BITS) - 1;
constexpr u32 FWD_VM_DST_SMEM = 0;
constexpr u32 FWD_VM_DST_GLOBAL = 1;
constexpr u32 FWD_VM_DST_SLOT_BITS = 4;
constexpr u32 FWD_VM_DST_SLOT_MASK = (1u << FWD_VM_DST_SLOT_BITS) - 1;
constexpr u32 FWD_VM_DST_CELL_SHIFT = FWD_VM_DST_TAG_BITS;                         // 1
constexpr u32 FWD_VM_DST_SLOT_SHIFT = FWD_VM_DST_TAG_BITS;                         // 1
constexpr u32 FWD_VM_DST_COL_SHIFT = FWD_VM_DST_SLOT_SHIFT + FWD_VM_DST_SLOT_BITS; // 5

} // namespace airbender::gkr
