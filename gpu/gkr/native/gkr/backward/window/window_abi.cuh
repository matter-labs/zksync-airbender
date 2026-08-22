#pragma once

// Wire and launch ABI of the window-3 sectioned backward executor. The address
// slots, immediate ids and coefficient bank are the segmented VM's; only the
// program encoding and the descriptor shape are the window's own.
#include "../segmented_vm.cuh"

namespace airbender::gkr::backward {

// opcode, factor, source_a, source_b.
constexpr u32 BWD_WINDOW_INSTRUCTION_WORDS = 4;
// Four live section endpoints; the fifth word carries the shape mask.
constexpr u32 BWD_WINDOW_SECTION_WORDS = 16;
constexpr u32 BWD_WINDOW_SECTION_BF = 0;
constexpr u32 BWD_WINDOW_SECTION_LINEAR_E4 = 1;
constexpr u32 BWD_WINDOW_SECTION_SINGLETON_E4 = 2;
constexpr u32 BWD_WINDOW_SECTION_PAIR_E4 = 3;
// Corpus maximum 7,036 words, rounded so the array is a whole number of
// 16-byte lines.
constexpr u32 BWD_WINDOW_PROGRAM_WORD_CAP = 7040;
constexpr u32 BWD_WINDOW_ADDR_SLOTS = BWD_SEG_ADDR_SLOTS;
constexpr u32 BWD_WINDOW_MAX_IMMEDIATES = BWD_SEG_MAX_IMMEDIATES;

// One block covers 32 rows x 9 (x0, x1) selector pairs; each thread owns the
// three x2 cells of its pair, so a row tile publishes the full 27-cell tensor.
constexpr u32 BWD_WINDOW_ROWS_PER_TILE = 32;
constexpr u32 BWD_WINDOW_SELECTOR_PAIRS = 9;
constexpr u32 BWD_WINDOW_TENSOR_CELLS = 27;
constexpr u32 BWD_WINDOW_BLOCK_THREADS = 288;

// Term/control opcodes, mirroring `window::WINDOW_OPCODE_*`. Values 0..3 are the
// lean R0 term classes; the rest are window-only control codes.
constexpr u16 BWD_WINDOW_OPCODE_LINEAR_BF = 0;
constexpr u16 BWD_WINDOW_OPCODE_LINEAR_E4 = 1;
constexpr u16 BWD_WINDOW_OPCODE_PRODUCT_BF_BF = 2;
constexpr u16 BWD_WINDOW_OPCODE_PRODUCT_BF_E4 = 3;
constexpr u16 BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL = 4;
constexpr u16 BWD_WINDOW_OPCODE_PRODUCT_E4_E4 = 5;
constexpr u16 BWD_WINDOW_OPCODE_GROUP_BF = 6;
constexpr u16 BWD_WINDOW_OPCODE_GROUP_E4 = 7;
constexpr u16 BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B = 8;
constexpr u16 BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB = 9;
constexpr u16 BWD_WINDOW_OPCODE_LINEAR_E4_WIDE = 10;
// The high bit of a factor word: a product prefix, a mid-group reduction, or a
// negated coefficient, depending on the section.
constexpr u16 BWD_WINDOW_FLAG = 1u << 15;
constexpr u16 BWD_WINDOW_ID_MASK = BWD_WINDOW_FLAG - 1;

static_assert(BWD_WINDOW_OPCODE_LINEAR_BF == BWD_SEG_R0_CLASS_C0_LINEAR_BF, "window opcode 0 must stay the lean BF linear class");
static_assert(BWD_WINDOW_OPCODE_LINEAR_E4 == BWD_SEG_R0_CLASS_C0_LINEAR_E4, "window opcode 1 must stay the lean E4 linear class");
static_assert(BWD_WINDOW_OPCODE_PRODUCT_BF_BF == BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF, "window opcode 2 must stay the lean BFxBF class");
static_assert(BWD_WINDOW_OPCODE_PRODUCT_BF_E4 == BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4, "window opcode 3 must stay the lean BFxE4 class");

// Compile-time hot-loop features, mirroring `window::WindowShape`.
constexpr u16 BWD_WINDOW_SHAPE_BF_PROCEDURAL = 1u << 0;
constexpr u16 BWD_WINDOW_SHAPE_BF_BANKED_IMMEDIATE = 1u << 1;
constexpr u16 BWD_WINDOW_SHAPE_BF_INNER_REDUCTION = 1u << 2;
constexpr u16 BWD_WINDOW_SHAPE_BF_LINEAR_TAIL = 1u << 3;
constexpr u16 BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_3 = 1u << 4;
constexpr u16 BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_5 = 1u << 5;
constexpr u16 BWD_WINDOW_SHAPE_E4_FIXED_PAIR = 1u << 6;
constexpr u16 BWD_WINDOW_SHAPE_BF_NEGATIVE_FACTOR = 1u << 7;
constexpr u16 BWD_WINDOW_SHAPE_E4_NEGATIVE_FACTOR = 1u << 8;
constexpr u16 BWD_WINDOW_SHAPE_E4_PAIR_CLASS_3 = 1u << 9;
constexpr u16 BWD_WINDOW_SHAPE_E4_PAIR_CLASS_5 = 1u << 10;
constexpr u16 BWD_WINDOW_SHAPE_BF_SINGLE_PRODUCT_PREFIX = 1u << 11;
constexpr u16 BWD_WINDOW_SHAPE_DEFINED_BITS = (1u << 12) - 1;

static_assert(BWD_WINDOW_SHAPE_DEFINED_BITS == 0xfff, "window shape mask width drift");

// A source operand is `slot:6 << 7 | column:7`, the segmented VM's addressing
// lane; the window stream carries it directly rather than through a slot table.
static_assert(BWD_SEG_ADDR_COLUMN_BITS == 7, "window source packing drift");

// The complete by-value launch descriptor, passed as a single
// `__grid_constant__` kernel parameter. Its Rust mirror is
// `src/backward/window/binding.rs`.
struct alignas(BWD_SEG_DESC_ALIGN) bwd_window_desc {
  bwd_seg_addr_slot slot[BWD_WINDOW_ADDR_SLOTS];
  // Production factored-eq low table; high tables stay in `ab_gkr_eq_high`.
  const e4 *eq_low;
  // Row-tile-major 27-cell partial tensor.
  e4 *partials;
  u32 log_rows;
  gkr_eq_sizes eq_sizes;
  // Cumulative instruction endpoints; word 4 carries the shape mask.
  u32 sections[BWD_WINDOW_SECTION_WORDS];
  u16 program[BWD_WINDOW_PROGRAM_WORD_CAP];
  u32 immediates[BWD_WINDOW_MAX_IMMEDIATES];
};

static_assert(sizeof(bwd_window_desc) == 17248, "bwd_window_desc/WindowLaunchBinding ABI size drift");
static_assert(alignof(bwd_window_desc) == BWD_SEG_DESC_ALIGN, "bwd_window_desc ABI alignment drift");
static_assert(sizeof(bwd_window_desc) <= BWD_SEG_DESC_CAP, "bwd_window_desc exceeds the __grid_constant__ parameter budget");
static_assert(__builtin_offsetof(bwd_window_desc, slot) == 0, "slot ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, eq_low) == 1024, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, partials) == 1032, "partials ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, log_rows) == 1040, "log_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, eq_sizes) == 1044, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, sections) == 1056, "sections ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, program) == 1120, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, immediates) == 15200, "immediates ABI offset drift");
static_assert(BWD_WINDOW_PROGRAM_WORD_CAP * sizeof(u16) % BWD_SEG_DESC_ALIGN == 0, "the program array is not a whole number of 16-byte quanta");
static_assert(BWD_WINDOW_PROGRAM_WORD_CAP % BWD_WINDOW_INSTRUCTION_WORDS == 0, "the program array must hold whole instructions");
static_assert(BWD_WINDOW_BLOCK_THREADS == BWD_WINDOW_SELECTOR_PAIRS * BWD_SEG_WARP_LANES, "one warp per selector pair");
static_assert(BWD_WINDOW_TENSOR_CELLS == 3 * BWD_WINDOW_SELECTOR_PAIRS, "the window tensor is nine pairs of three x2 cells");
static_assert(BWD_WINDOW_ROWS_PER_TILE == BWD_SEG_WARP_LANES, "a row tile is one warp of rows");

} // namespace airbender::gkr::backward
