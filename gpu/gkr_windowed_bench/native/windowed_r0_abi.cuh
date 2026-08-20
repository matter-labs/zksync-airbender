#pragma once

#include "common.cuh"
#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr_windowed_bench {

constexpr u32 R0_RECORD_WORDS = 4;
constexpr u32 R0_RECORD_CAPACITY = 1791;
constexpr u32 R0_PROGRAM_WORDS = 7164;
constexpr u32 R0_SOURCE_SLOTS = 1062;
constexpr u32 R0_WINDOW_CAPACITY = 64;
constexpr u32 R0_WINDOW_COLUMN_CAPACITY = 128;
// 1,665 sectioned entries at the corpus maximum plus 63 spare entries.
constexpr u32 R0_COEFFICIENT_CAPACITY = 1728;
constexpr u32 R0_IMMEDIATE_CAPACITY = 512;
constexpr u32 R0_PROJECTION_CAPACITY = 1731;
constexpr u32 R0_EQ_HIGH_ELEMENTS = 512;
constexpr u32 R0_KERNEL_ARGUMENT_CEILING_BYTES = 32764;
constexpr u32 R0_CONSTANT_MEMORY_CEILING_BYTES = 65536;
constexpr u32 R0_HISTORICAL_COEFFICIENT_ELEMENTS = 80;
constexpr u32 R0_HISTORICAL_EQ_HIGH_ELEMENTS = 512;
constexpr u32 R0_CONSTANT_FOOTPRINT_BYTES =
    (R0_HISTORICAL_COEFFICIENT_ELEMENTS + R0_HISTORICAL_EQ_HIGH_ELEMENTS + R0_COEFFICIENT_CAPACITY + R0_EQ_HIGH_ELEMENTS) * sizeof(e4);

constexpr u32 R0_COEFFICIENT_ONE = 0;
constexpr u32 R0_COEFFICIENT_NEG_ONE = 1;
constexpr u32 R0_COEFFICIENT_BANK_BIAS = 2;
constexpr u32 R0_C_INIT_NONE = 0xffffffffu;

constexpr u8 R0_CLASS_C0_LINEAR_BF = 0;
constexpr u8 R0_CLASS_C0_LINEAR_E4 = 1;
constexpr u8 R0_CLASS_C2_PRODUCT_BF_BF = 2;
constexpr u8 R0_CLASS_C2_PRODUCT_BF_E4 = 3;
constexpr u8 R0_CLASS_C2_PRODUCT_E4_E4 = 4;

constexpr u32 R0_SOURCE_WINDOW_BITS = 6;
constexpr u32 R0_SOURCE_COLUMN_BITS = 7;
constexpr u16 R0_SOURCE_WINDOW_MASK = (1u << R0_SOURCE_WINDOW_BITS) - 1;
constexpr u16 R0_SOURCE_COLUMN_MASK = (1u << R0_SOURCE_COLUMN_BITS) - 1;

struct r0_window_addr {
  const u8 *base;
  u8 log2_stride;
  u8 origin;
  u8 procedural_kind;
  u8 reserved[5];
};

struct r0_window_eq_sizes {
  u32 high[2];
  u32 low;
};

struct alignas(16) r0_vm_desc {
  r0_window_addr window_bases[R0_WINDOW_CAPACITY];
  u16 program[R0_PROGRAM_WORDS];
  const e4 *eq_low;
  e4 *partials;
  u32 log_rows;
  u32 record_count;
  u32 source_count;
  u32 window_count;
  u32 banked_coefficient_count;
  u32 c_init;
  r0_window_eq_sizes eq_sizes;
  u16 source_slots[R0_SOURCE_SLOTS];
};

struct r0_abi_layout {
  u64 window_addr_size;
  u64 window_addr_align;
  u64 window_addr_base;
  u64 window_addr_log2_stride;
  u64 window_addr_origin;
  u64 window_addr_procedural_kind;
  u64 window_addr_reserved;
  u64 eq_sizes_size;
  u64 eq_sizes_align;
  u64 eq_sizes_high;
  u64 eq_sizes_low;
  u64 vm_desc_size;
  u64 vm_desc_align;
  u64 vm_desc_window_bases;
  u64 vm_desc_program;
  u64 vm_desc_eq_low;
  u64 vm_desc_partials;
  u64 vm_desc_log_rows;
  u64 vm_desc_record_count;
  u64 vm_desc_source_count;
  u64 vm_desc_window_count;
  u64 vm_desc_banked_coefficient_count;
  u64 vm_desc_c_init;
  u64 vm_desc_eq_sizes;
  u64 vm_desc_source_slots;
};

static_assert(sizeof(void *) == 8);
static_assert(sizeof(r0_window_addr) == 16);
static_assert(alignof(r0_window_addr) == 8);
static_assert(__builtin_offsetof(r0_window_addr, base) == 0);
static_assert(__builtin_offsetof(r0_window_addr, log2_stride) == 8);
static_assert(__builtin_offsetof(r0_window_addr, origin) == 9);
static_assert(__builtin_offsetof(r0_window_addr, procedural_kind) == 10);
static_assert(__builtin_offsetof(r0_window_addr, reserved) == 11);
static_assert(sizeof(r0_window_eq_sizes) == 12);
static_assert(alignof(r0_window_eq_sizes) == 4);
static_assert(__builtin_offsetof(r0_window_eq_sizes, high) == 0);
static_assert(__builtin_offsetof(r0_window_eq_sizes, low) == 8);
static_assert(sizeof(r0_vm_desc) == 17536);
static_assert(alignof(r0_vm_desc) == 16);
static_assert(sizeof(r0_vm_desc) <= R0_KERNEL_ARGUMENT_CEILING_BYTES);
static_assert(__builtin_offsetof(r0_vm_desc, window_bases) == 0);
static_assert(__builtin_offsetof(r0_vm_desc, program) == 1024);
static_assert(__builtin_offsetof(r0_vm_desc, eq_low) == 15352);
static_assert(__builtin_offsetof(r0_vm_desc, partials) == 15360);
static_assert(__builtin_offsetof(r0_vm_desc, log_rows) == 15368);
static_assert(__builtin_offsetof(r0_vm_desc, record_count) == 15372);
static_assert(__builtin_offsetof(r0_vm_desc, source_count) == 15376);
static_assert(__builtin_offsetof(r0_vm_desc, window_count) == 15380);
static_assert(__builtin_offsetof(r0_vm_desc, banked_coefficient_count) == 15384);
static_assert(__builtin_offsetof(r0_vm_desc, c_init) == 15388);
static_assert(__builtin_offsetof(r0_vm_desc, eq_sizes) == 15392);
static_assert(__builtin_offsetof(r0_vm_desc, source_slots) == 15404);
static_assert(R0_RECORD_WORDS == 4);
static_assert(R0_PROGRAM_WORDS == R0_RECORD_CAPACITY * R0_RECORD_WORDS);
static_assert(R0_SOURCE_WINDOW_MASK == 0x3f);
static_assert(R0_SOURCE_COLUMN_MASK == 0x7f);
static_assert(R0_CLASS_C0_LINEAR_BF == 0);
static_assert(R0_CLASS_C0_LINEAR_E4 == 1);
static_assert(R0_CLASS_C2_PRODUCT_BF_BF == 2);
static_assert(R0_CLASS_C2_PRODUCT_BF_E4 == 3);
static_assert(R0_CLASS_C2_PRODUCT_E4_E4 == 4);
static_assert(R0_COEFFICIENT_ONE == 0);
static_assert(R0_COEFFICIENT_NEG_ONE == 1);
static_assert(R0_COEFFICIENT_BANK_BIAS == 2);
static_assert(R0_C_INIT_NONE != R0_COEFFICIENT_BANK_BIAS);
static_assert(R0_WINDOW_CAPACITY == 64);
static_assert(R0_WINDOW_COLUMN_CAPACITY == 128);
static_assert(R0_SOURCE_SLOTS == 1062);
static_assert(R0_COEFFICIENT_CAPACITY == 1728);
static_assert(R0_IMMEDIATE_CAPACITY == 512);
static_assert(R0_PROJECTION_CAPACITY == 1731);
static_assert(R0_EQ_HIGH_ELEMENTS == 512);
static_assert(R0_CONSTANT_FOOTPRINT_BYTES == 45312);
static_assert(R0_CONSTANT_FOOTPRINT_BYTES <= R0_CONSTANT_MEMORY_CEILING_BYTES);
static_assert(sizeof(r0_abi_layout) == 25 * sizeof(u64));

} // namespace airbender::gkr_windowed_bench
