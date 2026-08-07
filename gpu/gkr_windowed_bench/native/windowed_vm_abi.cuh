#pragma once

#include "common.cuh"
#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr_windowed_bench {

constexpr u32 WINDOW_WARPS_PER_BLOCK = 9;
constexpr u32 WINDOW_THREADS_PER_BLOCK = 288;
constexpr u32 WINDOW_CELLS = 27;
constexpr u32 WINDOW_PROGRAM_CAPACITY = 175;
constexpr u32 WINDOW_SOURCE_CAPACITY = 59;
constexpr u32 WINDOW_SLOT_CAPACITY = 6;
constexpr u32 WINDOW_IMMEDIATE_CAPACITY = 7;
constexpr u32 WINDOW_KERNEL_ARGUMENT_CEILING_BYTES = 32764;

struct window_eq_sizes {
  u32 high[2];
  u32 low;
};

struct window_addr_slot {
  const u8 *base;
  u8 log2_stride;
  u8 origin;
  u8 procedural_kind;
  u8 reserved[5];
};

struct alignas(2) window_source_record {
  u16 src;
  u16 cache;
  u8 source_class;
  u8 delta;
};

struct alignas(8) window_instruction {
  u16 term_class;
  u16 factor;
  u16 source_a;
  u16 source_b;
};

struct alignas(16) window_vm_desc {
  window_instruction program[WINDOW_PROGRAM_CAPACITY];
  window_source_record sources[WINDOW_SOURCE_CAPACITY];
  window_addr_slot slots[WINDOW_SLOT_CAPACITY];
  u32 immediates[WINDOW_IMMEDIATE_CAPACITY];
  const e4 *eq_low;
  e4 *partials;
  u32 program_records;
  u32 term_count;
  u32 record_count;
  u32 num_sources;
  u32 num_slots;
  u32 num_immediates;
  u32 num_coefficients;
  u32 c_init_coeff;
  u32 log_rows;
  window_eq_sizes eq_sizes;
};

static_assert(sizeof(window_eq_sizes) == 12);
static_assert(sizeof(window_addr_slot) == 16);
static_assert(alignof(window_addr_slot) == 8);
static_assert(__builtin_offsetof(window_addr_slot, base) == 0);
static_assert(__builtin_offsetof(window_addr_slot, log2_stride) == 8);
static_assert(__builtin_offsetof(window_addr_slot, origin) == 9);
static_assert(__builtin_offsetof(window_addr_slot, procedural_kind) == 10);
static_assert(__builtin_offsetof(window_addr_slot, reserved) == 11);
static_assert(sizeof(window_source_record) == 6);
static_assert(alignof(window_source_record) == 2);
static_assert(sizeof(window_instruction) == 8);
static_assert(alignof(window_instruction) == 8);
static_assert(__builtin_offsetof(window_instruction, term_class) == 0);
static_assert(__builtin_offsetof(window_instruction, factor) == 2);
static_assert(__builtin_offsetof(window_instruction, source_a) == 4);
static_assert(__builtin_offsetof(window_instruction, source_b) == 6);
static_assert(sizeof(window_vm_desc) == 1952);
static_assert(sizeof(window_vm_desc) <= WINDOW_KERNEL_ARGUMENT_CEILING_BYTES);
static_assert(alignof(window_vm_desc) == 16);
static_assert(__builtin_offsetof(window_vm_desc, program) == 0);
static_assert(__builtin_offsetof(window_vm_desc, sources) == 1400);
static_assert(__builtin_offsetof(window_vm_desc, slots) == 1760);
static_assert(__builtin_offsetof(window_vm_desc, immediates) == 1856);
static_assert(__builtin_offsetof(window_vm_desc, eq_low) == 1888);
static_assert(__builtin_offsetof(window_vm_desc, partials) == 1896);
static_assert(__builtin_offsetof(window_vm_desc, program_records) == 1904);
static_assert(__builtin_offsetof(window_vm_desc, term_count) == 1908);
static_assert(__builtin_offsetof(window_vm_desc, record_count) == 1912);
static_assert(__builtin_offsetof(window_vm_desc, num_sources) == 1916);
static_assert(__builtin_offsetof(window_vm_desc, num_slots) == 1920);
static_assert(__builtin_offsetof(window_vm_desc, num_immediates) == 1924);
static_assert(__builtin_offsetof(window_vm_desc, num_coefficients) == 1928);
static_assert(__builtin_offsetof(window_vm_desc, c_init_coeff) == 1932);
static_assert(__builtin_offsetof(window_vm_desc, log_rows) == 1936);
static_assert(__builtin_offsetof(window_vm_desc, eq_sizes) == 1940);
static_assert(WINDOW_THREADS_PER_BLOCK == 32 * WINDOW_WARPS_PER_BLOCK);
static_assert(WINDOW_CELLS == 3 * WINDOW_WARPS_PER_BLOCK);

} // namespace airbender::gkr_windowed_bench
