#pragma once

#include "common.cuh"
#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr_windowed_bench {

constexpr u32 WINDOW_WARPS_PER_BLOCK = 9;
constexpr u32 WINDOW_THREADS_PER_BLOCK = 288;
constexpr u32 WINDOW_CELLS = 27;
constexpr u32 WINDOW_PROGRAM_CAPACITY = 175;
constexpr u32 WINDOW_SLOT_CAPACITY = 6;
constexpr u32 WINDOW_IMMEDIATE_CAPACITY = 7;
constexpr u32 WINDOW_KERNEL_ARGUMENT_CEILING_BYTES = 32764;

struct window_eq_sizes {
  u32 high[2];
  u32 low;
};

struct alignas(8) window_base_record {
  const u8 *base;
};

struct alignas(8) window_instruction {
  u16 term_class;
  u16 factor;
  u16 source_a;
  u16 source_b;
};

struct alignas(16) window_vm_desc {
  window_instruction program[WINDOW_PROGRAM_CAPACITY];
  window_base_record window_bases[WINDOW_SLOT_CAPACITY];
  u32 immediates[WINDOW_IMMEDIATE_CAPACITY];
  const e4 *eq_low;
  e4 *partials;
  u32 program_records;
  u32 term_count;
  u32 record_count;
  u32 num_immediates;
  u32 num_coefficients;
  u32 c_init_coeff;
  u32 log_rows;
  window_eq_sizes eq_sizes;
};

static_assert(sizeof(window_eq_sizes) == 12);
static_assert(sizeof(window_base_record) == 8);
static_assert(alignof(window_base_record) == 8);
static_assert(__builtin_offsetof(window_base_record, base) == 0);
static_assert(sizeof(window_instruction) == 8);
static_assert(alignof(window_instruction) == 8);
static_assert(__builtin_offsetof(window_instruction, term_class) == 0);
static_assert(__builtin_offsetof(window_instruction, factor) == 2);
static_assert(__builtin_offsetof(window_instruction, source_a) == 4);
static_assert(__builtin_offsetof(window_instruction, source_b) == 6);
static_assert(sizeof(window_vm_desc) == 1536);
static_assert(sizeof(window_vm_desc) <= WINDOW_KERNEL_ARGUMENT_CEILING_BYTES);
static_assert(alignof(window_vm_desc) == 16);
static_assert(__builtin_offsetof(window_vm_desc, program) == 0);
static_assert(__builtin_offsetof(window_vm_desc, window_bases) == 1400);
static_assert(__builtin_offsetof(window_vm_desc, immediates) == 1448);
static_assert(__builtin_offsetof(window_vm_desc, eq_low) == 1480);
static_assert(__builtin_offsetof(window_vm_desc, partials) == 1488);
static_assert(__builtin_offsetof(window_vm_desc, program_records) == 1496);
static_assert(__builtin_offsetof(window_vm_desc, term_count) == 1500);
static_assert(__builtin_offsetof(window_vm_desc, record_count) == 1504);
static_assert(__builtin_offsetof(window_vm_desc, num_immediates) == 1508);
static_assert(__builtin_offsetof(window_vm_desc, num_coefficients) == 1512);
static_assert(__builtin_offsetof(window_vm_desc, c_init_coeff) == 1516);
static_assert(__builtin_offsetof(window_vm_desc, log_rows) == 1520);
static_assert(__builtin_offsetof(window_vm_desc, eq_sizes) == 1524);
static_assert(WINDOW_THREADS_PER_BLOCK == 32 * WINDOW_WARPS_PER_BLOCK);
static_assert(WINDOW_CELLS == 3 * WINDOW_WARPS_PER_BLOCK);

} // namespace airbender::gkr_windowed_bench
