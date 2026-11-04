#pragma once

#include "../memory.cuh"
#include "layout.cuh"
#include "ram_access.cuh"
#include "trace.cuh"

using namespace ::airbender::memory;
using namespace ::airbender::witness::layout;
using namespace ::airbender::witness::ram_access;
using namespace ::airbender::witness::trace;

namespace airbender::witness::memory {

#define MAX_INITS_AND_TEARDOWNS_SETS_COUNT 16

struct ShuffleRamInitAndTeardownLayouts {
  const u32 count;
  const ShuffleRamInitAndTeardownLayout layouts[MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
};

DEVICE_FORCEINLINE void write_bool_value(const ColumnAddress column, const bool value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_bool_value(const ColumnSet<1> column, const bool value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_u8_value(const ColumnAddress column, const u8 value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_u8_value(const ColumnSet<1> column, const u8 value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_u16_value(const ColumnAddress column, const u16 value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_u16_value(const ColumnSet<1> column, const u16 value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_u32_value(const ColumnSet<2> columns, const u32 value, const matrix_setter<bf, st_modifier::cg> dst) {
  const u32 low_index = columns.offset;
  const u32 high_index = low_index + 1;
  const u32 low_value = value & 0xffff;
  const u32 high_value = value >> 16;
  dst.set_at_col(low_index, bf(low_value));
  dst.set_at_col(high_index, bf(high_value));
}

DEVICE_FORCEINLINE void write_u32_as_bf_value(const ColumnSet<1> column, const u32 value, const matrix_setter<bf, st_modifier::cg> dst) {
  dst.set_at_col(column.offset, bf(value));
}

DEVICE_FORCEINLINE void write_timestamp_value(const ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> columns, const TimestampData value,
                                              const matrix_setter<bf, st_modifier::cg> dst) {
  static_assert(NUM_TIMESTAMP_COLUMNS_FOR_RAM == 2);
  const u32 low_index = columns.offset;
  const u32 high_index = low_index + 1;
  const u32 low_value = value.get_low();
  const u32 high_value = value.get_high();
  dst.set_at_col(low_index, bf(low_value));
  dst.set_at_col(high_index, bf(high_value));
}

// Uncomment to enable printing of memory writes for a specific thread index
// #define PRINT_THREAD_IDX 0xffffffff
#ifdef PRINT_THREAD_IDX
#define PRINT_U8(p, c, v)                                                                                                                                      \
  if (index == PRINT_THREAD_IDX)                                                                                                                               \
  printf(#p "[%u] <- %u\n", c.offset, v)
#define PRINT_U16(p, c, v)                                                                                                                                     \
  if (index == PRINT_THREAD_IDX)                                                                                                                               \
  printf(#p "[%u] <- %u\n", c.offset, v)
#define PRINT_U32(p, c, v)                                                                                                                                     \
  if (index == PRINT_THREAD_IDX)                                                                                                                               \
  printf(#p "[%u] <- %u\n" #p "[%u] <- %u\n", c.offset, v & 0xffff, c.offset + 1, v >> 16)
#define PRINT_R32(p, c, v)                                                                                                                                     \
  if (index == PRINT_THREAD_IDX)                                                                                                                               \
  printf(#p "[%u] <- %u\n", c.offset, v)
#define PRINT_TS(p, c, v)                                                                                                                                      \
  if (index == PRINT_THREAD_IDX)                                                                                                                               \
  printf(#p "[%u] <- %u\n" #p "[%u] <- %u\n", c.offset, v.get_low(), c.offset + 1, v.get_high())
#else
#define PRINT_U8(p, c, v)
#define PRINT_U16(p, c, v)
#define PRINT_U32(p, c, v)
#define PRINT_R32(p, c, v)
#define PRINT_TS(p, c, v)
#endif

} // namespace airbender::witness::memory