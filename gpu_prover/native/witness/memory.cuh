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

#define MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT 4

struct MemoryQueriesTimestampComparisonAuxVars {
  const u32 count;
  const ColumnAddress addresses[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
};

struct ShuffleRamAccessSets {
  const u32 count;
  const ShuffleRamQueryColumns sets[MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
};

#define MAX_INITS_AND_TEARDOWNS_SETS_COUNT 16

struct ShuffleRamAuxComparisonSets {
  const u32 count;
  const ShuffleRamAuxComparisonSet sets[MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
};

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
#define PRINT_TS(p, c, v)                                                                                                                                      \
  if (index == PRINT_THREAD_IDX)                                                                                                                               \
  printf(#p "[%u] <- %u\n" #p "[%u] <- %u\n", c.offset, v.get_low(), c.offset + 1, v.get_high())
#else
#define PRINT_U8(p, c, v)
#define PRINT_U16(p, c, v)
#define PRINT_U32(p, c, v)
#define PRINT_TS(p, c, v)
#endif

template <bool COMPUTE_WITNESS>
DEVICE_FORCEINLINE void process_inits_and_teardowns(const ShuffleRamInitAndTeardownLayouts &init_and_teardown_layouts,
                                                    const ShuffleRamInitsAndTeardowns &inits_and_teardowns,
                                                    const ShuffleRamAuxComparisonSets &aux_comparison_sets, const matrix_setter<bf, st_modifier::cg> memory,
                                                    const matrix_setter<bf, st_modifier::cg> witness, const unsigned count, const unsigned index) {
  const InitAndTeardown *data = inits_and_teardowns.inits_and_teardowns + index;
#pragma unroll
  for (u32 i = 0; i < MAX_INITS_AND_TEARDOWNS_SETS_COUNT; ++i, data += count) {
    if (i == init_and_teardown_layouts.count)
      break;
    const auto [addresses_columns, values_columns, timestamps_columns] = init_and_teardown_layouts.layouts[i];
    const auto [init_address, teardown_value, teardown_timestamp] = *data;
    write_u32_value(addresses_columns, init_address, memory);
    PRINT_U32(M, addresses_columns, init_address);
    write_u32_value(values_columns, teardown_value, memory);
    PRINT_U32(M, values_columns, teardown_value);
    write_timestamp_value(timestamps_columns, teardown_timestamp, memory);
    PRINT_TS(M, timestamps_columns, teardown_timestamp);
    if (!COMPUTE_WITNESS)
      continue;
    u16 low_value;
    u16 high_value;
    bool intermediate_borrow_value;
    bool final_borrow_value;
    if (index == count - 1) {
      low_value = 0;
      high_value = 0;
      intermediate_borrow_value = false;
      final_borrow_value = true;
    } else {
      const u32 next_row_lazy_init_address_value = data[1].address;
      const auto [a_low, a_high] = u32_to_u16_tuple(init_address);
      const auto [b_low, b_high] = u32_to_u16_tuple(next_row_lazy_init_address_value);
      const auto [low, intermediate_borrow] = sub_borrow(a_low, b_low);
      const auto [t, of0] = sub_borrow(a_high, b_high);
      const auto [high, of1] = sub_borrow(t, intermediate_borrow);
      low_value = low;
      high_value = high;
      intermediate_borrow_value = intermediate_borrow;
      final_borrow_value = of0 || of1;
    }
    const auto [aux_low_high, intermediate_borrow_address, final_borrow_address] = aux_comparison_sets.sets[i];
    const auto [low_address, high_address] = aux_low_high;
    write_u16_value(low_address, low_value, witness);
    PRINT_U16(W, low_address, low_value);
    write_u16_value(high_address, high_value, witness);
    PRINT_U16(W, high_address, high_value);
    write_bool_value(intermediate_borrow_address, intermediate_borrow_value, witness);
    PRINT_U16(W, intermediate_borrow_address, intermediate_borrow_value);
    write_bool_value(final_borrow_address, final_borrow_value, witness);
    PRINT_U16(W, final_borrow_address, final_borrow_value);
  }
}

} // namespace airbender::witness::memory