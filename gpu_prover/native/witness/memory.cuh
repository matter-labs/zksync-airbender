#pragma once

#include "../memory.cuh"
#include "ram_access.cuh"
#include "trace.cuh"

using namespace ::airbender::memory;
using namespace ::airbender::witness::ram_access;
using namespace ::airbender::witness::trace;

namespace airbender::witness::memory {

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

} // namespace airbender::witness::memory