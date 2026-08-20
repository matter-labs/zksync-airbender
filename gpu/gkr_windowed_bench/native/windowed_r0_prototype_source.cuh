#pragma once

#include "windowed_r0_executor.cuh"
#include "windowed_r0_prototype_cursor.cuh"

namespace airbender::gkr_windowed_bench {

constexpr u32 R0PB_TILE_ROWS = 32;
constexpr u32 R0PB_TILE_CORNERS = 8;
constexpr u32 R0PB_TILE_VALUES = R0PB_TILE_ROWS * R0PB_TILE_CORNERS;

template <typename Desc> DEVICE_FORCEINLINE const r0_prototype_common_desc &r0pb_common(const Desc &desc) { return desc.common; }

template <> DEVICE_FORCEINLINE const r0_prototype_common_desc &r0pb_common<r0_prototype_common_desc>(const r0_prototype_common_desc &desc) { return desc; }

template <typename Desc> DEVICE_FORCEINLINE const r0_window_addr &r0pb_window(const Desc &desc, const u16 window) {
  if constexpr (requires { desc.common.window_bases; })
    return desc.common.window_bases[window];
  else
    return desc.window_bases[window];
}

template <typename Desc> DEVICE_FORCEINLINE r0_bf_source r0pb_bf_source(const Desc &desc, const u16 packed) {
  const u16 window = packed >> R0_SOURCE_COLUMN_BITS;
  const u16 column = packed & R0_SOURCE_COLUMN_MASK;
  const r0_window_addr &address = r0pb_window(desc, window);
  const bf *base = reinterpret_cast<const bf *>(address.base);
  return {base + (static_cast<size_t>(column) << address.log2_stride), address.procedural_kind, address.origin == R0_ORIGIN_PROCEDURAL};
}

template <typename Desc> DEVICE_FORCEINLINE r0_e4_source r0pb_e4_source(const Desc &desc, const u16 packed) {
  const u16 window = packed >> R0_SOURCE_COLUMN_BITS;
  const u16 column = packed & R0_SOURCE_COLUMN_MASK;
  const r0_window_addr &address = r0pb_window(desc, window);
  const e4 *base = reinterpret_cast<const e4 *>(address.base);
  return {base + (static_cast<size_t>(column) << address.log2_stride)};
}

template <typename Desc> DEVICE_FORCEINLINE u16 r0pb_slot(const Desc &desc, const u16 source) { return desc.source_slots[source]; }

struct r0pb_ordinary_slot_resolver {
  template <typename Desc> DEVICE_FORCEINLINE static r0_bf_source bf_source(const Desc &desc, const decoded_r0_op &op, const u32 operand) {
    const u16 source = operand == 0 ? op.source_a : op.source_b;
    u16 packed = source;
    if constexpr (requires { desc.source_slots; }) {
      if (op.source_mode == R0PB_SOURCE_SLOT)
        packed = r0pb_slot(desc, source);
    }
    return r0pb_bf_source(desc, packed);
  }

  template <typename Desc> DEVICE_FORCEINLINE static r0_e4_source e4_source(const Desc &desc, const decoded_r0_op &op, const u32 operand) {
    const u16 source = operand == 0 ? op.source_a : op.source_b;
    u16 packed = source;
    if constexpr (requires { desc.source_slots; }) {
      if (op.source_mode == R0PB_SOURCE_SLOT)
        packed = r0pb_slot(desc, source);
    }
    return r0pb_e4_source(desc, packed);
  }
};

struct r0pb_ordinary_direct_resolver {
  template <typename Desc> DEVICE_FORCEINLINE static r0_bf_source bf_source(const Desc &desc, const decoded_r0_op &op, const u32 operand) {
    return r0pb_bf_source(desc, operand == 0 ? op.source_a : op.source_b);
  }

  template <typename Desc> DEVICE_FORCEINLINE static r0_e4_source e4_source(const Desc &desc, const decoded_r0_op &op, const u32 operand) {
    return r0pb_e4_source(desc, operand == 0 ? op.source_a : op.source_b);
  }
};

struct r0pb_shared_bf_source {
  const bf *column;

  DEVICE_FORCEINLINE bf value(const u32 index) const { return column[index]; }
};

struct r0pb_shared_e4_source {
  const e4 *column;

  DEVICE_FORCEINLINE e4 value(const u32 index) const { return column[index]; }
};

struct r0pb_materialized_resolver {
  u8 *storage;
  u32 bf_count = 0;
  u32 e4_count = 0;

  template <typename Desc> DEVICE_FORCEINLINE void begin_tile(const Desc &desc, const u32 tile_index, const u32 row_tile) {
    const r0_prototype_tile_header tile = desc.tiles[tile_index];
    bf_count = tile.source_counts & 0xffu;
    e4_count = tile.source_counts >> 8;
    const u32 bf_values = bf_count * R0PB_TILE_VALUES;
    const u32 e4_values = e4_count * R0PB_TILE_VALUES;
    bf *bf_storage = reinterpret_cast<bf *>(storage);
    e4 *e4_storage = reinterpret_cast<e4 *>(storage + static_cast<size_t>(bf_values) * sizeof(bf));
    for (u32 index = threadIdx.x; index < bf_values + e4_values; index += blockDim.x) {
      if (index < bf_values) {
        const u32 source = index / R0PB_TILE_VALUES;
        const u32 element = index % R0PB_TILE_VALUES;
        const u32 global_row = row_tile * R0PB_TILE_ROWS + element / R0PB_TILE_CORNERS;
        const u32 global_index = (global_row << 3) | (element & 7u);
        const u16 packed = desc.tile_sources[tile.source_offset + source] & 0x7fffu;
        bf_storage[index] = global_row < (1u << desc.ordinary.common.log_rows) ? r0pb_bf_source(desc.ordinary, packed).value(global_index) : bf::ZERO();
      } else {
        const u32 e4_index = index - bf_values;
        const u32 source = e4_index / R0PB_TILE_VALUES;
        const u32 element = e4_index % R0PB_TILE_VALUES;
        const u32 global_row = row_tile * R0PB_TILE_ROWS + element / R0PB_TILE_CORNERS;
        const u32 global_index = (global_row << 3) | (element & 7u);
        const u16 packed = desc.tile_sources[tile.source_offset + bf_count + source] & 0x7fffu;
        e4_storage[e4_index] = global_row < (1u << desc.ordinary.common.log_rows) ? r0pb_e4_source(desc.ordinary, packed).value(global_index) : e4::ZERO();
      }
    }
    __syncthreads();
  }

  DEVICE_FORCEINLINE r0pb_shared_bf_source bf_source(const u8 local) const {
    const bf *values = reinterpret_cast<const bf *>(storage);
    return {values + static_cast<size_t>(local) * R0PB_TILE_VALUES};
  }

  DEVICE_FORCEINLINE r0pb_shared_e4_source e4_source(const u8 local) const {
    const e4 *values = reinterpret_cast<const e4 *>(storage + static_cast<size_t>(bf_count) * R0PB_TILE_VALUES * sizeof(bf));
    return {values + static_cast<size_t>(local - bf_count) * R0PB_TILE_VALUES};
  }

  DEVICE_FORCEINLINE void end_tile() const { __syncthreads(); }
};

} // namespace airbender::gkr_windowed_bench
