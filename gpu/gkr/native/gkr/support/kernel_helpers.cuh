#pragma once

#include "descriptors.cuh"

namespace airbender::gkr {

// bit 15 = first_access, bits 14..11 = ptr_idx (4 bits, 16 slots),
// bits 10..0 = poly_idx (11 bits, max 2048).
DEVICE_FORCEINLINE void unpack_dim_reducing_source_u16(u16 packed, bool &first_access, u32 &ptr_idx, u32 &poly_idx) {
  first_access = (packed & 0x8000u) != 0;
  ptr_idx = (packed >> 11) & 0xFu;
  poly_idx = packed & 0x07FFu;
}

DEVICE_FORCEINLINE void unpack_dim_reducing_cache_u16(u16 packed, u32 &ptr_idx, u32 &poly_idx) {
  ptr_idx = (packed >> 11) & 0xFu;
  poly_idx = packed & 0x07FFu;
}

DEVICE_FORCEINLINE bf gkr_virtual_base_value(const gkr_base_source_kind kind, const unsigned row) {
  switch (kind) {
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS:
    return row < (1u << 16) ? bf::from_u32_unchecked(row) : bf::ZERO();
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP:
    return row < (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS) ? bf::from_u32_unchecked(row) : bf::ZERO();
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW:
    return bf::from_u32_unchecked((row << 2) & 0xffffu);
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH:
    return bf::from_u32_unchecked(row >> 14);
  case GKR_BASE_SOURCE_EMPTY:
  case GKR_BASE_SOURCE_REAL:
  default:
    return bf::ZERO();
  }
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_value(const gkr_ext_initial_source<E> &source, const unsigned index) {
  return load<E, ld_modifier::cs>(source.start, index);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_continuing_value(const gkr_ext_continuing_source<E> &source, const E folding_challenge, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_start, index);

  const E f0 = load<E, ld_modifier::cs>(source.previous_layer_start, index);
  const E f1 = load<E, ld_modifier::cs>(source.previous_layer_start, source.this_layer_size + index);
  const E diff = E::sub(f1, f0);
  const E folded = E::fma(folding_challenge, diff, f0);
  store<E, st_modifier::cs>(source.this_layer_start, folded, index);
  return folded;
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_delta(const gkr_ext_initial_source<E> &source, const unsigned index) {
  const E f0 = gkr_get_initial_value(source, index);
  const E f1 = gkr_get_initial_value(source, source.next_layer_size + index);
  return E::sub(f1, f0);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_get_continuing_points(const gkr_ext_continuing_source<E> &source, const E folding_challenge, const unsigned index, E &f0,
                                                  E &delta) {
  f0 = gkr_get_continuing_value(source, folding_challenge, index);
  const E f1 = gkr_get_continuing_value(source, folding_challenge, source.next_layer_size + index);
  delta = E::sub(f1, f0);
}

DEVICE_FORCEINLINE unsigned gkr_eq_group_count(const unsigned challenge_count) {
  return challenge_count == 0 ? 0 : (challenge_count + GKR_EQ_GROUP_SIZE - 1) / GKR_EQ_GROUP_SIZE;
}

DEVICE_FORCEINLINE unsigned gkr_eq_group_size(const unsigned challenge_count, const unsigned group_idx) {
  const unsigned group_start = group_idx * GKR_EQ_GROUP_SIZE;
  if (group_start >= challenge_count)
    return 0;
  const unsigned remaining = challenge_count - group_start;
  return remaining < GKR_EQ_GROUP_SIZE ? remaining : GKR_EQ_GROUP_SIZE;
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_group_tables_from_point(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                             E *eq_group_tables) {
  const unsigned group_idx = blockIdx.x;
  const unsigned group_size = gkr_eq_group_size(challenge_count, group_idx);
  if (group_size == 0)
    return;

  const unsigned tid = threadIdx.x;
  const unsigned chunk_count = (group_size + GKR_EQ_CHUNK_SIZE - 1) / GKR_EQ_CHUNK_SIZE;
  const unsigned group_start = group_idx * GKR_EQ_GROUP_SIZE;
  __shared__ E chunk_tables[GKR_EQ_MAX_CHUNKS_PER_GROUP][GKR_EQ_CHUNK_TABLE_LEN];

  if (tid < chunk_count * GKR_EQ_CHUNK_TABLE_LEN) {
    const unsigned chunk_idx = tid / GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned chunk_table_idx = tid % GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned variable_offset = chunk_idx * GKR_EQ_CHUNK_SIZE;
    const unsigned remaining = group_size - variable_offset;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned chunk_len = 1u << chunk_size;
    if (chunk_table_idx < chunk_len) {
      const unsigned variable_idx = group_start + variable_offset;
      const unsigned first_bit = chunk_size == 2 ? ((chunk_table_idx >> 1) & 1u) : (chunk_table_idx & 1u);
      const E first_challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + variable_idx);
      E value = first_bit ? first_challenge : E::sub(E::ONE(), first_challenge);
      if (chunk_size == 2) {
        const unsigned low_bit = chunk_table_idx & 1u;
        const E second_challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + variable_idx + 1);
        const E second_term = low_bit ? second_challenge : E::sub(E::ONE(), second_challenge);
        value = E::mul(value, second_term);
      }
      chunk_tables[chunk_idx][chunk_table_idx] = value;
    }
  }
  __syncthreads();

  const unsigned group_len = 1u << group_size;
  if (tid >= group_len)
    return;

  E acc;
  unsigned consumed_bits = 0;
  for (unsigned chunk_idx = 0; chunk_idx < chunk_count; ++chunk_idx) {
    const unsigned remaining = group_size - consumed_bits;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned shift = group_size - consumed_bits - chunk_size;
    const unsigned chunk_table_idx = (tid >> shift) & ((1u << chunk_size) - 1u);
    const E factor = chunk_tables[chunk_idx][chunk_table_idx];
    acc = (chunk_idx == 0) ? factor : E::mul(acc, factor);
    consumed_bits += chunk_size;
  }

  store<E, st_modifier::cs>(eq_group_tables + group_idx * GKR_EQ_GROUP_TABLE_LEN, acc, tid);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_values_from_group_tables(const E *eq_group_tables, const unsigned challenge_count, E *eq_values, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  if (challenge_count == 0) {
    store<E, st_modifier::cs>(eq_values, E::ONE(), gid);
    return;
  }

  E acc;
  const unsigned groups_count = gkr_eq_group_count(challenge_count);
  unsigned consumed_bits = 0;
  for (unsigned group_idx = 0; group_idx < groups_count; ++group_idx) {
    const unsigned group_size = gkr_eq_group_size(challenge_count, group_idx);
    const unsigned shift = challenge_count - consumed_bits - group_size;
    const unsigned local_gid = (gid >> shift) & ((1u << group_size) - 1u);
    const E factor = load<E, ld_modifier::cs>(eq_group_tables + group_idx * GKR_EQ_GROUP_TABLE_LEN, local_gid);
    acc = (group_idx == 0) ? factor : E::mul(acc, factor);
    consumed_bits += group_size;
  }

  store<E, st_modifier::cs>(eq_values, acc, gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_trace_holder_partials_shfl_xor_words(const E value, const int lane_mask, const unsigned mask, const unsigned width) {
  E result;
  constexpr unsigned words_count = sizeof(E) / sizeof(unsigned);
  const unsigned *src = reinterpret_cast<const unsigned *>(&value);
  unsigned *dst = reinterpret_cast<unsigned *>(&result);
#pragma unroll
  for (unsigned i = 0; i < words_count; ++i)
    dst[i] = shfl_xor(mask, src[i], lane_mask, width);
  return result;
}

template <typename E> DEVICE_FORCEINLINE E gkr_trace_holder_partials_shfl_xor(const E value, const int lane_mask, const unsigned mask = UINT32_MAX) {
  if constexpr (sizeof(E) % sizeof(uint4) == 0) {
    E result;
    constexpr unsigned words_count = sizeof(E) / sizeof(uint4);
    const uint4 *src = reinterpret_cast<const uint4 *>(&value);
    uint4 *dst = reinterpret_cast<uint4 *>(&result);
#pragma unroll
    for (unsigned i = 0; i < words_count; ++i)
      dst[i] = shfl_xor(mask, src[i], lane_mask, GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE);
    return result;
  } else if constexpr (sizeof(E) % sizeof(uint2) == 0) {
    E result;
    constexpr unsigned words_count = sizeof(E) / sizeof(uint2);
    const uint2 *src = reinterpret_cast<const uint2 *>(&value);
    uint2 *dst = reinterpret_cast<uint2 *>(&result);
#pragma unroll
    for (unsigned i = 0; i < words_count; ++i)
      dst[i] = shfl_xor(mask, src[i], lane_mask, GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE);
    return result;
  } else {
    return gkr_trace_holder_partials_shfl_xor_words(value, lane_mask, mask, GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE);
  }
}

template <typename E> DEVICE_FORCEINLINE E gkr_trace_holder_partials_warp_reduce_sum(E value) {
#pragma unroll
  for (int lane_mask = GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE >> 1; lane_mask > 0; lane_mask >>= 1)
    value = E::add(value, gkr_trace_holder_partials_shfl_xor(value, lane_mask));
  return value;
}

struct __align__(16) gkr_trace_holder_bf4 {
  bf values[4];
};

template <typename E> struct gkr_trace_holder_eq_dense {
  const E *eq_values;
  DEVICE_FORCEINLINE void load4(const unsigned row, E (&eq)[4]) const {
#pragma unroll
    for (unsigned i = 0; i < 4; ++i)
      eq[i] = load<E, ld_modifier::cs>(eq_values, row + i);
  }
};

template <typename E, typename EqFn>
DEVICE_FORCEINLINE void gkr_trace_holder_block_partials(const bf *raw_values, const EqFn eq_fn, E *block_partials, const unsigned trace_len,
                                                        const unsigned column_start, const unsigned chunk_cols, const unsigned blocks_count) {
  static_assert(GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK % GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE == 0);
  static_assert(sizeof(gkr_trace_holder_bf4) == 4 * sizeof(bf));

  const unsigned tid = threadIdx.x;
  const unsigned lane_id = tid & (GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE - 1);
  const unsigned warp_id = tid / GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE;
  const unsigned packed_trace_len = trace_len >> 2;
  const unsigned packed_gid = blockIdx.x * blockDim.x + tid;
  const unsigned packed_stride = gridDim.x * blockDim.x;
  E accumulators[GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK] = {
      E::ZERO(),
      E::ZERO(),
      E::ZERO(),
      E::ZERO(),
  };

  for (unsigned packed_row = packed_gid; packed_row < packed_trace_len; packed_row += packed_stride) {
    const unsigned row = packed_row << 2;
    E eq[4];
    eq_fn.load4(row, eq);
#pragma unroll
    for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
      if (local_col >= chunk_cols)
        break;
      const unsigned column = column_start + local_col;
      const size_t row_offset = static_cast<size_t>(column) * trace_len + row;
      const auto values = load<gkr_trace_holder_bf4, ld_modifier::cs>(reinterpret_cast<const gkr_trace_holder_bf4 *>(raw_values), row_offset >> 2);
      E partial = E::mul(values.values[0], eq[0]);
      partial = E::fma(eq[1], values.values[1], partial);
      partial = E::fma(eq[2], values.values[2], partial);
      partial = E::fma(eq[3], values.values[3], partial);
      accumulators[local_col] = E::add(accumulators[local_col], partial);
    }
  }

  __shared__ E warp_partials[GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK][GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK];
#pragma unroll
  for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
    if (local_col >= chunk_cols)
      break;
    const E warp_sum = gkr_trace_holder_partials_warp_reduce_sum(accumulators[local_col]);
    if (lane_id == 0)
      warp_partials[local_col][warp_id] = warp_sum;
  }
  __syncthreads();

  if (warp_id != 0)
    return;

#pragma unroll
  for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
    if (local_col >= chunk_cols)
      break;
    E block_sum = lane_id < GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK ? warp_partials[local_col][lane_id] : E::ZERO();
    block_sum = gkr_trace_holder_partials_warp_reduce_sum(block_sum);
    if (lane_id == 0) {
      const size_t partial_offset = static_cast<size_t>(column_start + local_col) * blocks_count + blockIdx.x;
      store<E, st_modifier::cs>(block_partials, block_sum, partial_offset);
    }
  }
}

// Launch contract: blockDim = one warp, blockIdx.x = column.
template <typename E> DEVICE_FORCEINLINE void gkr_trace_holder_column_sums(const E *block_partials, E *column_sums, const unsigned blocks_count) {
  const unsigned lane_id = threadIdx.x;
  const size_t column_base = static_cast<size_t>(blockIdx.x) * blocks_count;
  E acc = E::ZERO();
  for (unsigned i = lane_id; i < blocks_count; i += GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE)
    acc = E::add(acc, load<E, ld_modifier::cs>(block_partials, column_base + i));
  acc = gkr_trace_holder_partials_warp_reduce_sum(acc);
  if (lane_id == 0)
    store<E, st_modifier::cs>(column_sums, acc, blockIdx.x);
}

} // namespace airbender::gkr
