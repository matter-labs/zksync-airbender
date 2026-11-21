#pragma once

#include "gkr/support/descriptors.cuh"

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

DEVICE_FORCEINLINE unsigned gkr_dim_reducing_ancestor_index(const unsigned index) { return GKR_DIM_REDUCING_PAIR_STRIDE * (index & ~1u) + (index & 1u); }

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

template <typename E> struct gkr_global_eq_group_table_writer {
  E *destination;

  DEVICE_FORCEINLINE void operator()(const unsigned index, const E &value) const { store<E, st_modifier::cs>(destination, value, index); }
};

template <typename E> struct gkr_shared_eq_group_table_writer {
  E *destination;

  DEVICE_FORCEINLINE void operator()(const unsigned index, const E &value) const { destination[index] = value; }
};

template <typename E, typename DestinationWriter>
DEVICE_FORCEINLINE void gkr_build_eq_group_table_from_point(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                            const unsigned group_idx, const DestinationWriter &write_destination) {
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
      // LSB relabeling: the reversal is WITHIN `[challenge_offset, challenge_offset + challenge_count)`.
      const unsigned first_idx = challenge_offset + challenge_count - 1 - variable_idx;
      const unsigned first_bit = chunk_size == 2 ? ((chunk_table_idx >> 1) & 1u) : (chunk_table_idx & 1u);
      const E first_challenge = load<E, ld_modifier::cs>(claim_point, first_idx);
      E value = first_bit ? first_challenge : E::sub(E::ONE(), first_challenge);
      if (chunk_size == 2) {
        const unsigned low_bit = chunk_table_idx & 1u;
        const E second_challenge = load<E, ld_modifier::cs>(claim_point, first_idx - 1);
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

  write_destination(group_idx * GKR_EQ_GROUP_TABLE_LEN + tid, acc);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_group_tables_from_point(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                             E *eq_group_tables) {
  const gkr_global_eq_group_table_writer<E> write_destination{eq_group_tables};
  gkr_build_eq_group_table_from_point<E>(claim_point, challenge_offset, challenge_count, blockIdx.x, write_destination);
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

template <typename E> struct gkr_trace_holder_eq_dense {
  const E *eq_values;
  template <unsigned PACK_LOG2> DEVICE_FORCEINLINE void load_pack(const unsigned row, E (&eq)[1u << PACK_LOG2]) const {
#pragma unroll
    for (unsigned i = 0; i < (1u << PACK_LOG2); ++i)
      eq[i] = load<E, ld_modifier::cs>(eq_values, row + i);
  }
};

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
