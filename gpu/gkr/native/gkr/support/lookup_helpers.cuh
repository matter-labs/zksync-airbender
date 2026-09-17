#pragma once

#include "eq_inline.cuh"
#include "kernel_helpers.cuh"

namespace airbender::gkr {

template <typename E> DEVICE_FORCEINLINE void gkr_eval_product(const E a, const E b, E &value) { value = E::mul(a, b); }

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_pair(const E a, const E b, const E c, const E d, E &num, E &den) {
  num = E::fma(a, d, E::mul(c, b));
  den = E::mul(b, d);
}

// Each block consumes B = blockDim.x contiguous input rows of pair blockIdx.y and fuses up to
// log2(B) halving rounds in shared memory. Every round's output is also written to DRAM for
// backward consumption.
template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_forward_tower(const gkr_dim_reducing_forward_tower_batch<E> &batch) {
  extern __shared__ E smem_tower[];
  E *smem_a = smem_tower;
  E *smem_b = smem_tower + blockDim.x;

  const gkr_dim_reducing_forward_tower_pair<E> &pair = batch.pairs[blockIdx.y];
  const bool pairwise = ((batch.pairwise_mask >> blockIdx.y) & 1u) != 0u;
  const unsigned tid = threadIdx.x;
  const unsigned bid = blockIdx.x;
  const unsigned base = bid * blockDim.x;

  if (base + tid < batch.input_len) {
    smem_a[tid] = load<E, ld_modifier::cs>(pair.input[0], base + tid);
    smem_b[tid] = load<E, ld_modifier::cs>(pair.input[1], base + tid);
  }
  __syncthreads();

  // For body launches, cur_len == blockDim.x == B. For the single-block tail where
  // input_len < B, only the first input_len threads carried real data.
  unsigned cur_len = blockDim.x < batch.input_len ? blockDim.x : batch.input_len;
  for (unsigned r = 0; r < batch.round_count; ++r) {
    cur_len >>= 1;
    E out_a;
    E out_b;
    const bool active = tid < cur_len;
    if (active) {
      if (pairwise) {
        gkr_eval_product(smem_a[2 * tid], smem_a[2 * tid + 1], out_a);
        gkr_eval_product(smem_b[2 * tid], smem_b[2 * tid + 1], out_b);
      } else {
        gkr_eval_lookup_pair(smem_a[2 * tid], smem_b[2 * tid], smem_a[2 * tid + 1], smem_b[2 * tid + 1], out_a, out_b);
      }
      store<E, st_modifier::cs>(pair.round_outputs[r][0], out_a, bid * cur_len + tid);
      store<E, st_modifier::cs>(pair.round_outputs[r][1], out_b, bid * cur_len + tid);
    }
    __syncthreads(); // Read phase complete; safe to overwrite shmem.
    if (active) {
      smem_a[tid] = out_a;
      smem_b[tid] = out_b;
    }
    __syncthreads(); // Next round may read a wider slice; ensure all writes visible.
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_forward_setup_generic_lookup(const gkr_forward_setup_generic_lookup_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;

  // Thread 0 also folds the decoder fill value (alpha^(column_count-1) * decoder_table_id)
  // into a 1-element device slot for the forward VM.
  if (gid == 0 && batch.decoder_fill_value_out != nullptr && batch.decoder_table_id != 0 && batch.column_count > 0) {
    const E last_alpha_power = ::ab_gkr_lookup_alpha_powers[batch.column_count - 1];
    const bf table_id = bf::from_u32_unchecked(batch.decoder_table_id);
    const E fill = E::mul(last_alpha_power, table_id);
    store<E, st_modifier::cs>(batch.decoder_fill_value_out, fill, 0);
  }

  if (gid >= row_count)
    return;

  E value = E::ZERO();

#pragma unroll
  for (unsigned column_idx = 0; column_idx < GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS; ++column_idx) {
    if (column_idx >= batch.column_count)
      break;

    const auto descriptor = batch.descriptors[column_idx];
    const bf input = load<bf, ld_modifier::cs>(descriptor.input, gid);
    const E alpha_power = ::ab_gkr_lookup_alpha_powers[column_idx];
    value = E::fma(alpha_power, input, value);
  }

  store<E, st_modifier::cs>(batch.output, value, gid);
}

template <typename E>
DEVICE_FORCEINLINE gkr_ext_initial_source<E> gkr_resolve_dim_reducing_initial_source(const gkr_dim_reducing_tables &tables, const gkr_source_record record) {
  bool first_access;
  u32 ptr_idx;
  u32 poly_idx;
  unpack_dim_reducing_source_u16(record.src, first_access, ptr_idx, poly_idx);
  const E *base_e = reinterpret_cast<const E *>(tables.bases[ptr_idx]);
  const u32 log2_stride = tables.log2_stride[ptr_idx];
  const E *start = base_e + (static_cast<size_t>(poly_idx) << log2_stride);
  return gkr_ext_initial_source<E>{start};
}

// Loads a slot's 2 batch challenges from the __constant__ table.
DEVICE_FORCEINLINE void gkr_load_slot_batch_challenges(const gkr_dim_reducing_slot &slot, e4 (&bc)[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT]) {
#pragma unroll
  for (unsigned t = 0; t < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++t)
    bc[t] = ::ab_gkr_dim_reducing_batch_challenge_table[slot.batch_exp[t]];
}

template <typename E>
DEVICE_FORCEINLINE gkr_ext_continuing_source<E> gkr_resolve_dim_reducing_continuation_source(const gkr_dim_reducing_tables &tables,
                                                                                             const gkr_source_record record) {
  bool first_access;
  u32 ptr_idx;
  u32 poly_idx;
  unpack_dim_reducing_source_u16(record.src, first_access, ptr_idx, poly_idx);
  E *source_base = reinterpret_cast<E *>(const_cast<u8 *>(tables.bases[ptr_idx]));
  const u32 source_log2_stride = tables.log2_stride[ptr_idx];
  E *source_start = source_base + (static_cast<size_t>(poly_idx) << source_log2_stride);
  u32 cache_slot;
  u32 cache_poly_idx;
  unpack_dim_reducing_cache_u16(record.cache, cache_slot, cache_poly_idx);
  E *cache_base = reinterpret_cast<E *>(const_cast<u8 *>(tables.bases[cache_slot]));
  const u32 cache_log2_stride = tables.log2_stride[cache_slot];
  E *cache_start = cache_base + (static_cast<size_t>(cache_poly_idx) << cache_log2_stride);
  return gkr_ext_continuing_source<E>{source_start, cache_start, first_access};
}

} // namespace airbender::gkr
