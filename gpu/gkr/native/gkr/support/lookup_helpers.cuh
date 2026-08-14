#pragma once

#include "eq_inline.cuh"
#include "kernel_helpers.cuh"

namespace airbender::gkr {

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0_values(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E batch_challenge,
                                                   const unsigned gid, E &c0, E &c1) {
  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_value = gkr_get_initial_value(outputs[0], gid);
  const E delta_even = gkr_get_initial_delta(inputs[0], even_index);
  const E delta_odd = gkr_get_initial_delta(inputs[0], odd_index);

  c0 = E::mul(batch_challenge, output_value);
  c1 = E::mul(batch_challenge, E::mul(delta_even, delta_odd));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0_values(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E batch_challenge_0,
                                                 const E batch_challenge_1, const unsigned gid, E &c0, E &c1) {
  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_num = gkr_get_initial_value(outputs[0], gid);
  const E output_den = gkr_get_initial_value(outputs[1], gid);

  const E a = gkr_get_initial_delta(inputs[0], even_index);
  const E b = gkr_get_initial_delta(inputs[1], even_index);
  const E c = gkr_get_initial_delta(inputs[0], odd_index);
  const E d = gkr_get_initial_delta(inputs[1], odd_index);

  const E num = E::fma(a, d, E::mul(c, b));
  const E den = E::mul(b, d);

  c0 = E::fma(batch_challenge_0, output_num, E::mul(batch_challenge_1, output_den));
  c1 = E::fma(batch_challenge_0, num, E::mul(batch_challenge_1, den));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_continuation_values(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E batch_challenge,
                                                         const unsigned gid, E &c0, E &c1) {
  const E current_folding_challenge = folding_challenge[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E even_f0;
  E even_f1_or_delta;
  gkr_get_continuing_points<E>(inputs[0], current_folding_challenge, even_index, even_f0, even_f1_or_delta);

  E odd_f0;
  E odd_f1_or_delta;
  gkr_get_continuing_points<E>(inputs[0], current_folding_challenge, odd_index, odd_f0, odd_f1_or_delta);

  c0 = E::mul(batch_challenge, E::mul(even_f0, odd_f0));
  c1 = E::mul(batch_challenge, E::mul(even_f1_or_delta, odd_f1_or_delta));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_continuation_values(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E batch_challenge_0,
                                                       const E batch_challenge_1, const unsigned gid, E &out0, E &out1) {
  const E current_folding_challenge = folding_challenge[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E a0;
  E a1;
  gkr_get_continuing_points<E>(inputs[0], current_folding_challenge, even_index, a0, a1);
  E b0;
  E b1;
  gkr_get_continuing_points<E>(inputs[1], current_folding_challenge, even_index, b0, b1);
  E c0;
  E c1;
  gkr_get_continuing_points<E>(inputs[0], current_folding_challenge, odd_index, c0, c1);
  E d0;
  E d1;
  gkr_get_continuing_points<E>(inputs[1], current_folding_challenge, odd_index, d0, d1);

  const E num0 = E::fma(a0, d0, E::mul(c0, b0));
  const E den0 = E::mul(b0, d0);
  const E num1 = E::fma(a1, d1, E::mul(c1, b1));
  const E den1 = E::mul(b1, d1);

  out0 = E::fma(batch_challenge_0, num0, E::mul(batch_challenge_1, den0));
  out1 = E::fma(batch_challenge_0, num1, E::mul(batch_challenge_1, den1));
}

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
      if (pair.kind == GKR_DIM_REDUCING_FORWARD_TOWER_PAIRWISE2) {
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

// Round-0 inputs have `next_layer_size = 2 * acc_size`; output reads ignore it.
template <typename E>
DEVICE_FORCEINLINE gkr_ext_initial_source<E> gkr_resolve_dim_reducing_initial_source(const gkr_dim_reducing_tables &tables, const gkr_source_record record,
                                                                                     const unsigned acc_size) {
  bool first_access;
  u32 ptr_idx;
  u32 poly_idx;
  unpack_dim_reducing_source_u16(record.src, first_access, ptr_idx, poly_idx);
  const E *base_e = reinterpret_cast<const E *>(tables.bases[ptr_idx]);
  const u32 log2_stride = tables.log2_stride[ptr_idx];
  const E *start = base_e + (static_cast<size_t>(poly_idx) << log2_stride);
  return gkr_ext_initial_source<E>{start, 2u * acc_size};
}

template <typename E>
DEVICE_FORCEINLINE void gkr_dim_reducing_round0_batched_compact(const gkr_dim_reducing_round0_batch_compact<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    gkr_ext_initial_source<E> inputs[GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD];
    gkr_ext_initial_source<E> outputs[GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD];
    for (unsigned k = 0; k < record.inputs.count; ++k) {
      inputs[k] = gkr_resolve_dim_reducing_initial_source<E>(batch.tables, batch.inline_payload[record.inputs.offset + k], acc_size);
    }
    for (unsigned k = 0; k < record.outputs.count; ++k) {
      outputs[k] = gkr_resolve_dim_reducing_initial_source<E>(batch.tables, batch.inline_payload[record.outputs.offset + k], acc_size);
    }
    E c0;
    E c1;
    switch (record.kind) {
    case GKR_DIM_REDUCING_PAIRWISE:
      gkr_pairwise_round0_values(inputs, outputs, ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset], gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_round0_values(inputs, outputs, ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset],
                               ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset + 1], gid, c0, c1);
      break;
    default:
      return;
    }
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = gkr_compute_eq_inline<E>(batch.eq_low, batch.eq_sizes, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

// Round-1 (sumcheck step 1) source resolver. The u16 encodes the GKR ext
// storage slot of the original input poly; `previous_layer_start` is that
// poly's start, and `this_layer_start` is the matching folding-buffer slot
// from the record's cache half. this_layer_size and
// next_layer_size at step 1 are uniformly `2 * acc_size` and `acc_size`.
template <typename E>
DEVICE_FORCEINLINE gkr_ext_continuing_source<E> gkr_resolve_dim_reducing_round1_source(const gkr_dim_reducing_tables &tables, const gkr_source_record record,
                                                                                       const unsigned acc_size) {
  bool first_access;
  u32 ptr_idx;
  u32 poly_idx;
  unpack_dim_reducing_source_u16(record.src, first_access, ptr_idx, poly_idx);
  const E *poly_base = reinterpret_cast<const E *>(tables.bases[ptr_idx]);
  const u32 poly_log2_stride = tables.log2_stride[ptr_idx];
  const E *previous = poly_base + (static_cast<size_t>(poly_idx) << poly_log2_stride);
  u32 buffer_slot;
  u32 buffer_poly_idx;
  unpack_dim_reducing_cache_u16(record.cache, buffer_slot, buffer_poly_idx);
  E *buffer_base = reinterpret_cast<E *>(const_cast<u8 *>(tables.bases[buffer_slot]));
  const u32 buffer_log2_stride = tables.log2_stride[buffer_slot];
  E *this_layer = buffer_base + (static_cast<size_t>(buffer_poly_idx) << buffer_log2_stride);
  // At sumcheck step 1, `this_layer_size` is the f0/f1 stride within the
  // previous (= original input) poly, which is `poly_size / 2 = 4 * acc_size`
  // (input size at step 1 = 8 * acc_size since acc_size = trace_len_after_reduction/4).
  // `next_layer_size` is the produced fold's stride = `this_layer_size / 2 = 2 * acc_size`.
  return gkr_ext_continuing_source<E>{previous, this_layer, 4u * acc_size, 2u * acc_size, first_access};
}

template <typename E>
DEVICE_FORCEINLINE void gkr_dim_reducing_round1_batched_compact_inner(const gkr_dim_reducing_continuation_batch_compact<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    gkr_ext_continuing_source<E> inputs[GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD];
    for (unsigned k = 0; k < record.inputs.count; ++k) {
      inputs[k] = gkr_resolve_dim_reducing_round1_source<E>(batch.tables, batch.inline_payload[record.inputs.offset + k], acc_size);
    }
    E c0;
    E c1;
    switch (record.kind) {
    case GKR_DIM_REDUCING_PAIRWISE:
      gkr_pairwise_continuation_values<E>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[0],
                                          ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset], gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_continuation_values<E>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[0],
                                        ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset],
                                        ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset + 1], gid, c0, c1);
      break;
    default:
      return;
    }
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = gkr_compute_eq_inline<E>(batch.eq_low, batch.eq_sizes, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

// Continuation sources read the current round arena and write the next one.
template <typename E>
DEVICE_FORCEINLINE gkr_ext_continuing_source<E> gkr_resolve_dim_reducing_continuation_source(const gkr_dim_reducing_tables &tables,
                                                                                             const gkr_source_record record, const unsigned acc_size) {
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
  // At step k >= 2, `this_layer_size = 4 * acc_size` (the f0/f1 stride within
  // the previous-layer span = trace_len_after_reduction >> (k-1) = 4 * acc_size_at_step_k);
  // `next_layer_size = this_layer_size / 2 = 2 * acc_size`.
  return gkr_ext_continuing_source<E>{source_start, cache_start, 4u * acc_size, 2u * acc_size, first_access};
}

template <typename E>
DEVICE_FORCEINLINE void gkr_dim_reducing_continuation_batched_compact_inner(const gkr_dim_reducing_continuation_batch_compact<E> &batch,
                                                                            const unsigned acc_size, const unsigned step) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    gkr_ext_continuing_source<E> inputs[GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD];
    for (unsigned k = 0; k < record.inputs.count; ++k) {
      inputs[k] = gkr_resolve_dim_reducing_continuation_source<E>(batch.tables, batch.inline_payload[record.inputs.offset + k], acc_size);
    }
    E c0;
    E c1;
    switch (record.kind) {
    case GKR_DIM_REDUCING_PAIRWISE:
      gkr_pairwise_continuation_values<E>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[step - 1],
                                          ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset], gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_continuation_values<E>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[step - 1],
                                        ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset],
                                        ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset + 1], gid, c0, c1);
      break;
    default:
      return;
    }
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = gkr_compute_eq_inline<E>(batch.eq_low, batch.eq_sizes, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

} // namespace airbender::gkr
