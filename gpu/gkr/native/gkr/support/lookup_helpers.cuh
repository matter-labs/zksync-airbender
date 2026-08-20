#pragma once

#include "eq_inline.cuh"
#include "kernel_helpers.cuh"

namespace airbender::gkr {

// Slot bodies accumulate into the round's (constant-term, t^2-coefficient) pair;
// the round's linear coefficient is recovered from the running claim downstream,
// which is why only two values per round leave the kernel.

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0_accumulate(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *bc,
                                                       const unsigned gid, E &acc0, E &acc1) {
  const unsigned even_index = gid * GKR_DIM_REDUCING_ROW_SPAN;
  const unsigned odd_index = even_index + 1;
  const unsigned output_index = gid * GKR_DIM_REDUCING_PAIR_STRIDE;

#pragma unroll
  for (unsigned t = 0; t < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++t) {
    // Round 0 reads the forward tower's own output as the value at t = 0; the
    // row's X = 0 half is coordinate 2 * gid.
    const E output_value = gkr_get_initial_value(outputs[t], output_index);
    const E delta_even = gkr_get_initial_delta(inputs[t], even_index);
    const E delta_odd = gkr_get_initial_delta(inputs[t], odd_index);

    acc0 = E::fma(bc[t], output_value, acc0);
    acc1 = E::fma(bc[t], E::mul(delta_even, delta_odd), acc1);
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0_accumulate(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *bc,
                                                     const unsigned gid, E &acc0, E &acc1) {
  const unsigned even_index = gid * GKR_DIM_REDUCING_ROW_SPAN;
  const unsigned odd_index = even_index + 1;
  const unsigned output_index = gid * GKR_DIM_REDUCING_PAIR_STRIDE;

  const E output_num = gkr_get_initial_value(outputs[0], output_index);
  const E output_den = gkr_get_initial_value(outputs[1], output_index);

  const E a = gkr_get_initial_delta(inputs[0], even_index);
  const E b = gkr_get_initial_delta(inputs[1], even_index);
  const E c = gkr_get_initial_delta(inputs[0], odd_index);
  const E d = gkr_get_initial_delta(inputs[1], odd_index);

  const E num = E::fma(a, d, E::mul(c, b));
  const E den = E::mul(b, d);

  acc0 = E::fma(bc[0], output_num, E::fma(bc[1], output_den, acc0));
  acc1 = E::fma(bc[0], num, E::fma(bc[1], den, acc1));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_continuation_accumulate(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *bc,
                                                             const unsigned gid, E &acc0, E &acc1) {
  const E current_folding_challenge = folding_challenge[0];

  const unsigned even_index = gid * GKR_DIM_REDUCING_ROW_SPAN;
  const unsigned odd_index = even_index + 1;

#pragma unroll
  for (unsigned t = 0; t < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++t) {
    E even_f0;
    E even_delta;
    gkr_get_continuing_points<E>(inputs[t], current_folding_challenge, even_index, even_f0, even_delta);

    E odd_f0;
    E odd_delta;
    gkr_get_continuing_points<E>(inputs[t], current_folding_challenge, odd_index, odd_f0, odd_delta);

    acc0 = E::fma(bc[t], E::mul(even_f0, odd_f0), acc0);
    acc1 = E::fma(bc[t], E::mul(even_delta, odd_delta), acc1);
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_continuation_accumulate(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *bc,
                                                           const unsigned gid, E &acc0, E &acc1) {
  const E current_folding_challenge = folding_challenge[0];

  const unsigned even_index = gid * GKR_DIM_REDUCING_ROW_SPAN;
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

  acc0 = E::fma(bc[0], num0, E::fma(bc[1], den0, acc0));
  acc1 = E::fma(bc[0], num1, E::fma(bc[1], den1, acc1));
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

// Round 0 addresses inputs and outputs by index alone: the f0/f1 pair stride is
// the layout constant `GKR_DIM_REDUCING_PAIR_STRIDE`, not a span size.
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

template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_round0_batched_compact(const gkr_dim_reducing_batch<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  // Fully unrolled: `slot` is a compile-time constant in each copy, so the
  // pairwise/lookup selection folds away and no dispatch survives codegen.
#pragma unroll
  for (unsigned slot = 0; slot < GKR_DIM_REDUCING_SLOTS; ++slot) {
    if ((batch.enabled_mask & (1u << slot)) == 0)
      continue;
    const gkr_dim_reducing_slot &desc = batch.slots[slot];

    E bc[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
    gkr_load_slot_batch_challenges(desc, bc);

    gkr_ext_initial_source<E> inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
    gkr_ext_initial_source<E> outputs[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
#pragma unroll
    for (unsigned k = 0; k < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++k)
      inputs[k] = gkr_resolve_dim_reducing_initial_source<E>(batch.tables, desc.io[k]);
#pragma unroll
    for (unsigned k = 0; k < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++k)
      outputs[k] = gkr_resolve_dim_reducing_initial_source<E>(batch.tables, desc.io[GKR_DIM_REDUCING_INPUTS_PER_SLOT + k]);

    if ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK >> slot) & 1u)
      gkr_pairwise_round0_accumulate<E>(inputs, outputs, bc, gid, total0, total1);
    else
      gkr_lookup_round0_accumulate<E>(inputs, outputs, bc, gid, total0, total1);
  }

  const E eq = gkr_compute_eq_inline<E>(batch.eq_low, batch.eq_sizes, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

// `src` names the poly being folded -- the original GKR ext storage poly at step
// 1, the previous round's arena from step 2 on -- and `cache` the arena slot the
// fold is written to. Both resolve through the same pointer table, so one kernel
// serves every step past 0; only the host encoder distinguishes the two cases.
//
// The source and cache spans never overlap (the host allocates a fresh
// destination arena per step), and each thread reads exactly the source cells it
// alone folds into the cells it alone writes, so the pairing needs no size
// bookkeeping: `gkr_dim_reducing_ancestor_index` maps a cache index to its
// source pair.
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

template <typename E>
DEVICE_FORCEINLINE void gkr_dim_reducing_continuation_batched_compact_inner(const gkr_dim_reducing_batch<E> &batch, const unsigned acc_size,
                                                                            const unsigned step) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const E *folding_challenge = &::ab_gkr_dim_reducing_layer_claim_point[step - 1];

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  // Fully unrolled: `slot` is a compile-time constant in each copy, so the
  // pairwise/lookup selection folds away and no dispatch survives codegen.
#pragma unroll
  for (unsigned slot = 0; slot < GKR_DIM_REDUCING_SLOTS; ++slot) {
    if ((batch.enabled_mask & (1u << slot)) == 0)
      continue;
    const gkr_dim_reducing_slot &desc = batch.slots[slot];

    E bc[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
    gkr_load_slot_batch_challenges(desc, bc);

    gkr_ext_continuing_source<E> inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
#pragma unroll
    for (unsigned k = 0; k < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++k)
      inputs[k] = gkr_resolve_dim_reducing_continuation_source<E>(batch.tables, desc.io[k]);

    if ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK >> slot) & 1u)
      gkr_pairwise_continuation_accumulate<E>(inputs, folding_challenge, bc, gid, total0, total1);
    else
      gkr_lookup_continuation_accumulate<E>(inputs, folding_challenge, bc, gid, total0, total1);
  }

  const E eq = gkr_compute_eq_inline<E>(batch.eq_low, batch.eq_sizes, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

} // namespace airbender::gkr
