#pragma once

#include "eq_inline.cuh"
#include "kernel_helpers.cuh"

namespace airbender::prover::gkr {

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache_memory_tuple(const gkr_forward_cache_descriptor<E> &descriptor, const unsigned gid) {
  E value = descriptor.constant_term;
  switch (descriptor.address_space_kind) {
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT:
    value = E::add(value, descriptor.address_space_constant);
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_IS:
    value = E::add(value, load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT:
    value = E::add(value, E::sub(E::ONE(), load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid)));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY:
    break;
  }

#pragma unroll
  for (unsigned term = 0; term < GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS; ++term) {
    if (descriptor.linear_inputs[term] == nullptr)
      continue;
    const bf input = load<bf, ld_modifier::cs>(descriptor.linear_inputs[term], gid);
    value = E::fma(descriptor.linear_challenges[term], input, value);
  }

  store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
}

template <typename E> DEVICE_FORCEINLINE E gkr_forward_lookup_setup_value(const E *generic_lookup, const u32 generic_lookup_len, const unsigned gid) {
  return gid < generic_lookup_len ? load<E, ld_modifier::cs>(generic_lookup, gid) : E::ZERO();
}

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache(const gkr_forward_cache_batch<E> &batch, const unsigned trace_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= trace_len)
    return;

#pragma unroll
  for (unsigned relation_idx = 0; relation_idx < GKR_FORWARD_CACHE_MAX_RELATIONS; ++relation_idx) {
    if (relation_idx >= batch.count)
      return;

    const auto &descriptor = batch.descriptors[relation_idx];
    switch (descriptor.kind) {
    case GKR_FORWARD_CACHE_SINGLE_COLUMN_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      const bf value = descriptor.setup_source_kind == GKR_BASE_SOURCE_REAL ? load<bf, ld_modifier::cs>(descriptor.setup_values, mapping)
                                                                            : gkr_virtual_base_value(descriptor.setup_source_kind, mapping);
      store<bf, st_modifier::cs>(descriptor.base_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      E value = load<E, ld_modifier::cs>(descriptor.generic_lookup, mapping);
      if (descriptor.decoder_mask != nullptr) {
        const bf enabled = load<bf, ld_modifier::cs>(descriptor.decoder_mask, gid);
        if (enabled.limb == 0) {
          value = load<E, ld_modifier::cs>(descriptor.decoder_fill_value, 0);
        }
      }
      store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP_SETUP: {
      const E value = gid < descriptor.generic_lookup_len ? load<E, ld_modifier::cs>(descriptor.generic_lookup, gid) : E::ZERO();
      store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_MEMORY_TUPLE:
      gkr_forward_cache_memory_tuple(descriptor, gid);
      break;
    case GKR_FORWARD_CACHE_EMPTY:
      return;
    }
  }
}

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

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_pairwise_continuation_values(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E batch_challenge,
                                                         const unsigned gid, E &c0, E &c1) {
  const E current_folding_challenge = folding_challenge[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E even_f0;
  E even_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, even_index, even_f0, even_f1_or_delta);

  E odd_f0;
  E odd_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, odd_index, odd_f0, odd_f1_or_delta);

  c0 = E::mul(batch_challenge, E::mul(even_f0, odd_f0));
  c1 = E::mul(batch_challenge, E::mul(even_f1_or_delta, odd_f1_or_delta));
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_lookup_continuation_values(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E batch_challenge_0,
                                                       const E batch_challenge_1, const unsigned gid, E &out0, E &out1) {
  const E current_folding_challenge = folding_challenge[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E a0;
  E a1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, even_index, a0, a1);
  E b0;
  E b1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], current_folding_challenge, even_index, b0, b1);
  E c0;
  E c1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, odd_index, c0, c1);
  E d0;
  E d1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], current_folding_challenge, odd_index, d0, d1);

  const E num0 = E::fma(a0, d0, E::mul(c0, b0));
  const E den0 = E::mul(b0, d0);
  const E num1 = E::fma(a1, d1, E::mul(c1, b1));
  const E den1 = E::mul(b1, d1);

  out0 = E::fma(batch_challenge_0, num0, E::mul(batch_challenge_1, den0));
  out1 = E::fma(batch_challenge_0, num1, E::mul(batch_challenge_1, den1));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                            E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E c0;
  E c1;
  gkr_pairwise_round0_values(inputs, outputs, batch_challenges[0], gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                          E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E c0;
  E c1;
  gkr_lookup_round0_values(inputs, outputs, batch_challenges[0], batch_challenges[1], gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_pairwise_continuation(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                  E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E c0;
  E c1;
  gkr_pairwise_continuation_values<E, EXPLICIT_FORM>(inputs, folding_challenge, batch_challenges[0], gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_lookup_continuation(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E out0;
  E out1;
  gkr_lookup_continuation_values<E, EXPLICIT_FORM>(inputs, folding_challenge, batch_challenges[0], batch_challenges[1], gid, out0, out1);
  gkr_accumulate_contribution(contributions, gid, acc_size, out0, out1);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_product(const E a, const E b, E &value) { value = E::mul(a, b); }

template <typename E, typename Mask, typename Value> DEVICE_FORCEINLINE void gkr_eval_mask_identity(const Mask mask, const Value value, E &result) {
  result = E::sub(value, E::ONE());
  result = E::mul(result, mask);
  result = E::add(result, E::ONE());
}

template <typename E, typename Mask, typename Value> DEVICE_FORCEINLINE void gkr_eval_mask_identity_quadratic(const Mask mask, const Value value, E &result) {
  result = E::mul(value, mask);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_pair(const E a, const E b, const E c, const E d, E &num, E &den) {
  num = E::fma(a, d, E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E, typename B, typename D> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair(const B b, const D d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::add(shifted_b, shifted_d);
  den = E::mul(shifted_b, shifted_d);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_v2(const bf b, const bf d, const E gamma, const E gamma_sq, const E two_gamma, E &num, E &den) {
  const bf bd_sum = bf::add(b, d);
  num = E::add(two_gamma, bd_sum);
  const bf bd_prod = bf::mul(b, d);
  const E gamma_sq_plus_bd = E::add(gamma_sq, bd_prod);
  den = E::fma(gamma, bd_sum, gamma_sq_plus_bd);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_ext_pair(const E b, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::add(shifted_b, shifted_d);
  den = E::mul(shifted_b, shifted_d);
}

template <typename E, typename B, typename D> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_quadratic(const B b, const D d, E &num, E &den) {
  num = E::ZERO();
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_quadratic(const bf b, const bf d, E &num, E &den) {
  num = E::ZERO();
  den = E::from_scalar(bf::mul(b, d));
}

template <typename E, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity(const B b, const C c, const D d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(shifted_d, E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_v2(const bf b, const bf c, const bf d, const E gamma, const E gamma_sq, E &num, E &den) {
  const bf cb = bf::mul(c, b);
  const bf one_minus_c = bf::sub(bf::ONE(), c);
  const bf d_minus_cb = bf::sub(d, cb);
  num = E::fma(gamma, one_minus_c, d_minus_cb);

  const bf bd_sum = bf::add(b, d);
  const bf bd_prod = bf::mul(b, d);
  const E gamma_sq_plus_bd = E::add(gamma_sq, bd_prod);
  den = E::fma(gamma, bd_sum, gamma_sq_plus_bd);
}

template <typename E, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_quadratic(const B b, const C c, const D d, E &num, E &den) {
  num = E::neg(E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_quadratic(const bf b, const bf c, const bf d, E &num, E &den) {
  num = E::neg(E::from_scalar(bf::mul(c, b)));
  den = E::from_scalar(bf::mul(b, d));
}

template <typename E, typename D, typename A, typename B>
DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced(const D d, const A a, const B b, const E gamma, E &num, E &den) {
  const E shifted_d = E::add(d, gamma);
  num = E::fma(a, shifted_d, b);
  den = E::mul(b, shifted_d);
}

template <typename E, typename D, typename A, typename B>
DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced_quadratic(const D d, const A a, const B b, E &num, E &den) {
  num = E::mul(d, a);
  den = E::mul(d, b);
}

template <typename E, typename A, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup(const A a, const B b, const C c, const D d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::fms(a, shifted_d, E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E, typename A, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup_quadratic(const A a, const B b, const C c, const D d, E &num, E &den) {
  num = E::fms(a, d, E::mul(c, b));
  den = E::mul(b, d);
}

// Pairwise-product tower: each block consumes B = blockDim.x contiguous input rows (or fewer, in
// the single-block tail) and fuses up to log2(B) halving rounds in shared memory. Every round's
// output is also written to DRAM for backward consumption.
template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_forward_tower_pairwise(const gkr_dim_reducing_forward_tower_pairwise_batch<E> &batch) {
  extern __shared__ E smem_pairwise[];

  const unsigned tid = threadIdx.x;
  const unsigned bid = blockIdx.x;
  const unsigned base = bid * blockDim.x;

  // Round-0 load from DRAM to shmem. Threads outside the valid tail range idle.
  if (base + tid < batch.input_len)
    smem_pairwise[tid] = load<E, ld_modifier::cs>(batch.input, base + tid);
  __syncthreads();

  // For body launches, cur_len == blockDim.x == B. For the single-block tail where
  // input_len < B, only the first input_len threads carried real data.
  unsigned cur_len = blockDim.x < batch.input_len ? blockDim.x : batch.input_len;
  for (unsigned r = 0; r < batch.round_count; ++r) {
    cur_len >>= 1;
    E out;
    const bool active = tid < cur_len;
    if (active) {
      const E lhs = smem_pairwise[2 * tid];
      const E rhs = smem_pairwise[2 * tid + 1];
      gkr_eval_product(lhs, rhs, out);
      // Coalesced DRAM write — block b's slice of this level is [b*cur_len, (b+1)*cur_len).
      store<E, st_modifier::cs>(batch.round_outputs[r], out, bid * cur_len + tid);
    }
    __syncthreads(); // Read phase complete; safe to overwrite shmem.
    if (active)
      smem_pairwise[tid] = out;
    __syncthreads(); // Next round may read a wider slice; ensure all writes visible.
  }
}

// Lookup-pair tower: same shape as pairwise but with num/den shmem buffers side by side.
template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_forward_tower_lookup(const gkr_dim_reducing_forward_tower_lookup_batch<E> &batch) {
  extern __shared__ E smem_lookup[];
  E *smem_num = smem_lookup;
  E *smem_den = smem_lookup + blockDim.x;

  const unsigned tid = threadIdx.x;
  const unsigned bid = blockIdx.x;
  const unsigned base = bid * blockDim.x;

  if (base + tid < batch.input_len) {
    smem_num[tid] = load<E, ld_modifier::cs>(batch.input_num, base + tid);
    smem_den[tid] = load<E, ld_modifier::cs>(batch.input_den, base + tid);
  }
  __syncthreads();

  unsigned cur_len = blockDim.x < batch.input_len ? blockDim.x : batch.input_len;
  for (unsigned r = 0; r < batch.round_count; ++r) {
    cur_len >>= 1;
    E out_num;
    E out_den;
    const bool active = tid < cur_len;
    if (active) {
      const E a = smem_num[2 * tid];
      const E b = smem_den[2 * tid];
      const E c = smem_num[2 * tid + 1];
      const E d = smem_den[2 * tid + 1];
      gkr_eval_lookup_pair(a, b, c, d, out_num, out_den);
      store<E, st_modifier::cs>(batch.round_outputs_num[r], out_num, bid * cur_len + tid);
      store<E, st_modifier::cs>(batch.round_outputs_den[r], out_den, bid * cur_len + tid);
    }
    __syncthreads();
    if (active) {
      smem_num[tid] = out_num;
      smem_den[tid] = out_den;
    }
    __syncthreads();
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_forward_setup_generic_lookup(const gkr_forward_setup_generic_lookup_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;

  // Thread 0 also folds the decoder fill value (alpha^(column_count-1) * decoder_table_id)
  // into a 1-element device slot so downstream forward-cache kernels can read it
  // directly, avoiding a host callback + H2D copy.
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

// Compact-path round-0 decoder. Walks `inline_payload` u16 source descriptors and resolves each to
// a poly start via the per-launch `bases` / `log2_stride` tables. Round 0's `next_layer_size` is
// uniformly `acc_size` for every input/output (all polys at one layer share the same trace_len),
// so no per-source size metadata is needed. `log2_stride` is the **element-count** stride
// (matches the Rust storage layout's per-poly element stride; see
// `GpuGKRStorageLayout::log2_stride`). We re-interpret the byte base as `const E *` and advance by
// element index, so the unit matches the Rust side regardless of `sizeof(E)`.
//
// Round 0 inputs sit one layer above the output layer (input size = 2 *
// output_size = 2 * trace_len_after_reduction = 4 * acc_size), so the input
// poly's `next_layer_size = input_size / 2 = 2 * acc_size`. The kernel's
// `gkr_get_initial_delta` is only called on inputs; outputs are read via
// `gkr_get_initial_value` (which ignores `next_layer_size`), so this
// uniform setting is correct for both input and output sources at round 0.
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

template <typename E, bool EXPLICIT_FORM>
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
      gkr_pairwise_continuation_values<E, EXPLICIT_FORM>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[0],
                                                         ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset], gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_continuation_values<E, EXPLICIT_FORM>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[0],
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

// Continuation (sumcheck step >= 2) source resolver. The u16 encodes the
// folding-buffer slot directly (the host has set up bases[ptr_idx] to the
// consolidated folding backing's start). At step N >= 2:
//   per_poly_size = (1 << (N+1)) * acc_size   (uniform for all polys)
//   previous_offset_in_E = ((1 << (N+1)) - 8) * acc_size   // step 2 → 0
//   this_offset_in_E     = ((1 << (N+1)) - 4) * acc_size   // step 2 → 4*acc
//   this_layer_size = 2 * acc_size, next_layer_size = acc_size
template <typename E>
DEVICE_FORCEINLINE gkr_ext_continuing_source<E> gkr_resolve_dim_reducing_continuation_source(const gkr_dim_reducing_tables &tables,
                                                                                             const gkr_source_record record, const unsigned acc_size,
                                                                                             const unsigned step) {
  bool first_access;
  u32 ptr_idx;
  u32 poly_idx;
  unpack_dim_reducing_source_u16(record.src, first_access, ptr_idx, poly_idx);
  E *buffer_base = reinterpret_cast<E *>(const_cast<u8 *>(tables.bases[ptr_idx]));
  const u32 buffer_log2_stride = tables.log2_stride[ptr_idx];
  E *buffer_start = buffer_base + (static_cast<size_t>(poly_idx) << buffer_log2_stride);
  // Mirrors `pointer_for_sumcheck_continuation` cumulative offsets.
  // At step k >= 2 (in acc_size units, where size_after_one_fold = 2^(k+1) * acc_size):
  //   previous_offset = sum_{i=0..k-3} size_after_one_fold/2^i = (2^(k+2) - 16) * acc_size
  //   this_offset     = previous_offset + size_after_one_fold/2^(k-2) = (2^(k+2) - 8) * acc_size
  const unsigned shifted = 1u << (step + 2);
  const E *previous = buffer_start + static_cast<size_t>(shifted - 16u) * acc_size;
  E *this_layer = buffer_start + static_cast<size_t>(shifted - 8u) * acc_size;
  // At step k >= 2, `this_layer_size = 4 * acc_size` (the f0/f1 stride within
  // the previous-layer span = trace_len_after_reduction >> (k-1) = 4 * acc_size_at_step_k);
  // `next_layer_size = this_layer_size / 2 = 2 * acc_size`.
  return gkr_ext_continuing_source<E>{previous, this_layer, 4u * acc_size, 2u * acc_size, first_access};
}

template <typename E, bool EXPLICIT_FORM>
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
      inputs[k] = gkr_resolve_dim_reducing_continuation_source<E>(batch.tables, batch.inline_payload[record.inputs.offset + k], acc_size, step);
    }
    E c0;
    E c1;
    switch (record.kind) {
    case GKR_DIM_REDUCING_PAIRWISE:
      gkr_pairwise_continuation_values<E, EXPLICIT_FORM>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[step - 1],
                                                         ::ab_gkr_dim_reducing_batch_challenge_table[record.batch_challenge_offset], gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_continuation_values<E, EXPLICIT_FORM>(inputs, &::ab_gkr_dim_reducing_layer_claim_point[step - 1],
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

} // namespace airbender::prover::gkr
