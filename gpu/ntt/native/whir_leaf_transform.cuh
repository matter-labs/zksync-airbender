#pragma once

#include <common.cuh>
#include <cstddef>
#include <primitives/field.cuh>
#include <primitives/memory.cuh>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ntt {

struct whir_leaf_transform_params {
  const bf *inverse_fine_values;
  unsigned inverse_fine_mask;
  unsigned inverse_fine_log_count;
  const bf *inverse_coarse_values;
  unsigned inverse_coarse_mask;
  bf two_inv_power;
  unsigned omega_log_order;
};

// Twin of `WhirLeafTransformParams` in `src/ntt_twiddles.rs`.
static_assert(sizeof(whir_leaf_transform_params) == 40);
static_assert(alignof(whir_leaf_transform_params) == 8);
static_assert(offsetof(whir_leaf_transform_params, inverse_fine_values) == 0);
static_assert(offsetof(whir_leaf_transform_params, inverse_fine_mask) == 8);
static_assert(offsetof(whir_leaf_transform_params, inverse_fine_log_count) == 12);
static_assert(offsetof(whir_leaf_transform_params, inverse_coarse_values) == 16);
static_assert(offsetof(whir_leaf_transform_params, inverse_coarse_mask) == 24);
static_assert(offsetof(whir_leaf_transform_params, two_inv_power) == 28);
static_assert(offsetof(whir_leaf_transform_params, omega_log_order) == 32);

struct params_inverse_power_source {
  whir_leaf_transform_params params;

  DEVICE_FORCEINLINE bf get(const unsigned idx) const {
    const unsigned coarse_idx = (idx >> params.inverse_fine_log_count) & params.inverse_coarse_mask;
    const unsigned fine_idx = idx & params.inverse_fine_mask;
    bf value = load_ca(params.inverse_coarse_values + coarse_idx);
    if (fine_idx != 0) {
      value = bf::mul(value, load_ca(params.inverse_fine_values + fine_idx));
    }
    return value;
  }
};

// "Improving running time via alternate domain evaluation," page 15:
// https://eprint.iacr.org/2024/1586.pdf
template <class Source, class Destination, class InversePowerSource>
DEVICE_FORCEINLINE void transform_whir_leaf_from_ntt(const Source &src, Destination &dst, const unsigned log_trace_len, const unsigned log_lde_factor,
                                                     const unsigned log_values_per_leaf, const unsigned coset, const unsigned base_lane_in_coset,
                                                     e4 *values_smem, bf *x_invs_smem, const bf two_inv_power, const InversePowerSource &inverse_power_source) {
  const unsigned leaves_per_coset = 1 << (log_trace_len - log_values_per_leaf);
  const unsigned initial_slot_in_leaf = threadIdx.y;
  const unsigned initial_exchg_stride = leaves_per_coset << (log_values_per_leaf - 1);
  // Bit-reversed jumps make the NTT-like transform's butterfly pairing direct.
  const unsigned src_row_a = leaves_per_coset * initial_slot_in_leaf;
  const unsigned src_row_b = src_row_a + initial_exchg_stride;

  const e4 a = src.get_at_row(src_row_a);
  const e4 b = src.get_at_row(src_row_b);

  const unsigned coset_offset = coset << (inverse_power_source.params.omega_log_order - log_trace_len - log_lde_factor);
  bf x_inv = inverse_power_source.get(((base_lane_in_coset + src_row_a) << (inverse_power_source.params.omega_log_order - log_trace_len)) + coset_offset);

  if (log_values_per_leaf == 1) {
    const e4 c = e4::mul(two_inv_power, e4::add(a, b));
    const e4 d = e4::mul(bf::mul(x_inv, two_inv_power), e4::sub(a, b));
    dst.set_at_slot(0, c);
    dst.set_at_slot(1, d);
    return;
  }

  e4 *smem_thread = values_smem + threadIdx.x;
  bf *x_invs = x_invs_smem + threadIdx.x;

  smem_thread[blockDim.x * initial_slot_in_leaf] = e4::mul(two_inv_power, e4::add(a, b));
  smem_thread[blockDim.x * (initial_slot_in_leaf + blockDim.y)] = e4::mul(bf::mul(x_inv, two_inv_power), e4::sub(a, b));

  for (unsigned stage = 1; stage < log_values_per_leaf - 1; stage++) {
    const unsigned log_exchg_stride = log_values_per_leaf - 1 - stage;
    const unsigned exchg_stride = 1 << log_exchg_stride;
    const unsigned exchg_region = threadIdx.y >> log_exchg_stride;
    const unsigned exchg_lane = threadIdx.y & (exchg_stride - 1);
    const unsigned mid_stage_slot_in_leaf = 2 * exchg_stride * exchg_region + exchg_lane;

    if (exchg_region == 0) {
      x_inv = bf::sqr(x_inv);
      x_invs[blockDim.x * exchg_lane] = x_inv;
    }
    __syncthreads();
    const e4 stage_a = smem_thread[blockDim.x * mid_stage_slot_in_leaf];
    const e4 stage_b = smem_thread[blockDim.x * (mid_stage_slot_in_leaf + exchg_stride)];
    if (exchg_region != 0)
      x_inv = x_invs[blockDim.x * exchg_lane];

    const e4 c = e4::add(stage_a, stage_b);
    const e4 d = e4::mul(x_inv, e4::sub(stage_a, stage_b));
    smem_thread[blockDim.x * mid_stage_slot_in_leaf] = c;
    smem_thread[blockDim.x * (mid_stage_slot_in_leaf + exchg_stride)] = d;

    x_invs += blockDim.x * (blockDim.y >> stage);
  }

  const unsigned final_slot_in_leaf = 2 * threadIdx.y;
  if (threadIdx.y == 0) {
    x_inv = bf::sqr(x_inv);
    x_invs[0] = x_inv;
  }
  __syncthreads();
  if (threadIdx.y != 0)
    x_inv = x_invs[0];
  const e4 final_a = smem_thread[blockDim.x * final_slot_in_leaf];
  const e4 final_b = smem_thread[blockDim.x * (final_slot_in_leaf + 1)];

  if constexpr (Destination::ALIASES_VALUES_SMEM) {
    // All final reads must finish before aliased stores reuse values_smem.
    __syncthreads();
  }
  dst.set_at_slot(final_slot_in_leaf, e4::add(final_a, final_b));
  dst.set_at_slot(final_slot_in_leaf + 1, e4::mul(x_inv, e4::sub(final_a, final_b)));
}

} // namespace airbender::ntt
