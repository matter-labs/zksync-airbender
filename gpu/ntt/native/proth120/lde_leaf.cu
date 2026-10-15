#include "context.cuh"

namespace airbender::ntt {

template <u32 LOG_VALUES> DEVICE_FORCEINLINE void pr_convert_coset_leaves(pr *coset, const u32 log_n, const proth120_twiddle_descriptor &d, const pr *offset) {
  __shared__ pr offset_inv;
  if (threadIdx.x == 0)
    offset_inv = pr::inv(load_ca(offset));
  __syncthreads();
  constexpr u32 VALUES = 1u << LOG_VALUES;
  const u32 leaf_index = blockIdx.x * blockDim.x + threadIdx.x;
  const u32 leaves = 1u << (log_n - LOG_VALUES);
  if (leaf_index >= leaves)
    return;
  pr leaf[VALUES];
#pragma unroll
  for (u32 slot = 0; slot < VALUES; slot++)
    leaf[slot] = load_cg(coset + leaf_index + leaves * bitreverse_low_bits(slot, LOG_VALUES));
  const pr base_root_inv = pr::mul(offset_inv, pr_root_power_inv(d, leaf_index << (d.log_max_domain - log_n)));
  ab_pr_convert_leaf<LOG_VALUES>(d, leaf, base_root_inv);
#pragma unroll
  for (u32 slot = 0; slot < VALUES; slot++)
    store_cg(coset + leaf_index + leaves * bitreverse_low_bits(slot, LOG_VALUES), leaf[slot]);
}

template <u32 LOG_VALUES>
DEVICE_FORCEINLINE void pr_convert_gathered_leaves(pr *leaves, const u32 *indices, const u32 count, const u32 log_coset, const proth120_twiddle_descriptor &d,
                                                   const pr *offset) {
  __shared__ pr offset_inv;
  if (threadIdx.x == 0)
    offset_inv = pr::inv(load_ca(offset));
  __syncthreads();
  constexpr u32 VALUES = 1u << LOG_VALUES;
  const u32 query = blockIdx.x * blockDim.x + threadIdx.x;
  if (query >= count)
    return;
  const u32 leaf_index = load_cg(indices + query);
  pr *target = leaves + static_cast<size_t>(query) * VALUES;
  pr leaf[VALUES];
#pragma unroll
  for (u32 slot = 0; slot < VALUES; slot++)
    leaf[slot] = load_cg(target + slot);
  const pr base_root_inv = pr::mul(offset_inv, pr_root_power_inv(d, leaf_index << (d.log_max_domain - log_coset)));
  ab_pr_convert_leaf<LOG_VALUES>(d, leaf, base_root_inv);
#pragma unroll
  for (u32 slot = 0; slot < VALUES; slot++)
    store_cg(target + slot, leaf[slot]);
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_convert_coset_leaves_1_kernel(pr *coset, const u32 log_n, const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_coset_leaves<1>(coset, log_n, d, offset);
}
EXTERN __launch_bounds__(256) __global__ void ab_pr_convert_gathered_leaves_1_kernel(pr *leaves, const u32 *indices, const u32 count, const u32 log_coset,
                                                                                     const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_gathered_leaves<1>(leaves, indices, count, log_coset, d, offset);
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_convert_coset_leaves_2_kernel(pr *coset, const u32 log_n, const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_coset_leaves<2>(coset, log_n, d, offset);
}
EXTERN __launch_bounds__(256) __global__ void ab_pr_convert_gathered_leaves_2_kernel(pr *leaves, const u32 *indices, const u32 count, const u32 log_coset,
                                                                                     const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_gathered_leaves<2>(leaves, indices, count, log_coset, d, offset);
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_convert_coset_leaves_3_kernel(pr *coset, const u32 log_n, const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_coset_leaves<3>(coset, log_n, d, offset);
}
EXTERN __launch_bounds__(256) __global__ void ab_pr_convert_gathered_leaves_3_kernel(pr *leaves, const u32 *indices, const u32 count, const u32 log_coset,
                                                                                     const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_gathered_leaves<3>(leaves, indices, count, log_coset, d, offset);
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_convert_coset_leaves_4_kernel(pr *coset, const u32 log_n, const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_coset_leaves<4>(coset, log_n, d, offset);
}
EXTERN __launch_bounds__(256) __global__ void ab_pr_convert_gathered_leaves_4_kernel(pr *leaves, const u32 *indices, const u32 count, const u32 log_coset,
                                                                                     const proth120_twiddle_descriptor d, const pr *offset) {
  pr_convert_gathered_leaves<4>(leaves, indices, count, log_coset, d, offset);
}

} // namespace airbender::ntt
