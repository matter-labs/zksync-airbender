#include "context.cuh"

namespace airbender::ntt {

EXTERN __global__ void ab_hypercube_evals_natural_to_bitreversed_coeffs_stage_kernel(bf *values, const unsigned log_n, const unsigned stage) {
  const unsigned pair_count = 1u << (log_n - 1);
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= pair_count)
    return;

  const unsigned stride = 1u << stage;
  const unsigned pair_offset = gid & (stride - 1);
  const unsigned block = gid >> stage;
  const unsigned left_idx = (block << (stage + 1)) + pair_offset;
  const unsigned right_idx = left_idx + stride;

  const bf left = load_cg(values + left_idx);
  bf right = load_cg(values + right_idx);
  right = bf::sub(right, left);
  store_cg(values + right_idx, right);
}

EXTERN __global__ void ab_hypercube_coeffs_natural_to_natural_evals_stage_kernel(bf *values, const unsigned log_n, const unsigned stage) {
  const unsigned pair_count = 1u << (log_n - 1);
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= pair_count)
    return;

  const unsigned stride = 1u << stage;
  const unsigned pair_offset = gid & (stride - 1);
  const unsigned block = gid >> stage;
  const unsigned left_idx = (block << (stage + 1)) + pair_offset;
  const unsigned right_idx = left_idx + stride;

  const bf left = load_cg(values + left_idx);
  bf right = load_cg(values + right_idx);
  right = bf::add(right, left);
  store_cg(values + right_idx, right);
}

} // namespace airbender::ntt
