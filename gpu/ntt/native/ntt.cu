#include "context.cuh"

namespace airbender::ntt {

DEVICE_FORCEINLINE unsigned get_forward_stage_twiddle_power(const unsigned group, const unsigned log_n) {
  const unsigned exponent = bitrev(group, log_n - 1) << (OMEGA_LOG_ORDER - log_n);
  return exponent;
}

EXTERN __global__ void ab_natural_evals_to_bitreversed_coeffs_ntt_stage_kernel(bf *values, const unsigned log_n, const unsigned stage) {
  const unsigned pair_count = 1u << (log_n - 1);
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= pair_count)
    return;

  const unsigned pairs_per_group = 1u << (log_n - stage - 1);
  const unsigned group = gid >> (log_n - stage - 1);
  const unsigned pair = gid & (pairs_per_group - 1);
  const unsigned left_idx = group * (pairs_per_group << 1) + pair;
  const unsigned right_idx = left_idx + pairs_per_group;

  bf left = load_cg(values + left_idx);
  bf right = load_cg(values + right_idx);
  if (stage != 0) {
    const unsigned twiddle_power = get_forward_stage_twiddle_power(group, log_n);
    right = bf::mul(right, get_inverse_twiddle_power(twiddle_power));
  }

  const bf left_out = bf::add(left, right);
  const bf right_out = bf::sub(left, right);
  if (stage + 1 == log_n) {
    const bf scale = load_ca(::ab_inv_sizes + log_n);
    store_cg(values + left_idx, bf::mul(left_out, scale));
    store_cg(values + right_idx, bf::mul(right_out, scale));
  } else {
    store_cg(values + left_idx, left_out);
    store_cg(values + right_idx, right_out);
  }
}

} // namespace airbender::ntt
