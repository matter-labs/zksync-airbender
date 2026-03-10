#include "context.cuh"

namespace airbender::ntt {

DEVICE_FORCEINLINE unsigned get_forward_stage_twiddle_power(const unsigned group, const unsigned log_n) {
  const unsigned exponent = bitrev(group, log_n - 1) << (OMEGA_LOG_ORDER - log_n);
  return exponent;
}

EXTERN __global__ void ab_copy_scale_bitreversed_coeffs_kernel(const bf *src, bf *dst, const bf coset_offset, const bool apply_scale,
                                                               const unsigned log_n) {
  const unsigned count = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  bf value = load_cg(src + gid);
  if (apply_scale) {
    const unsigned coeff_index = bitrev(gid, log_n);
    value = bf::mul(value, bf::pow(coset_offset, coeff_index));
  }
  store_cg(dst + gid, value);
}

EXTERN __global__ void ab_bitreversed_coeffs_to_natural_ntt_stage_kernel(bf *values, const unsigned log_n, const unsigned stage) {
  const unsigned pair_count = 1u << (log_n - 1);
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= pair_count)
    return;

  const unsigned pairs_per_group = 1u << stage;
  const unsigned group = gid >> stage;
  const unsigned pair = gid & (pairs_per_group - 1);
  const unsigned left_idx = group * (pairs_per_group << 1) + pair;
  const unsigned right_idx = left_idx + pairs_per_group;

  const bf left = load_cg(values + left_idx);
  const bf right = load_cg(values + right_idx);

  bf twiddled_diff = bf::sub(left, right);
  if (stage + 1 < log_n) {
    const unsigned twiddle_power = get_forward_stage_twiddle_power(group, log_n);
    twiddled_diff = bf::mul(twiddled_diff, get_forward_twiddle_power(twiddle_power));
  }

  store_cg(values + left_idx, bf::add(left, right));
  store_cg(values + right_idx, twiddled_diff);
}

} // namespace airbender::ntt
