#include "context.cuh"

namespace airbender::ntt {

DEVICE_FORCEINLINE unsigned get_forward_stage_twiddle_power(const unsigned group, const unsigned log_n) {
  const unsigned exponent = bitrev(group, log_n - 1) << (OMEGA_LOG_ORDER - log_n);
  return exponent;
}

DEVICE_FORCEINLINE unsigned get_inverse_stage_twiddle_power(const unsigned group, const unsigned log_n) {
  const unsigned exponent = bitrev(group, log_n - 1) << (OMEGA_LOG_ORDER - log_n);
  return exponent;
}

EXTERN __global__ void ab_copy_scale_bitreversed_coeffs_kernel(const bf *src, bf *dst, const bf coset_offset, const bool apply_scale, const unsigned log_n) {
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
    const unsigned twiddle_power = get_inverse_stage_twiddle_power(group, log_n);
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

EXTERN __launch_bounds__(32, 8) __global__ void ab_transpose_monomials_naive_kernel(bf *values, const unsigned log_n) {
  constexpr unsigned TILE_ROWS = 32;
  constexpr unsigned TILE_COLS = 32;
  constexpr unsigned TILE_SIZE = TILE_ROWS * TILE_COLS;

  const unsigned count = 1u << log_n;
  const unsigned tile_offset = blockIdx.x * TILE_SIZE;
  if (tile_offset >= count)
    return;

  const unsigned row = threadIdx.x;
  if (row >= TILE_ROWS)
    return;

  bf *tile = values + tile_offset;
#pragma unroll
  for (unsigned col = 0; col < row; col++) {
    const unsigned a_idx = row * TILE_COLS + col;
    const unsigned b_idx = col * TILE_COLS + row;
    const bf a = load_cg(tile + a_idx);
    const bf b = load_cg(tile + b_idx);
    store_cg(tile + a_idx, b);
    store_cg(tile + b_idx, a);
  }
}

} // namespace airbender::ntt
