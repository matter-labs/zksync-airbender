#include "context.cuh"

namespace airbender::ntt {

// Device probes used by the Rust CPU-parity tests.
extern "C" __global__ void ab_pr_ntt_test_root_powers_kernel(const proth120_twiddle_descriptor d, const u64 *exponents, pr *powers, u32 *reversed) {
  const u32 i = threadIdx.x;
  const u64 e = exponents[i];
  powers[3 * i] = pr_root_power(d, e);
  powers[3 * i + 1] = pr_root_power_inv(d, e);
  powers[3 * i + 2] = get_forward_pr_twiddle(d, static_cast<u32>(e));
  reversed[i] = bitreverse_low_bits(static_cast<u32>(e), 32);
}

extern "C" __global__ void ab_pr_ntt_test_inverse_leaf_kernel(const proth120_twiddle_descriptor d, const u32 exponent, pr *values) {
  pr leaf[16];
#pragma unroll
  for (u32 i = 0; i < 16; i++)
    leaf[i] = values[i];
  ab_pr_convert_leaf<4>(d, leaf, pr_root_power_inv(d, exponent));
#pragma unroll
  for (u32 i = 0; i < 16; i++)
    values[i] = leaf[i];
}

} // namespace airbender::ntt
