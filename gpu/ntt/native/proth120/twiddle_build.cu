#include "context.cuh"

namespace airbender::ntt {
namespace {
constexpr u32 FACTOR_BITS = 4;
constexpr u32 FACTOR_SIZE = 1u << FACTOR_BITS;
constexpr u32 FACTORS = 32 / FACTOR_BITS;
constexpr u32 LOW_LEN = 1u << 16;
constexpr u32 TABLE_LEN = LOW_LEN + (1u << 15);
// domain_generator_for_size<Proth120>(2^31), in canonical Montgomery form.
constexpr DEVICE_FORCEINLINE pr root31() { return {{0xeea02be9, 0xe4a2ec2e, 0x23510c85, 0x00c1d7c2}}; }
} // namespace

extern "C" __global__ void ab_pr_ntt_build_factors_kernel(pr *factors) {
  __shared__ pr base;
  if (threadIdx.x == 0) {
    pr value = root31();
    for (u32 i = 0; i < blockIdx.x * FACTOR_BITS; i++)
      value = pr::sqr(value);
    base = value;
  }
  __syncthreads();
  if (threadIdx.x < FACTOR_SIZE)
    store_wb(factors + blockIdx.x * FACTOR_SIZE + threadIdx.x, pr::pow(base, threadIdx.x));
}

extern "C" __global__ void ab_pr_ntt_build_tables_kernel(const pr *factors, pr *output) {
  const u32 idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= TABLE_LEN)
    return;
  const bool high = idx >= LOW_LEN;
  const u32 exponent = high ? idx - LOW_LEN : idx;
  const pr *source = factors + (high ? FACTORS / 2 * FACTOR_SIZE : 0);
  pr value = load_ca(source + (exponent & (FACTOR_SIZE - 1)));
#pragma unroll
  for (u32 digit = 1; digit < FACTORS / 2; digit++)
    value = pr::mul(value, load_ca(source + digit * FACTOR_SIZE + ((exponent >> (digit * FACTOR_BITS)) & (FACTOR_SIZE - 1))));
  store_wb(output + idx, value);
}
} // namespace airbender::ntt
