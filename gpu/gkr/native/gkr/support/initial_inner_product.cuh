#pragma once
#include "primitives/field.cuh"

namespace airbender::gkr {

template <typename F, unsigned BLOCK_SIZE>
DEVICE_FORCEINLINE void initial_inner_product(const F *polys_base, const F *eq_values, unsigned poly_len, F *claims_out, F *smem) {
  const F *poly = polys_base + blockIdx.x * poly_len;
  F sum = F::ZERO();
  for (unsigned i = threadIdx.x; i < poly_len; i += BLOCK_SIZE) {
    sum = F::add(sum, F::mul(poly[i], eq_values[i]));
  }
  smem[threadIdx.x] = sum;
  __syncthreads();
#pragma unroll
  for (unsigned step = BLOCK_SIZE / 2; step > 0; step >>= 1) {
    if (threadIdx.x < step) {
      smem[threadIdx.x] = F::add(smem[threadIdx.x], smem[threadIdx.x + step]);
    }
    __syncthreads();
  }
  if (threadIdx.x == 0) {
    claims_out[blockIdx.x] = smem[0];
  }
}

} // namespace airbender::gkr
