#include "primitives/proth120.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr::proth120::support {
using pr = ::airbender::primitives::field::proth120;
static_assert(sizeof(void *) == 8 && sizeof(u32) == 4 && sizeof(pr) == 16);
static_assert(3 * sizeof(void *) + sizeof(u32) <= 32764);

EXTERN __global__ void ab_pr_gkr_initial_inner_product_kernel(const pr *polys_base, const pr *eq_values, const unsigned poly_len, pr *claims_out) {
  constexpr unsigned BLOCK_SIZE = 256;
  const pr *poly = polys_base + blockIdx.x * poly_len;
  pr sum = pr::ZERO();
  for (unsigned i = threadIdx.x; i < poly_len; i += BLOCK_SIZE) {
    sum = pr::add(sum, pr::mul(poly[i], eq_values[i]));
  }
  __shared__ pr smem[BLOCK_SIZE];
  smem[threadIdx.x] = sum;
  __syncthreads();
#pragma unroll
  for (unsigned step = BLOCK_SIZE / 2; step > 0; step >>= 1) {
    if (threadIdx.x < step) {
      smem[threadIdx.x] = pr::add(smem[threadIdx.x], smem[threadIdx.x + step]);
    }
    __syncthreads();
  }
  if (threadIdx.x == 0) {
    claims_out[blockIdx.x] = smem[0];
  }
}

} // namespace airbender::gkr::proth120::support
