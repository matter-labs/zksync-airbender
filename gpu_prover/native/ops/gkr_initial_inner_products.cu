#include "../primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::ops {

// One block per inner product. The polys are laid out contiguously starting at
// `polys_base` with stride `poly_len`: block `b` consumes
// `polys_base[b*poly_len .. (b+1)*poly_len]`. The slot-order / iteration-order
// permutation is provably identity (see proof.rs construction note) so no
// per-poly pointer table is needed. Computes `sum_i poly[i] * eq_values[i]`
// via a striped per-thread accumulation followed by a block-wide tree
// reduction in shared memory, then writes the resulting E4 to
// `claims_out[blockIdx.x]`.
EXTERN __global__ void ab_initial_inner_product_e4_kernel(const e4 *polys_base, const e4 *eq_values, const unsigned poly_len, e4 *claims_out) {
  constexpr unsigned BLOCK_SIZE = 256;
  const e4 *poly = polys_base + blockIdx.x * poly_len;
  e4 sum = e4::ZERO();
  for (unsigned i = threadIdx.x; i < poly_len; i += BLOCK_SIZE) {
    sum = e4::add(sum, e4::mul(poly[i], eq_values[i]));
  }
  __shared__ e4 smem[BLOCK_SIZE];
  smem[threadIdx.x] = sum;
  __syncthreads();
#pragma unroll
  for (unsigned step = BLOCK_SIZE / 2; step > 0; step >>= 1) {
    if (threadIdx.x < step) {
      smem[threadIdx.x] = e4::add(smem[threadIdx.x], smem[threadIdx.x + step]);
    }
    __syncthreads();
  }
  if (threadIdx.x == 0) {
    claims_out[blockIdx.x] = smem[0];
  }
}

} // namespace airbender::ops
