#include "initial_inner_product.cuh"
#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr {

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
  __shared__ e4 smem[BLOCK_SIZE];
  ::airbender::gkr::initial_inner_product<e4, BLOCK_SIZE>(polys_base, eq_values, poly_len, claims_out, smem);
}
} // namespace airbender::gkr
