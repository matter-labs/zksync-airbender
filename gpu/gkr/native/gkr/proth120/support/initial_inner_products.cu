#include "../../support/initial_inner_product.cuh"
#include "primitives/proth120.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr::proth120::support {
using pr = ::airbender::primitives::field::proth120;
static_assert(sizeof(void *) == 8 && sizeof(u32) == 4 && sizeof(pr) == 16);
static_assert(3 * sizeof(void *) + sizeof(u32) <= 32764);

EXTERN __global__ void ab_pr_gkr_initial_inner_product_kernel(const pr *polys_base, const pr *eq_values, const unsigned poly_len, pr *claims_out) {
  constexpr unsigned BLOCK_SIZE = 256;
  __shared__ pr smem[BLOCK_SIZE];
  ::airbender::gkr::initial_inner_product<pr, BLOCK_SIZE>(polys_base, eq_values, poly_len, claims_out, smem);
}
} // namespace airbender::gkr::proth120::support
