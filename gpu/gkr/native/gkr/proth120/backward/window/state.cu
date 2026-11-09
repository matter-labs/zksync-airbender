#include "../../../backward/window/common.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

static_assert(BWD_FOLD_WEIGHT_SLOTS == 11 && BWD_FOLD_WEIGHT_BASE_D1 == 0 && BWD_FOLD_WEIGHT_BASE_D2 == 1 && BWD_FOLD_WEIGHT_BASE_D3 == 4);
static_assert(2 * sizeof(void *) + sizeof(u32) <= 32764);

EXTERN __global__ void ab_pr_gkr_bwd_build_fold_weights_kernel(pr *const fold_weights, const pr *const claim_point, const u32 round) {
  const u32 slot = threadIdx.x;
  if (blockIdx.x != 0 || slot >= BWD_FOLD_WEIGHT_SLOTS)
    return;
  const u32 delta = slot < BWD_FOLD_WEIGHT_BASE_D2 ? 1 : slot < BWD_FOLD_WEIGHT_BASE_D3 ? 2 : 3;
  const u32 base = delta == 1 ? BWD_FOLD_WEIGHT_BASE_D1 : delta == 2 ? BWD_FOLD_WEIGHT_BASE_D2 : BWD_FOLD_WEIGHT_BASE_D3;
  const u32 q = slot - base + 1;
  if (delta > round) {
    fold_weights[slot] = pr::ZERO();
    return;
  }
  pr weight = pr::ONE();
  for (u32 j = 0; j < delta; ++j) {
    const pr challenge = claim_point[round - delta + j];
    weight = pr::mul(weight, ((q >> j) & 1) != 0 ? challenge : pr::sub(pr::ONE(), challenge));
  }
  fold_weights[slot] = weight;
}

} // namespace airbender::gkr::proth120::backward
