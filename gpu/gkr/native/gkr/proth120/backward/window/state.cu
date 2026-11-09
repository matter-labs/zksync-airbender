#include "../../../backward/window/common.cuh"
#include "../../../backward/window/fold_weights_shared.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

static_assert(BWD_FOLD_WEIGHT_SLOTS == 11 && BWD_FOLD_WEIGHT_BASE_D1 == 0 && BWD_FOLD_WEIGHT_BASE_D2 == 1 && BWD_FOLD_WEIGHT_BASE_D3 == 4);
static_assert(2 * sizeof(void *) + sizeof(u32) <= 32764);

struct fold_weight_point_reader {
  const pr *point;
  DEVICE_FORCEINLINE pr operator()(u32 index) const { return point[index]; }
};
EXTERN __global__ void ab_pr_gkr_bwd_build_fold_weights_kernel(pr *const fold_weights, const pr *const claim_point, const u32 round) {
  ::airbender::gkr::build_fold_weights(fold_weights, fold_weight_point_reader{claim_point}, round);
}

} // namespace airbender::gkr::proth120::backward
