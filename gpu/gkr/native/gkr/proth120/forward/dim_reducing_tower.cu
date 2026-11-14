#include "../../support/lookup_helpers.cuh"
#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::forward {
using pr = ::airbender::primitives::field::proth120;
static_assert(sizeof(gkr_dim_reducing_forward_tower_batch<pr>) == 736);
EXTERN __global__ __launch_bounds__(GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK, 4) void ab_pr_gkr_dim_reducing_forward_tower_kernel(
    const __grid_constant__ gkr_dim_reducing_forward_tower_batch<pr> batch) {
  gkr_dim_reducing_forward_tower(batch);
}
} // namespace airbender::gkr::proth120::forward
