#include "lookup_helpers_pr.cuh"
namespace airbender::gkr::proth120::setup {
EXTERN __global__ void ab_pr_gkr_forward_setup_generic_lookup_batch_kernel(const __grid_constant__ forward_setup_lookup_batch_pr batch, const u32 rows) {
  forward_setup_lookup(batch, rows);
}
} // namespace airbender::gkr::proth120::setup
