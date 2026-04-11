#include "common.cuh"
#include "generated/add_sub_lui_auipc_mop_main_backward_e4.cuh"

namespace airbender::prover::gkr {

EXTERN __global__ void
ab_gkr_generated_add_sub_lui_auipc_mop_main_round2_batched_compact_e4_kernel(
    const unsigned layer_idx, const __grid_constant__ gkr_main_round2_batch_static<e4> batch_static,
    const gkr_main_round2_batch_runtime<e4> batch_runtime,
    const gkr_generated_add_sub_lui_auipc_mop_main_challenges<e4> *challenges, const unsigned acc_size) {
  gkr_generated_add_sub_lui_auipc_mop_main_round2_compact<e4>(layer_idx, batch_static, batch_runtime, challenges[0], acc_size);
}

} // namespace airbender::prover::gkr
