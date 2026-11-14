#include "common.cuh"
#include "fold_weights_shared.cuh"

__device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];
__device__ __constant__ e4 ab_gkr_bwd_coeff_bank[airbender::gkr::BWD_COEFF_BANK_CAPACITY];
__device__ __constant__ e4 ab_gkr_bwd_fold_weights[airbender::gkr::BWD_FOLD_WEIGHT_SLOTS];

struct fold_weight_point_reader {
  DEVICE_FORCEINLINE e4 operator()(u32 index) const { return ::ab_gkr_main_layer_claim_point[index]; }
};
EXTERN __global__ void ab_gkr_bwd_build_fold_weights_kernel(e4 *const fold_weights, const u32 round) {
  ::airbender::gkr::build_fold_weights(fold_weights, fold_weight_point_reader{}, round);
}
