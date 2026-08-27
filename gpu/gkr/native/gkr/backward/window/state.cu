#include "common.cuh"

__device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];
__device__ __constant__ e4 ab_gkr_bwd_coeff_bank[airbender::gkr::BWD_COEFF_BANK_CAPACITY];
__device__ __constant__ e4 ab_gkr_bwd_fold_weights[airbender::gkr::BWD_FOLD_WEIGHT_SLOTS];

EXTERN __global__ void ab_gkr_bwd_build_fold_weights_kernel(e4 *const fold_weights, const u32 round) {
  using namespace airbender::gkr;
  const u32 slot = threadIdx.x;
  if (blockIdx.x != 0 || slot >= BWD_FOLD_WEIGHT_SLOTS)
    return;
  const u32 delta = slot < BWD_FOLD_WEIGHT_BASE_D2 ? 1 : slot < BWD_FOLD_WEIGHT_BASE_D3 ? 2 : 3;
  const u32 base = delta == 1 ? BWD_FOLD_WEIGHT_BASE_D1 : delta == 2 ? BWD_FOLD_WEIGHT_BASE_D2 : BWD_FOLD_WEIGHT_BASE_D3;
  const u32 q = slot - base + 1;
  if (delta > round) {
    fold_weights[slot] = e4::ZERO();
    return;
  }
  const e4 one = e4::from_scalar(bf::ONE());
  e4 weight = one;
  for (u32 j = 0; j < delta; ++j) {
    const e4 challenge = ::ab_gkr_main_layer_claim_point[round - delta + j];
    weight = e4::mul(weight, ((q >> j) & 1) != 0 ? challenge : e4::sub(one, challenge));
  }
  fold_weights[slot] = weight;
}
