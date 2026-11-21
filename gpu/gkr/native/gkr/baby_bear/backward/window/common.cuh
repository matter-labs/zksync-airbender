#pragma once

#include "gkr/baby_bear/support/eq_inline.cuh"
#include "gkr/baby_bear/support/kernel_helpers.cuh"
#include "gkr/backward/window/common.cuh"

namespace airbender::gkr {

static_assert(BWD_COEFF_BANK_CAPACITY * sizeof(e4) == 28 * 1024, "coefficient bank size drift");

} // namespace airbender::gkr

EXTERN __device__ __constant__ e4 ab_gkr_bwd_coeff_bank[airbender::gkr::BWD_COEFF_BANK_CAPACITY];
#define AB_GKR_BWD_COEFF(slot) (::ab_gkr_bwd_coeff_bank[(slot)])

EXTERN __device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_bwd_fold_weights[airbender::gkr::BWD_FOLD_WEIGHT_SLOTS];

EXTERN __global__ void ab_gkr_bwd_build_fold_weights_kernel(e4 *fold_weights, u32 round);
