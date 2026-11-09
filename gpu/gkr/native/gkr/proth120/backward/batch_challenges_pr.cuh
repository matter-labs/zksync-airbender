#pragma once

#include "../../support/descriptors.cuh"
#include "primitives/proth120.cuh"

EXTERN __device__ __constant__ ::airbender::primitives::field::proth120
    ab_pr_gkr_dim_reducing_batch_challenge_table[::airbender::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
