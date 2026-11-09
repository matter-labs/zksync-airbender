#pragma once

#include <type_traits>

#include "../../../backward/window/window_geometry.cuh"
#include "../../../support/lookup_helpers.cuh"
#include "../accumulator_pr.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;
namespace pr_dr_bwd = ::airbender::gkr::backward;

struct alignas(16) pr_dr_window_desc {
  gkr_dim_reducing_batch<pr> batch;
  const pr *batch_challenges;
  const pr *eq_high_0;
  const pr *eq_high_1;
  pr *partials;
  const pr *claim_point;
  u32 log_rows;
  u32 start_round;
};

static_assert(sizeof(gkr_dim_reducing_batch<pr>) == 288 && alignof(gkr_dim_reducing_batch<pr>) == 8, "Proth120 DR batch ABI drift");
static_assert(sizeof(pr_dr_window_desc) == 336 && alignof(pr_dr_window_desc) == 16, "Proth120 DR window descriptor ABI drift");
static_assert(sizeof(pr_dr_window_desc) <= BWD_WINDOW_DESC_CAP, "Proth120 DR window descriptor exceeds the kernel-argument ceiling");
static_assert(__builtin_offsetof(pr_dr_window_desc, batch) == 0 && __builtin_offsetof(pr_dr_window_desc, batch_challenges) == 288 &&
                  __builtin_offsetof(pr_dr_window_desc, eq_high_0) == 296 && __builtin_offsetof(pr_dr_window_desc, eq_high_1) == 304 &&
                  __builtin_offsetof(pr_dr_window_desc, partials) == 312 && __builtin_offsetof(pr_dr_window_desc, claim_point) == 320 &&
                  __builtin_offsetof(pr_dr_window_desc, log_rows) == 328 && __builtin_offsetof(pr_dr_window_desc, start_round) == 332,
              "Proth120 DR window descriptor offsets drift");
static_assert(std::is_standard_layout_v<pr_dr_window_desc> && std::is_trivially_copyable_v<pr_dr_window_desc>,
              "Proth120 DR window descriptor must be a plain record");
static_assert(GKR_DIM_REDUCING_INPUTS_PER_SLOT == GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, "DR pairwise tower and batch-challenge cardinalities must match");
static_assert(GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_OUTPUTS_PER_SLOT <= PR_SUM32_TERMS, "Proth120 DR window cell sums exceed one lazy chunk");

} // namespace airbender::gkr::proth120::backward
