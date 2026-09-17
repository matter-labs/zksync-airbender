#pragma once

#include <type_traits>

#include "../../support/lookup_helpers.cuh"
#include "../window/window_abi.cuh"

namespace airbender::gkr::backward {

// R0 reads the prebuilt constant Eq slabs. Continuations use global Eq tables;
// a kernel must not rewrite and read the constant slabs within one launch.
struct alignas(16) gkr_dr_window3_desc {
  gkr_dim_reducing_batch<e4> batch;
  e4 *partials;
  u32 log_rows;
  u32 reserved;
};

static_assert(sizeof(gkr_dr_window3_desc) == 304, "gkr_dr_window3_desc/DrWindowLaunchBinding ABI size drift");
static_assert(alignof(gkr_dr_window3_desc) == 16, "gkr_dr_window3_desc ABI alignment drift");
static_assert(sizeof(gkr_dr_window3_desc) <= BWD_WINDOW_DESC_CAP, "gkr_dr_window3_desc exceeds the CUDA kernel-argument ceiling");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, batch) == 0, "DR batch ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, partials) == 288, "DR partials ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, log_rows) == 296, "DR log_rows ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, reserved) == 300, "DR reserved ABI offset drift");
static_assert(GKR_DIM_REDUCING_INPUTS_PER_SLOT == GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, "DR pairwise tower and batch-challenge cardinalities must match");

struct alignas(16) gkr_dr_cont_window3_desc {
  gkr_dim_reducing_batch<e4> batch;
  const e4 *eq_high_0;
  const e4 *eq_high_1;
  e4 *partials;
  const e4 *claim_point;
  u32 log_rows;
  u32 start_round;
  u32 reserved[2];
};

static_assert(sizeof(gkr_dr_cont_window3_desc) == 336, "gkr_dr_cont_window3_desc/DrWindowContinuationLaunchBinding ABI size drift");
static_assert(alignof(gkr_dr_cont_window3_desc) == 16, "gkr_dr_cont_window3_desc ABI alignment drift");
static_assert(sizeof(gkr_dr_cont_window3_desc) <= BWD_WINDOW_DESC_CAP, "gkr_dr_cont_window3_desc exceeds the CUDA kernel-argument ceiling");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, batch) == 0, "DR continuation batch ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, eq_high_0) == 288, "DR continuation eq_high_0 ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, eq_high_1) == 296, "DR continuation eq_high_1 ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, partials) == 304, "DR continuation partials ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, claim_point) == 312, "DR continuation claim_point ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, log_rows) == 320, "DR continuation log_rows ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, start_round) == 324, "DR continuation start_round ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, reserved) == 328, "DR continuation reserved ABI offset drift");
static_assert(std::is_standard_layout_v<gkr_dr_cont_window3_desc>, "DR continuation descriptor must be standard-layout");
static_assert(std::is_trivially_copyable_v<gkr_dr_cont_window3_desc>, "DR continuation descriptor must be trivially copyable");

} // namespace airbender::gkr::backward
