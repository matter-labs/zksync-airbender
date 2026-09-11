#pragma once

#include "../../support/lookup_helpers.cuh"
#include "../window/window_geometry.cuh"

namespace airbender::gkr::backward {

// R0 reads the prebuilt constant Eq slabs. Continuations use global Eq tables;
// a kernel must not rewrite and read the constant slabs within one launch.
struct alignas(16) gkr_dr_window3_desc {
  gkr_dim_reducing_batch<e4> batch;
  e4 *partials;
  u32 log_rows;
  u32 reserved;
};

static_assert(sizeof(gkr_dr_window3_desc) == 352, "gkr_dr_window3_desc/DrWindowLaunchBinding ABI size drift");
static_assert(alignof(gkr_dr_window3_desc) == 16, "gkr_dr_window3_desc ABI alignment drift");
static_assert(sizeof(gkr_dr_window3_desc) <= BWD_WINDOW_DESC_CAP, "gkr_dr_window3_desc exceeds the CUDA kernel-argument ceiling");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, batch) == 0, "DR batch ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, partials) == 336, "DR partials ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, log_rows) == 344, "DR log_rows ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, reserved) == 348, "DR reserved ABI offset drift");
static_assert(GKR_DIM_REDUCING_INPUTS_PER_SLOT == GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, "DR pairwise tower and batch-challenge cardinalities must match");

DEVICE_FORCEINLINE bwd_window_triplet<e4> dr_window_add_triplets(const bwd_window_triplet<e4> a, const bwd_window_triplet<e4> b) {
  return {{e4::add(a.values[0], b.values[0]), e4::add(a.values[1], b.values[1]), e4::add(a.values[2], b.values[2])}};
}

} // namespace airbender::gkr::backward
