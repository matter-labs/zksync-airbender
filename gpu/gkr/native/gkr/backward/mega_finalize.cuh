#pragma once

// Shared eq-slot fold for fused-tail kernels.

#include "../../ops/gkr_ops_helpers.cuh"
#include "../support/descriptors.cuh"

namespace airbender::gkr {

using ::airbender::gkr::ops::run_round_update_single_thread;

// Parallel fold of the active eq slot, called by EVERY thread of the block.
// `active_eq_size_before_fold` is the bit count before the fold. The largest
// fold (eq_low / GKR_EQ_GROUP_TABLE_LEN / 2 = 128) fits in any block with
// BLOCK_THREADS >= 128.
//
// LSB draining eliminates the slot's LOWEST bit, so the read range
// [0, 2 * new_g_len) overlaps the write range [0, new_g_len): thread 0 reads
// element 1, which thread 1 would otherwise overwrite. Load into a register,
// barrier across the WHOLE block, then store.
template <unsigned BLOCK_THREADS> DEVICE_FORCEINLINE void fold_active_eq_slot(e4 *__restrict__ active_eq_slot_base, const unsigned active_eq_size_before_fold) {
  static_assert(BLOCK_THREADS >= GKR_EQ_GROUP_TABLE_LEN / 2, "the widest eq slot fold needs half the group table in threads");
  const unsigned tid = threadIdx.x;
  const unsigned new_g_len = active_eq_size_before_fold >= 1 ? 1u << (active_eq_size_before_fold - 1) : 0u;
  const bool folds = tid < new_g_len;
  e4 folded = e4::ZERO();
  if (folds)
    folded = e4::add(active_eq_slot_base[2 * tid], active_eq_slot_base[2 * tid + 1]);
  __syncthreads();
  if (folds)
    active_eq_slot_base[tid] = folded;
}

} // namespace airbender::gkr
