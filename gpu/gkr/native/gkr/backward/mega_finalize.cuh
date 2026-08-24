#pragma once

// Shared reduction and transcript finalization for fused-tail kernels.

#include "../../ops/gkr_ops_helpers.cuh"
#include "../support/descriptors.cuh"

namespace airbender::gkr {

using ::airbender::gkr::ops::run_round_update_single_thread;

// Maximum threads-per-block for the mega-finalize launch. Matches the
// 256-thread default used by the existing CUB-driven tail. Folding the eq
// slot uses at most `GKR_EQ_GROUP_TABLE_LEN / 2 = 128` threads, well under
// this cap.
constexpr unsigned MEGA_FINALIZE_BLOCK_THREADS = 256;

// NOT __restrict__: both schedulers build the output claim-point view over the same symbol the input view reads, so round `step` reads and writes one address.
template <unsigned BLOCK_THREADS, typename PartialsSource>
DEVICE_FORCEINLINE void mega_finalize_block(const PartialsSource &partials, const unsigned num_partials, const e4 *prev_claim_coord, u32 *__restrict__ seed_io,
                                            e4 *__restrict__ claim_io, e4 *__restrict__ eq_prefactor_io, e4 *__restrict__ coeffs_out, e4 *challenge_out,
                                            e4 *__restrict__ active_eq_slot_base, const unsigned active_eq_size_before_fold) {
  static_assert(BLOCK_THREADS > 0 && (BLOCK_THREADS & (BLOCK_THREADS - 1)) == 0, "BLOCK_THREADS must be a power of two");

  __shared__ e4 smem_c0[BLOCK_THREADS];
  __shared__ e4 smem_c1[BLOCK_THREADS];
  const unsigned tid = threadIdx.x;

  // Strided initial accumulation handles num_partials larger than the block,
  // e.g. stage-2 reading num_blocks partial pairs.
  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  for (unsigned i = tid; i < num_partials; i += BLOCK_THREADS) {
    e4 p0, p1;
    partials(i, p0, p1);
    c0 = e4::add(c0, p0);
    c1 = e4::add(c1, p1);
  }
  smem_c0[tid] = c0;
  smem_c1[tid] = c1;
  __syncthreads();

  // Standard tree reduction in shared memory.
#pragma unroll
  for (unsigned stride = BLOCK_THREADS / 2; stride > 0; stride >>= 1) {
    if (tid < stride) {
      smem_c0[tid] = e4::add(smem_c0[tid], smem_c0[tid + stride]);
      smem_c1[tid] = e4::add(smem_c1[tid], smem_c1[tid + stride]);
    }
    __syncthreads();
  }

  // Thread 0: run the round-update algebra against the reduced (e_partial, c_partial).
  if (tid == 0) {
    const e4 e_partial = smem_c0[0];
    const e4 c_partial = smem_c1[0];
    const e4 prev_coord = *prev_claim_coord;
    run_round_update_single_thread(e_partial, c_partial, prev_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenge_out);
  }

  // Parallel fold of the active eq slot. `active_eq_size_before_fold` is the
  // bit count before the fold. The largest fold
  // (eq_low / GKR_EQ_GROUP_TABLE_LEN / 2 = 128) fits in any
  // block with BLOCK_THREADS >= 128.
  //
  // LSB drain: reads [0, 2 * new_g_len) overlap writes [0, new_g_len), so load to a register, barrier across the whole block, then store.
  const unsigned new_g_len = active_eq_size_before_fold >= 1 ? 1u << (active_eq_size_before_fold - 1) : 0u;
  const bool folds = tid < new_g_len;
  e4 folded = e4::ZERO();
  if (folds)
    folded = e4::add(active_eq_slot_base[2 * tid], active_eq_slot_base[2 * tid + 1]);
  __syncthreads();
  if (folds)
    active_eq_slot_base[tid] = folded;
  // Implicit kernel-exit sync makes both updates visible to subsequent
  // launches on the same stream.
}

} // namespace airbender::gkr
