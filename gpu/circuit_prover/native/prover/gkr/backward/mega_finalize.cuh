#pragma once

// Single-block "mega-finalize" template used by the backward sumcheck
// fused-tail kernels. The block:
//  * Cooperatively reduces a partials buffer to `(e_partial, c_partial)` in
//    shared memory (each thread accumulates a strided slice of the partials,
//    then a standard tree reduction collapses to slot 0).
//  * Thread 0 runs the round-update algebra (`run_round_update_single_thread`):
//    normalize claim, derive 4 univariate coefficients, Blake2s-commit them,
//    extract the next folding challenge, fold claim/eq_prefactor.
//  * Threads with `tid < new_g_len` fold the active eq slot
//    (eq_low or eq_high[k]) in parallel with thread 0's update. The two
//    sub-tasks touch disjoint memory, so no inter-task barrier is required
//    inside the block.
//
// PartialsSource: callable `(unsigned i, e4 &c0, e4 &c1)` that returns the
// per-index partial pair. Two adapters in `tail_fused.cu`:
//  * `PartialsFromGlobal`: reads per-block partials from a global scratch
//    buffer (used by the two-stage path, and by the warp-partial round
//    kernels in `round{0,1,2,3}_flat_warp_partial.cu`).
//  * `PartialsFromAcc`: reads directly from the accumulator (combined
//    single-launch path when `acc_size <= BLOCK_THREADS`).
//
// The template lives in a header so each finalize kernel can instantiate
// it next to its entry point, keeping the round-update + fold-eq algebra
// in exactly one place. The shared algebra used inside
// `run_round_update_single_thread` is defined in
// `gpu/circuit_prover/native/ops/gkr_ops_helpers.cuh`.

#include "../../../ops/gkr_ops_helpers.cuh"
#include "../support/descriptors.cuh"

namespace airbender::prover::gkr {

using ::airbender::ops::gkr_ops::run_round_update_single_thread;

// Maximum threads-per-block for the mega-finalize launch. Matches the
// 256-thread default used by the existing CUB-driven tail. Folding the eq
// slot uses at most `GKR_EQ_GROUP_TABLE_LEN / 2 = 128` threads, well under
// this cap.
constexpr unsigned MEGA_FINALIZE_BLOCK_THREADS = 256;

template <unsigned BLOCK_THREADS, typename PartialsSource>
DEVICE_FORCEINLINE void mega_finalize_block(const PartialsSource &partials, const unsigned num_partials, const e4 *__restrict__ prev_claim_coord,
                                            u32 *__restrict__ seed_io, e4 *__restrict__ claim_io, e4 *__restrict__ eq_prefactor_io, e4 *__restrict__ coeffs_out,
                                            e4 *__restrict__ challenge_out, e4 *__restrict__ active_eq_slot_base, const unsigned active_eq_size_before_fold) {
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

  // Thread 0: run the round-update algebra against the reduced
  // (e_partial, c_partial). Reads `smem_c0[0]` / `smem_c1[0]` before any
  // other thread overwrites them — the active eq slot is disjoint memory,
  // so no extra barrier is needed.
  if (tid == 0) {
    const e4 e_partial = smem_c0[0];
    const e4 c_partial = smem_c1[0];
    const e4 prev_coord = *prev_claim_coord;
    run_round_update_single_thread(e_partial, c_partial, prev_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenge_out);
  }

  // Parallel fold of the active eq slot. `active_eq_size_before_fold` is the
  // bit count (matches `g_size_before` in `fold_factored_eq_one_round`). The
  // largest fold (eq_low / GKR_EQ_GROUP_TABLE_LEN / 2 = 128) fits in any
  // block with BLOCK_THREADS >= 128.
  if (active_eq_size_before_fold >= 1) {
    const unsigned new_g_len = 1u << (active_eq_size_before_fold - 1);
    if (tid < new_g_len) {
      const e4 low = active_eq_slot_base[tid];
      const e4 high = active_eq_slot_base[tid + new_g_len];
      active_eq_slot_base[tid] = e4::add(low, high);
    }
  }
  // Implicit kernel-exit sync makes both updates visible to subsequent
  // launches on the same stream.
}

} // namespace airbender::prover::gkr
