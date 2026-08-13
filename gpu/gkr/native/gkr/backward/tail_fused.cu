// `partials` layout: 2 * num_blocks E4 elements, interleaved as
// `[c0_block_0, c1_block_0, c0_block_1, c1_block_1, ...]`.

#include "mega_finalize.cuh"

namespace airbender::gkr {

EXTERN __global__ void ab_gkr_backward_dual_reduce_blockwise_e4_kernel(const e4 *__restrict__ contributions, const unsigned acc_size,
                                                                       e4 *__restrict__ partials) {
  constexpr unsigned BLOCK = MEGA_FINALIZE_BLOCK_THREADS;
  __shared__ e4 smem_c0[BLOCK];
  __shared__ e4 smem_c1[BLOCK];
  const unsigned tid = threadIdx.x;
  const unsigned gid = blockIdx.x * BLOCK + tid;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  if (gid < acc_size) {
    c0 = contributions[gid];
    c1 = contributions[acc_size + gid];
  }
  smem_c0[tid] = c0;
  smem_c1[tid] = c1;
  __syncthreads();

#pragma unroll
  for (unsigned stride = BLOCK / 2; stride > 0; stride >>= 1) {
    if (tid < stride) {
      smem_c0[tid] = e4::add(smem_c0[tid], smem_c0[tid + stride]);
      smem_c1[tid] = e4::add(smem_c1[tid], smem_c1[tid + stride]);
    }
    __syncthreads();
  }
  if (tid == 0) {
    partials[blockIdx.x * 2u + 0u] = smem_c0[0];
    partials[blockIdx.x * 2u + 1u] = smem_c1[0];
  }
}

// PartialsSource adapter that reads from a packed `partials[]` global buffer
// where each block-pair occupies two consecutive E4 slots.
struct PartialsFromGlobal {
  const e4 *__restrict__ p;
  DEVICE_FORCEINLINE void operator()(unsigned i, e4 &c0, e4 &c1) const {
    c0 = p[i * 2u + 0u];
    c1 = p[i * 2u + 1u];
  }
};

// PartialsSource adapter that reads directly from the per-round accumulator,
// treating index `i` as one (low-half, high-half) pair.
struct PartialsFromAcc {
  const e4 *__restrict__ acc;
  unsigned acc_size;
  DEVICE_FORCEINLINE void operator()(unsigned i, e4 &c0, e4 &c1) const {
    c0 = acc[i];
    c1 = acc[acc_size + i];
  }
};

// Stage 2: reduce the per-block partials buffer to a single pair, run the
// round-update algebra, and fold the active eq slot. Single block.
EXTERN __global__ void ab_gkr_backward_dual_finalize_from_partials_e4_kernel(const e4 *__restrict__ partials, const unsigned num_partials,
                                                                             const e4 *prev_claim_coord, u32 *seed_io, e4 *claim_io, e4 *eq_prefactor_io,
                                                                             e4 *coeffs_out, e4 *challenge_out, e4 *active_eq_slot_base,
                                                                             const unsigned active_eq_size_before_fold) {
  PartialsFromGlobal src{partials};
  mega_finalize_block<MEGA_FINALIZE_BLOCK_THREADS>(src, num_partials, prev_claim_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenge_out,
                                                   active_eq_slot_base, active_eq_size_before_fold);
}

// Single-launch combined kernel: reads `acc[]` directly, runs reduce +
// round-update + fold-eq in one block. Used when `acc_size <= BLOCK_THREADS`.
EXTERN __global__ void ab_gkr_backward_dual_finalize_from_acc_e4_kernel(const e4 *__restrict__ acc, const unsigned acc_size, const e4 *prev_claim_coord,
                                                                        u32 *seed_io, e4 *claim_io, e4 *eq_prefactor_io, e4 *coeffs_out, e4 *challenge_out,
                                                                        e4 *active_eq_slot_base, const unsigned active_eq_size_before_fold) {
  PartialsFromAcc src{acc, acc_size};
  mega_finalize_block<MEGA_FINALIZE_BLOCK_THREADS>(src, acc_size, prev_claim_coord, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenge_out,
                                                   active_eq_slot_base, active_eq_size_before_fold);
}

} // namespace airbender::gkr
