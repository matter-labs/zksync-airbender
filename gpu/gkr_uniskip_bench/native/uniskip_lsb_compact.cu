#include "uniskip_lsb_compact.cuh"

__device__ __constant__
    airbender::gkr_uniskip_bench::uniskip_compact_slot ab_gkr_uniskip_compact_sched[airbender::gkr_uniskip_bench::UNISKIP_COMPACT_MAX_ROUNDS * 32];

namespace airbender::gkr_uniskip_bench {

// Term execution at the lane's ELEMENTS rows x 2 cells. Same wire, same classes, same
// coefficient bank as R0; only the element count per lane changes, and the accumulators
// are still indexed by name alone.
template <u32 G>
DEVICE_FORCEINLINE void uniskip_eval_compact_body(const uniskip_compact_desc &desc, const uniskip_compact_lane<G> &lane,
                                                  e4 acc_h[uniskip_compact_lane<G>::ELEMENTS], e4 acc_c[uniskip_compact_lane<G>::ELEMENTS]) {
  constexpr u32 ELEMENTS = uniskip_compact_lane<G>::ELEMENTS;
#pragma unroll
  for (u32 k = 0; k < ELEMENTS; ++k) {
    acc_h[k] = e4::ZERO();
    acc_c[k] = e4::ZERO();
  }

  for (u32 pc = 0; pc < desc.record_count;) {
    const uniskip_term term = desc.program[pc];
    const e4 coeff = ab_gkr_uniskip_coeff_bank[term.coeff];
    if (term.term_class == UNISKIP_CLASS_GROUP_BF) {
      const u32 arity = term.source_a;
      bf sum_h[ELEMENTS];
      bf sum_c[ELEMENTS];
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        sum_h[k] = bf::ZERO();
        sum_c[k] = bf::ZERO();
      }
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        bf ah[ELEMENTS], ac[ELEMENTS];
        uniskip_compact_resolve<G>(desc, lane, member.source_a, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[ELEMENTS], bc[ELEMENTS];
          uniskip_compact_resolve_second<G>(desc, lane, member, ah, ac, bh, bc);
#pragma unroll
          for (u32 k = 0; k < ELEMENTS; ++k) {
            ah[k] = bf::mul(ah[k], bh[k]);
            ac[k] = bf::mul(ac[k], bc[k]);
          }
        }
        if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
#pragma unroll
          for (u32 k = 0; k < ELEMENTS; ++k) {
            sum_h[k] = bf::add(sum_h[k], ah[k]);
            sum_c[k] = bf::add(sum_c[k], ac[k]);
          }
        } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
#pragma unroll
          for (u32 k = 0; k < ELEMENTS; ++k) {
            sum_h[k] = bf::sub(sum_h[k], ah[k]);
            sum_c[k] = bf::sub(sum_c[k], ac[k]);
          }
        } else {
          const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
#pragma unroll
          for (u32 k = 0; k < ELEMENTS; ++k) {
            sum_h[k] = bf::fma(immediate, ah[k], sum_h[k]);
            sum_c[k] = bf::fma(immediate, ac[k], sum_c[k]);
          }
        }
      }
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        acc_h[k] = e4::fma(coeff, sum_h[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, sum_c[k], acc_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf ah[ELEMENTS], ac[ELEMENTS];
      uniskip_compact_resolve<G>(desc, lane, term.source_a, ah, ac);
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[ELEMENTS], ac[ELEMENTS];
      uniskip_compact_resolve<G>(desc, lane, term.source_a, ah, ac);
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[ELEMENTS], ac[ELEMENTS], bh[ELEMENTS], bc[ELEMENTS];
      uniskip_compact_resolve<G>(desc, lane, term.source_a, ah, ac);
      uniskip_compact_resolve_second<G>(desc, lane, term, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        acc_h[k] = e4::fma(coeff, bf::mul(ah[k], bh[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, bf::mul(ac[k], bc[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf ah[ELEMENTS], ac[ELEMENTS];
      e4 bh[ELEMENTS], bc[ELEMENTS];
      uniskip_compact_resolve<G>(desc, lane, term.source_a, ah, ac);
      uniskip_compact_resolve<G>(desc, lane, term.source_b, bh, bc);
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(bh[k], ah[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(bc[k], ac[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[ELEMENTS], ac[ELEMENTS], bh[ELEMENTS], bc[ELEMENTS];
      uniskip_compact_resolve<G>(desc, lane, term.source_a, ah, ac);
      uniskip_compact_resolve_second<G>(desc, lane, term, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < ELEMENTS; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(ah[k], bh[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(ac[k], bc[k]), acc_c[k]);
      }
      break;
    }
    }
    ++pc;
  }
}

// v3 R1: LSB lane-striped uniskip at W = 0 with a shared-memory-staged, COMPACTED
// producer. A block is 8 warps x G groups logical rows; `finalize` and the partials
// layout are R0's, unchanged.
//
// eq is per row, so it is applied to each of the lane's ELEMENTS accumulator pairs before
// they collapse; after that the reduction is R0's - `xor 16` merges the two half-warps,
// which hold the same cell for complementary rows, then a shared plane crosses the block.
template <u32 G> DEVICE_FORCEINLINE void uniskip_eval_compact(const uniskip_compact_desc &desc) {
  constexpr u32 ELEMENTS = uniskip_compact_lane<G>::ELEMENTS;
  constexpr u32 ROUNDS = uniskip_compact_total_rounds(G);
  static_assert(ROUNDS <= UNISKIP_COMPACT_MAX_ROUNDS);

  __shared__ uniskip_compact_slot sched[ROUNDS * 32];
  __shared__ bf staging[UNISKIP_WARPS_PER_BLOCK * G * UNISKIP_TAPS];
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];

  // The schedule is lane-indexed, so it is copied out of `__constant__` ONCE per block -
  // paying the divergent-address serialization here instead of on every round.
  for (u32 i = threadIdx.x; i < ROUNDS * 32; i += UNISKIP_THREADS_PER_BLOCK)
    sched[i] = ab_gkr_uniskip_compact_sched[i];
  __syncthreads();

  const u32 warp = threadIdx.x / 32;
  const u32 lane_id = threadIdx.x % 32;
  uniskip_compact_lane<G> lane;
  lane.tap = lane_id & (UNISKIP_TAPS - 1);
  lane.perm_tap = uniskip_compact_bank_perm(lane.tap);
  lane.half = lane_id >> UNISKIP_LOG_TAPS;
  lane.row_base = blockIdx.x * u64{UNISKIP_WARPS_PER_BLOCK * G} + warp * G;
  lane.stage = staging + warp * G * UNISKIP_TAPS;
  lane.sched = sched;

  e4 acc_h[ELEMENTS], acc_c[ELEMENTS];
  uniskip_eval_compact_body<G>(desc, lane, acc_h, acc_c);

  e4 sum_h = e4::ZERO();
  e4 sum_c = e4::ZERO();
#pragma unroll
  for (u32 k = 0; k < ELEMENTS; ++k) {
    const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.row(k)));
    sum_h = e4::add(sum_h, e4::mul(acc_h[k], eq));
    sum_c = e4::add(sum_c, e4::mul(acc_c[k], eq));
  }
  sum_h = e4::add(sum_h, uniskip_lsb_shfl_xor_e4(sum_h, UNISKIP_TAPS));
  sum_c = e4::add(sum_c, uniskip_lsb_shfl_xor_e4(sum_c, UNISKIP_TAPS));

  if (lane.half == 0) {
    plane[warp * UNISKIP_CELLS + lane.tap] = sum_h;
    plane[warp * UNISKIP_CELLS + UNISKIP_TAPS + lane.tap] = sum_c;
  }
  __syncthreads();
  if (threadIdx.x < UNISKIP_CELLS) {
    e4 total = plane[threadIdx.x];
#pragma unroll
    for (u32 w = 1; w < UNISKIP_WARPS_PER_BLOCK; ++w)
      total = e4::add(total, plane[w * UNISKIP_CELLS + threadIdx.x]);
    desc.partials[blockIdx.x * UNISKIP_CELLS + threadIdx.x] = total;
  }
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_compact_g4_kernel(const __grid_constant__ uniskip_compact_desc desc) { uniskip_eval_compact<4>(desc); }

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_compact_g8_kernel(const __grid_constant__ uniskip_compact_desc desc) { uniskip_eval_compact<8>(desc); }

} // namespace airbender::gkr_uniskip_bench
