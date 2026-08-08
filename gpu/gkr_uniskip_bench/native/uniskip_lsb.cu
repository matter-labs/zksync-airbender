#include "uniskip_lsb.cuh"

// Storage for the `__constant__` symbol declared by uniskip_lsb.cuh.
__device__ __constant__ bf ab_gkr_uniskip_ntt_twiddles[airbender::gkr_uniskip_bench::UNISKIP_NTT_TABLES * airbender::gkr_uniskip_bench::UNISKIP_TAPS];

namespace airbender::gkr_uniskip_bench {

// TERM EXECUTION at the lane's TWO cells. Same wire, same classes, same coefficient bank
// and immediates as `uniskip_eval_body` - the program is identical at every cell, so the
// only thing that changes with the lane map is how many accumulators a lane carries. Two
// e4 here against v2's four; both are indexed only by name, never dynamically.
DEVICE_FORCEINLINE void uniskip_eval_lsb_body(const uniskip_lsb_desc &desc, const uniskip_lsb_lane &lane, e4 &acc_h, e4 &acc_c) {
  acc_h = e4::ZERO();
  acc_c = e4::ZERO();

  for (u32 pc = 0; pc < desc.record_count;) {
    const uniskip_term term = desc.program[pc];
    const e4 coeff = ab_gkr_uniskip_coeff_bank[term.coeff];
    if (term.term_class == UNISKIP_CLASS_GROUP_BF) {
      const u32 arity = term.source_a;
      bf sum_h = bf::ZERO();
      bf sum_c = bf::ZERO();
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        bf ah, ac;
        uniskip_lsb_resolve(desc, lane, member.source_a, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh, bc;
          uniskip_lsb_resolve_second(desc, lane, member, ah, ac, bh, bc);
          ah = bf::mul(ah, bh);
          ac = bf::mul(ac, bc);
        }
        if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
          sum_h = bf::add(sum_h, ah);
          sum_c = bf::add(sum_c, ac);
        } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
          sum_h = bf::sub(sum_h, ah);
          sum_c = bf::sub(sum_c, ac);
        } else {
          const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
          sum_h = bf::fma(immediate, ah, sum_h);
          sum_c = bf::fma(immediate, ac, sum_c);
        }
      }
      acc_h = e4::fma(coeff, sum_h, acc_h);
      acc_c = e4::fma(coeff, sum_c, acc_c);
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf ah, ac;
      uniskip_lsb_resolve(desc, lane, term.source_a, ah, ac);
      acc_h = e4::fma(coeff, ah, acc_h);
      acc_c = e4::fma(coeff, ac, acc_c);
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah, ac;
      uniskip_lsb_resolve(desc, lane, term.source_a, ah, ac);
      acc_h = e4::fma(coeff, ah, acc_h);
      acc_c = e4::fma(coeff, ac, acc_c);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah, ac, bh, bc;
      uniskip_lsb_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_lsb_resolve_second(desc, lane, term, ah, ac, bh, bc);
      acc_h = e4::fma(coeff, bf::mul(ah, bh), acc_h);
      acc_c = e4::fma(coeff, bf::mul(ac, bc), acc_c);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf ah, ac;
      e4 bh, bc;
      uniskip_lsb_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_lsb_resolve(desc, lane, term.source_b, bh, bc);
      acc_h = e4::fma(coeff, e4::mul(bh, ah), acc_h);
      acc_c = e4::fma(coeff, e4::mul(bc, ac), acc_c);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah, ac, bh, bc;
      uniskip_lsb_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_lsb_resolve_second(desc, lane, term, ah, ac, bh, bc);
      acc_h = e4::fma(coeff, e4::mul(ah, bh), acc_h);
      acc_c = e4::fma(coeff, e4::mul(ac, bc), acc_c);
      break;
    }
    }
    ++pc;
  }
}

// v3 R0: LSB lane-striped uniskip at W = 0 - every reference loads its group and runs the
// shuffle-NTT, nothing is retained across references. One kernel; the pass is this plus
// `finalize`.
//
// REDUCTION. Within a half-warp the lanes hold DIFFERENT cells, so a half-warp tree would
// wrongly mix them. Corresponding lanes across the two half-warps (`xor 16`) hold the
// SAME cell for the warp's two groups and `q` sums over groups, so one `shfl_xor(16)` per
// accumulator is the whole warp-level combine; the block's eight same-cell slots then meet
// in a 4 KB shared plane. Shared memory rather than atomics because `e4` has none, and
// 4096 + 1024 B per block is nowhere near the sm_120 occupancy cliff (registers bind first).
// `eq` is warp-uniform per group and is applied at the epilogue, BEFORE the merge - the two
// half-warps carry different rows.
//
// `Geometry` guarantees rows == gridDim.x * UNISKIP_LSB_ROWS_PER_BLOCK (log_rows >= 5), so
// no group is out of range, and the addressing bound (log_rows <= 21) keeps the element
// index inside `load`'s 32-bit offset exactly as in the plane-major ordering.
EXTERN __global__ void ab_gkr_uniskip_eval_lsb_w0_kernel(const __grid_constant__ uniskip_lsb_desc desc) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];

  const uniskip_lsb_lane lane = uniskip_lsb_lane_of(threadIdx.x);
  e4 acc_h, acc_c;
  uniskip_eval_lsb_body(desc, lane, acc_h, acc_c);

  const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.group));
  acc_h = e4::mul(acc_h, eq);
  acc_c = e4::mul(acc_c, eq);
  acc_h = e4::add(acc_h, uniskip_lsb_shfl_xor_e4(acc_h, UNISKIP_TAPS));
  acc_c = e4::add(acc_c, uniskip_lsb_shfl_xor_e4(acc_c, UNISKIP_TAPS));

  const u32 warp = threadIdx.x / 32;
  if ((threadIdx.x % 32) < UNISKIP_TAPS) {
    plane[warp * UNISKIP_CELLS + lane.tap] = acc_h;
    plane[warp * UNISKIP_CELLS + UNISKIP_TAPS + lane.tap] = acc_c;
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

} // namespace airbender::gkr_uniskip_bench
