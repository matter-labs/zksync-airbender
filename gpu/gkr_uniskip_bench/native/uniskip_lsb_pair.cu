#include "uniskip_lsb_pair.cuh"

#if AB_UNISKIP_WINDOW_DIAG_ON
__device__ unsigned long long ab_gkr_uniskip_chain_calls;
__device__ __constant__ u32 ab_gkr_uniskip_poison_slots;
#endif

namespace airbender::gkr_uniskip_bench {

// Term execution at the lane's TWO taps x 2 cells. Same wire, same classes, same
// coefficient bank as R0; the lane carries four `e4` accumulators instead of two because
// it owns two taps, and every one is indexed by name alone.
DEVICE_FORCEINLINE void uniskip_eval_pair_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, e4 acc_h[2], e4 acc_c[2]) {
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::ZERO();
    acc_c[k] = e4::ZERO();
  }

  for (u32 pc = 0; pc < desc.record_count;) {
    const uniskip_term term = desc.program[pc];
    const e4 coeff = ab_gkr_uniskip_coeff_bank[term.coeff];
    if (term.term_class == UNISKIP_CLASS_GROUP_BF) {
      const u32 arity = term.source_a;
      bf sum_h[2], sum_c[2];
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        sum_h[k] = bf::ZERO();
        sum_c[k] = bf::ZERO();
      }
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        bf ah[2], ac[2];
        uniskip_pair_resolve(desc, lane, member.source_a, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[2], bc[2];
          uniskip_pair_resolve_second(desc, lane, member, ah, ac, bh, bc);
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            ah[k] = bf::mul(ah[k], bh[k]);
            ac[k] = bf::mul(ac[k], bc[k]);
          }
        }
        if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            sum_h[k] = bf::add(sum_h[k], ah[k]);
            sum_c[k] = bf::add(sum_c[k], ac[k]);
          }
        } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            sum_h[k] = bf::sub(sum_h[k], ah[k]);
            sum_c[k] = bf::sub(sum_c[k], ac[k]);
          }
        } else {
          const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            sum_h[k] = bf::fma(immediate, ah[k], sum_h[k]);
            sum_c[k] = bf::fma(immediate, ac[k], sum_c[k]);
          }
        }
      }
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, sum_h[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, sum_c[k], acc_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf ah[2], ac[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[2], ac[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_pair_resolve_second(desc, lane, term, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, bf::mul(ah[k], bh[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, bf::mul(ac[k], bc[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf ah[2], ac[2];
      e4 bh[2], bc[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_pair_resolve(desc, lane, term.source_b, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(bh[k], ah[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(bc[k], ac[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_pair_resolve_second(desc, lane, term, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(ah[k], bh[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(ac[k], bc[k]), acc_c[k]);
      }
      break;
    }
    }
    ++pc;
  }
}

// v3 R2: LSB lane-striped uniskip at W = 0 with a PAIR-RESIDENT producer. A block is
// 8 warps x 4 groups = 32 logical rows; `finalize` and the partials layout are R0's.
//
// REDUCTION. Lane (group, l) holds all four of its cells for ONE row, so `eq` — which is
// per row — applies once to all four before anything merges. The warp's four groups sit at
// lane offsets `group * 8`, so corresponding lanes across groups differ in the two high
// lane bits: `xor 8` then `xor 16` sums the warp's four rows per cell slot. (R0's single
// `xor 16` was for two groups; this is the same argument at 4, and it is gated by `q`, not
// by analogy.) Lanes 0..7 then hold cells `l`, `l + 8`, `16 + l`, `24 + l` — all 32 — and
// the block's eight warps meet in R0's shared plane.
// WINDOW TERM BODY. A separate text from `uniskip_eval_pair_body` on purpose: the R2
// control is source-frozen, so it cannot be templated or wrapped without putting its
// emitted SASS at risk. Differences from the control are exactly: the per-record tag byte,
// and `bf` resolutions routed through the windowed resolve. `e4` operands are never tagged
// (the host validator rejects it) and keep the control's resolve.
DEVICE_FORCEINLINE void uniskip_eval_pair_win_body(const uniskip_pair_desc &desc, const uniskip_window_desc &win, const uniskip_pair_lane &lane, e4 acc_h[2],
                                                   e4 acc_c[2]) {
  uniskip_win_slots slots;
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::ZERO();
    acc_c[k] = e4::ZERO();
  }

  for (u32 pc = 0; pc < desc.record_count;) {
    const uniskip_term term = desc.program[pc];
    const e4 coeff = ab_gkr_uniskip_coeff_bank[term.coeff];
    if (term.term_class == UNISKIP_CLASS_GROUP_BF) {
      const u32 arity = term.source_a;
      bf sum_h[2], sum_c[2];
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        sum_h[k] = bf::ZERO();
        sum_c[k] = bf::ZERO();
      }
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        const u8 tags = win.tags[pc + m];
        bf ah[2], ac[2];
        uniskip_pair_resolve_win(desc, lane, member.source_a, uniskip_win_tag_a(tags), slots, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[2], bc[2];
          uniskip_pair_resolve_second_win(desc, lane, member, uniskip_win_tag_b(tags), slots, ah, ac, bh, bc);
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            ah[k] = bf::mul(ah[k], bh[k]);
            ac[k] = bf::mul(ac[k], bc[k]);
          }
        }
        if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            sum_h[k] = bf::add(sum_h[k], ah[k]);
            sum_c[k] = bf::add(sum_c[k], ac[k]);
          }
        } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            sum_h[k] = bf::sub(sum_h[k], ah[k]);
            sum_c[k] = bf::sub(sum_c[k], ac[k]);
          }
        } else {
          const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
#pragma unroll
          for (u32 k = 0; k < 2; ++k) {
            sum_h[k] = bf::fma(immediate, ah[k], sum_h[k]);
            sum_c[k] = bf::fma(immediate, ac[k], sum_c[k]);
          }
        }
      }
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, sum_h[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, sum_c[k], acc_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    const u8 tags = win.tags[pc];
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf ah[2], ac[2];
      uniskip_pair_resolve_win(desc, lane, term.source_a, uniskip_win_tag_a(tags), slots, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[2], ac[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_win(desc, lane, term.source_a, uniskip_win_tag_a(tags), slots, ah, ac);
      uniskip_pair_resolve_second_win(desc, lane, term, uniskip_win_tag_b(tags), slots, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, bf::mul(ah[k], bh[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, bf::mul(ac[k], bc[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf ah[2], ac[2];
      e4 bh[2], bc[2];
      uniskip_pair_resolve_win(desc, lane, term.source_a, uniskip_win_tag_a(tags), slots, ah, ac);
      uniskip_pair_resolve(desc, lane, term.source_b, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(bh[k], ah[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(bc[k], ac[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve(desc, lane, term.source_a, ah, ac);
      uniskip_pair_resolve_second(desc, lane, term, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(ah[k], bh[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(ac[k], bc[k]), acc_c[k]);
      }
      break;
    }
    }
    ++pc;
  }
}

// The epilogue, shared by the three NEW entry points. The control keeps its own inline
// copy so that its SASS cannot move; this is the same text, extracted once for the arms.
DEVICE_FORCEINLINE void uniskip_pair_epilogue(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, e4 acc_h[2], e4 acc_c[2], e4 *plane) {
  const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.row));
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::mul(acc_h[k], eq);
    acc_c[k] = e4::mul(acc_c[k], eq);
  }
#pragma unroll
  for (int mask = UNISKIP_PAIR_LANES; mask < 32; mask <<= 1) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      acc_h[k] = e4::add(acc_h[k], uniskip_lsb_shfl_xor_e4(acc_h[k], mask));
      acc_c[k] = e4::add(acc_c[k], uniskip_lsb_shfl_xor_e4(acc_c[k], mask));
    }
  }
  const u32 warp = threadIdx.x / 32;
  if (lane.group == 0) {
    e4 *slot = plane + warp * UNISKIP_CELLS;
    slot[lane.lane] = acc_h[0];
    slot[lane.lane + UNISKIP_PAIR_LANES] = acc_h[1];
    slot[UNISKIP_TAPS + lane.lane] = acc_c[0];
    slot[UNISKIP_TAPS + lane.lane + UNISKIP_PAIR_LANES] = acc_c[1];
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

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_kernel(const __grid_constant__ uniskip_pair_desc desc) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];

  const uniskip_pair_lane lane = uniskip_pair_lane_of(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_body(desc, lane, acc_h, acc_c);

  const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.row));
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::mul(acc_h[k], eq);
    acc_c[k] = e4::mul(acc_c[k], eq);
  }
#pragma unroll
  for (int mask = UNISKIP_PAIR_LANES; mask < 32; mask <<= 1) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      acc_h[k] = e4::add(acc_h[k], uniskip_lsb_shfl_xor_e4(acc_h[k], mask));
      acc_c[k] = e4::add(acc_c[k], uniskip_lsb_shfl_xor_e4(acc_c[k], mask));
    }
  }

  const u32 warp = threadIdx.x / 32;
  if (lane.group == 0) {
    e4 *slot = plane + warp * UNISKIP_CELLS;
    slot[lane.lane] = acc_h[0];
    slot[lane.lane + UNISKIP_PAIR_LANES] = acc_h[1];
    slot[UNISKIP_TAPS + lane.lane] = acc_c[0];
    slot[UNISKIP_TAPS + lane.lane + UNISKIP_PAIR_LANES] = acc_c[1];
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

// The `t` arm: the control body verbatim, differing only by `__launch_bounds__`. It was
// built to make ptxas keep the eight preloaded twiddles alive rather than rematerialize
// them; measured, it does NOT — the bank-3 twiddle loads are byte-identical with and
// without the bound, and what the bound moved was a bank-0 stream from the uniform to the
// vector datapath (see iteration_times.md, v3 R3). A `__global__` cannot be called as a
// device function and extracting a shared helper would edit the frozen control, so the
// entry text is duplicated deliberately.
EXTERN __global__ __launch_bounds__(UNISKIP_THREADS_PER_BLOCK, 3) void ab_gkr_uniskip_eval_lsb_pair_lb_kernel(const __grid_constant__ uniskip_pair_desc desc) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];
  const uniskip_pair_lane lane = uniskip_pair_lane_of(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_body(desc, lane, acc_h, acc_c);
  uniskip_pair_epilogue(desc, lane, acc_h, acc_c, plane);
}

// The `w` arm. `wnone` is this same kernel launched with an all-`none` tag stream, which
// is why there is no separate diagnostic entry point: it pays the window's registers and
// branches and takes none of its saving.
EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_win_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                               const __grid_constant__ uniskip_window_desc win) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];
  const uniskip_pair_lane lane = uniskip_pair_lane_of(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_win_body(desc, win, lane, acc_h, acc_c);
  uniskip_pair_epilogue(desc, lane, acc_h, acc_c, plane);
}

// The `wt` arm: window plus the launch-bounds twiddle trade.
EXTERN __global__ __launch_bounds__(UNISKIP_THREADS_PER_BLOCK,
                                    3) void ab_gkr_uniskip_eval_lsb_pair_win_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                       const __grid_constant__ uniskip_window_desc win) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];
  const uniskip_pair_lane lane = uniskip_pair_lane_of(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_win_body(desc, win, lane, acc_h, acc_c);
  uniskip_pair_epilogue(desc, lane, acc_h, acc_c, plane);
}

} // namespace airbender::gkr_uniskip_bench
