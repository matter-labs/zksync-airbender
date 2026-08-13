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

// v3 R4 CACHED TERM BODY. A separate text from `uniskip_eval_pair_body` on purpose: the R2
// control is source-frozen, so it cannot be templated or wrapped without putting its
// emitted SASS at risk. Differences from the control are exactly the resolve calls, which
// take the frame and consult the record's `cache_slot`. Admission is source-global, so
// every operand - A, B, group member, either class - carries its own disposition and the
// R3 two-operand problem cannot recur.
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                      e4 acc_h[2], e4 acc_c[2]) {
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
        uniskip_pair_resolve_cached(desc, lane, member.source_a, cache, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[2], bc[2];
          uniskip_pair_resolve_second_cached(desc, lane, member, cache, ah, ac, bh, bc);
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
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[2], ac[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_second_cached(desc, lane, term, cache, ah, ac, bh, bc);
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
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_cached(desc, lane, term.source_b, cache, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(bh[k], ah[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(bc[k], ac[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_second_cached(desc, lane, term, cache, ah, ac, bh, bc);
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

// The epilogue, shared by the FOUR non-control entry points: the three R3 window arms and
// R4's control128. The 256 control keeps its own inline copy so that its SASS cannot move;
// this is the same text, extracted once for the arms.
//
// WARNING: templating it on WARPS gave it four FROZEN consumers at once - win, win_lb (R3
// baselines) and control128 (the R4 128-axis baseline), plus the R3 t arm through the lane
// map. One edit here puts all of them at risk in a single build; the per-function SASS
// comparison against task1-final-sass.txt and task1a-control128-sass.txt is the only guard.
template <u32 WARPS = UNISKIP_WARPS_PER_BLOCK>
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
    for (u32 w = 1; w < WARPS; ++w)
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

// The `wt` arm: window plus `__launch_bounds__`. The bound was meant as a twiddle-remat
// trade; measured, it trades nothing there — bank-3 twiddle loads are byte-identical with
// and without it. Its real effect is the 82 -> 80 register cut that buys back the third
// block (see iteration_times.md, v3 R3).
EXTERN __global__ __launch_bounds__(UNISKIP_THREADS_PER_BLOCK,
                                    3) void ab_gkr_uniskip_eval_lsb_pair_win_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                       const __grid_constant__ uniskip_window_desc win) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];
  const uniskip_pair_lane lane = uniskip_pair_lane_of(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_win_body(desc, win, lane, acc_h, acc_c);
  uniskip_pair_epilogue(desc, lane, acc_h, acc_c, plane);
}

// The v3 R4 128-thread no-cache BASELINE (spec 3.5). Four warps, so the shared reduction
// plane and the epilogue's cross-warp sum halve and a block covers 16 rows; the grid
// doubles. Per-warp geometry, the lane map and the program walk are the 256 control's,
// unchanged - only the block shape moves. No `__launch_bounds__`, matching the 256
// control: a baseline must not carry a codegen hint the arm it anchors does not.
// It is FROZEN from here: no cache code ever enters this entry point.
EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_128_kernel(const __grid_constant__ uniskip_pair_desc desc) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  const uniskip_pair_lane lane = uniskip_pair_lane_of<UNISKIP_PAIR_WARPS_128>(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_body(desc, lane, acc_h, acc_c);
  uniskip_pair_epilogue<UNISKIP_PAIR_WARPS_128>(desc, lane, acc_h, acc_c, plane);
}

// v3 R4 CACHED KERNELS - one function per block size, sharing the device body. The frame is
// C_max-sized for EVERY arm, so all arms are one SASS body varying only in uploaded state;
// a per-arm frame would confound codegen with footprint. `cache0` is this same kernel with
// an all-sentinel record clone and an empty table, which prices the fixed machinery the way
// R3's `wnone` priced the window's.
template <u32 WARPS> DEVICE_FORCEINLINE void uniskip_eval_pair_cached(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_body(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                  const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS];
  uniskip_eval_pair_cached<UNISKIP_WARPS_PER_BLOCK>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                      const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached<UNISKIP_PAIR_WARPS_128>(desc, plan, plane);
}

// OCCUPANCY-GATE SIBLING. Unbounded, the 128 cached body compiles to 75 registers = 6
// blocks/SM against control128's 7, so the 128-axis cache-vs-control contrast would carry
// an occupancy step - R3's `w` failure mode exactly. The bound restores the control's block
// count by capping registers at 72. Both variants ship (R3's wt/wtnone precedent): this is
// the measurement arm, and the unbounded one prices what the bound costs.
EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                              const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached<UNISKIP_PAIR_WARPS_128>(desc, plan, plane);
}

// v3 R9 GATE-FIRST TERM BODY. Same program, same classes, same coefficient bank as the R4
// cached body; what moves is WHEN each domain is live. Per factor: load H, gate on H, turn
// that storage into C, gate on C - so a term's peak liveness is one domain of its operands
// instead of both.
//
// THE INVARIANT, and the reason `q` must stay bit-identical: each accumulator sees its own
// factors and terms in exactly the cached body's order. Only the interleaving between
// `acc_h` and `acc_c` changes. The group member's product therefore goes to a temporary
// rather than back into the operand - the control overwrites `ah[k]`, which here would
// destroy the H the chain still needs.
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_reorder_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                              e4 acc_h[2], e4 acc_c[2]) {
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
        const bool product = member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF;
        bf a[2], b[2];
        uniskip_pair_load_h(desc, lane, member.source_a, a);
        if (product) {
          uniskip_pair_load_h_second_reorder(desc, lane, member, a, b);
          bf p[2];
#pragma unroll
          for (u32 k = 0; k < 2; ++k)
            p[k] = bf::mul(a[k], b[k]);
          uniskip_pair_group_sum_reorder(desc, member, p, sum_h);
        } else {
          uniskip_pair_group_sum_reorder(desc, member, a, sum_h);
        }
        uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
        if (product) {
          uniskip_pair_coset_second_reorder(desc, lane, member, cache, a, b);
          bf p[2];
#pragma unroll
          for (u32 k = 0; k < 2; ++k)
            p[k] = bf::mul(a[k], b[k]);
          uniskip_pair_group_sum_reorder(desc, member, p, sum_c);
        } else {
          uniskip_pair_group_sum_reorder(desc, member, a, sum_c);
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
      bf a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, a[k], acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, a[k], acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, a[k], acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, a[k], acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, bf::mul(a[k], b[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, bf::mul(a[k], b[k]), acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      // B (the `e4`) first: the classes differ, so no duplicate rule applies here, and the
      // gate keeps the control's `e4 x bf` operand order.
      bf a[2];
      e4 b[2];
      uniskip_pair_load_h(desc, lane, term.source_b, b);
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, e4::mul(b[k], a[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_b, cache, b);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, e4::mul(b[k], a[k]), acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, e4::mul(a[k], b[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, e4::mul(a[k], b[k]), acc_c[k]);
      break;
    }
    }
    ++pc;
  }
}

// The R9 kernels. The prologue is the R4 one unchanged - production still happens once per
// admitted source before the walk - so the reorder is the walk's alone.
template <u32 WARPS> DEVICE_FORCEINLINE void uniskip_eval_pair_cached_reorder(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_reorder_body(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                      const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_reorder<UNISKIP_PAIR_WARPS_128>(desc, plan, plane);
}

// The UNBOUNDED sibling, on the incumbent's precedent: the bounded body is the measurement
// arm at the incumbent's block count, and this one prices what the bound costs - and is the
// register-attribution comparator against the unbounded cached body.
EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                              const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_reorder<UNISKIP_PAIR_WARPS_128>(desc, plan, plane);
}

// v3 R9b CORRECTED GROUPED PATH. Everything outside the GROUP_BF member loop is the R9 body's
// text; inside it the per-member decode is what changes. Two independent axes:
//
// - `HOIST_CLASS` = false is lever C: the accumuland converges on `p`, which carries the
//   non-product value too, so the two phases reach ONE dispatch call site each while both
//   `if (product)` branches stay. true is lever B: one class branch encloses both phases with
//   its body duplicated per branch, so a member takes one class test instead of two.
// - `COEFF_FORM`: `R9` is the R9 dispatch, re-tested per accumulate. `KIND` resolves
//   `member.coeff` once per member and still branches on the resolved kind per accumulate - the
//   attribution cell for "decode once but branch twice". `BRANCH` is lever D proper: ONE runtime
//   three-way test per member, each arm carrying the member's whole sequence, so no coefficient
//   test runs between the two accumulates.
//
// What IS forced: the product is ephemeral, because the coset transform overwrites its operands'
// storage in place - but only lever C needs to name it, and `BRANCH` + `HOIST_CLASS` multiplies
// straight into the accumulate with no slot at all.
template <bool HOIST_CLASS, u32 COEFF_FORM>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_regroup_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                              e4 acc_h[2], e4 acc_c[2]) {
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
        if constexpr (COEFF_FORM == UNISKIP_PAIR_COEFF_FORM_BRANCH) {
          if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
            uniskip_pair_group_member_reorder<UNISKIP_PAIR_COEFF_ONE, HOIST_CLASS>(desc, lane, cache, member, bf::ZERO(), sum_h, sum_c);
          } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
            uniskip_pair_group_member_reorder<UNISKIP_PAIR_COEFF_NEG_ONE, HOIST_CLASS>(desc, lane, cache, member, bf::ZERO(), sum_h, sum_c);
          } else {
            uniskip_pair_group_member_reorder<UNISKIP_PAIR_COEFF_IMMEDIATE, HOIST_CLASS>(
                desc, lane, cache, member, desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED], sum_h, sum_c);
          }
          continue;
        }
        using form = uniskip_pair_coeff_form_reorder<COEFF_FORM == UNISKIP_PAIR_COEFF_FORM_KIND>;
        const typename form::coeff mc = form::resolve(desc, member);
        bf a[2];
        uniskip_pair_load_h(desc, lane, member.source_a, a);
        if constexpr (HOIST_CLASS) {
          if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
            bf b[2], p[2];
            uniskip_pair_load_h_second_reorder(desc, lane, member, a, b);
#pragma unroll
            for (u32 k = 0; k < 2; ++k)
              p[k] = bf::mul(a[k], b[k]);
            form::sum(desc, mc, p, sum_h);
            uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
            uniskip_pair_coset_second_reorder(desc, lane, member, cache, a, b);
#pragma unroll
            for (u32 k = 0; k < 2; ++k)
              p[k] = bf::mul(a[k], b[k]);
            form::sum(desc, mc, p, sum_c);
          } else {
            form::sum(desc, mc, a, sum_h);
            uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
            form::sum(desc, mc, a, sum_c);
          }
        } else {
          const bool product = member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF;
          bf b[2], p[2];
          if (product) {
            uniskip_pair_load_h_second_reorder(desc, lane, member, a, b);
#pragma unroll
            for (u32 k = 0; k < 2; ++k)
              p[k] = bf::mul(a[k], b[k]);
          } else {
#pragma unroll
            for (u32 k = 0; k < 2; ++k)
              p[k] = a[k];
          }
          form::sum(desc, mc, p, sum_h);
          uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
          if (product) {
            uniskip_pair_coset_second_reorder(desc, lane, member, cache, a, b);
#pragma unroll
            for (u32 k = 0; k < 2; ++k)
              p[k] = bf::mul(a[k], b[k]);
          } else {
#pragma unroll
            for (u32 k = 0; k < 2; ++k)
              p[k] = a[k];
          }
          form::sum(desc, mc, p, sum_c);
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
      bf a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, a[k], acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, a[k], acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, a[k], acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, a[k], acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, bf::mul(a[k], b[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, bf::mul(a[k], b[k]), acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf a[2];
      e4 b[2];
      uniskip_pair_load_h(desc, lane, term.source_b, b);
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, e4::mul(b[k], a[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_b, cache, b);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, e4::mul(b[k], a[k]), acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, e4::mul(a[k], b[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, e4::mul(a[k], b[k]), acc_c[k]);
      break;
    }
    }
    ++pc;
  }
}

template <u32 WARPS, bool HOIST_CLASS, u32 COEFF_FORM>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_regroup(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_regroup_body<HOIST_CLASS, COEFF_FORM>(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

// The R9b GRID: six corrected bodies x three register budgets. Body axis: `c`/`b` are levers C
// and B over the R9 dispatch, `ck`/`bk` decode the coefficient once per member but still branch on
// the resolved kind per accumulate, `cd`/`bd` are lever D proper - ONE runtime three-way
// coefficient test per member, each arm carrying the member's whole sequence. Budget axis: `_lb`
// is the R9 drop-in's `(128, 7)`, `_lb6` relaxes the floor to 6 blocks, and the bare name is
// unbounded - a step of the 4-warp ladder costs 4 warps here against 9 in the windowed bench that
// took the same trade and won. Written out per symbol rather than macro-generated: the gate tables
// and the Rust launchers key on these exact names.

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                        const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_R9>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                         const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_R9>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_R9>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                         const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_KIND>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                          const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_KIND>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                 const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_KIND>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                         const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_BRANCH>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                          const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_BRANCH>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                 const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, false, UNISKIP_PAIR_COEFF_FORM_BRANCH>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                        const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_R9>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                         const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_R9>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_R9>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                         const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_KIND>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                          const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_KIND>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                 const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_KIND>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                         const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_BRANCH>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                          const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_BRANCH>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                 const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup<UNISKIP_PAIR_WARPS_128, true, UNISKIP_PAIR_COEFF_FORM_BRANCH>(desc, plan, plane);
}

// The two REFERENCE bodies at the relaxed floor, on the same unchanged wrappers. Their `(128,
// 7)` and unbounded cells are already built and pinned, so only `_lb6` is new: the incumbent
// with a relaxed bound is the cell R9's record left as arithmetic.
EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                               const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached<UNISKIP_PAIR_WARPS_128>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                       const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_reorder<UNISKIP_PAIR_WARPS_128>(desc, plan, plane);
}

// The BOUNDED no-cache baseline at 128. R3's `t` arm is the precedent that forces this to
// exist: pricing a launch bound on the cached side alone would assume the bound's cost is
// additive across bodies, and `t` measured +3.43 % on a body whose registers the bound did
// not even change. So the 128 axis carries both baselines, and the cached-vs-control
// contrast can be taken bound-to-bound. control128's own text is untouched.
EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  const uniskip_pair_lane lane = uniskip_pair_lane_of<UNISKIP_PAIR_WARPS_128>(threadIdx.x);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_body(desc, lane, acc_h, acc_c);
  uniskip_pair_epilogue<UNISKIP_PAIR_WARPS_128>(desc, lane, acc_h, acc_c, plane);
}

// v3 R10 LAZY BF ACCUMULATORS over the INCUMBENT walk. Everything outside the GROUP_BF member
// loop is `uniskip_eval_pair_cached_body`'s text; inside it `sum_h` / `sum_c` are `ACC` instead of
// `bf`, so no product is reduced on its way into the sum and the whole sum folds once. The class
// test and the coefficient test are the incumbent's, one each per member. `ACC` is the accumulator
// STATE - `uniskip_acc_w96` or `uniskip_acc_a64` - and nothing outside the group path changes
// state: the sumcheck accumulators stay `e4` and canonical, which is the division of labour
// green's 24-arm campaign settled.
template <typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_lazy_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                           e4 acc_h[2], e4 acc_c[2]) {
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
      ACC sum_h[2], sum_c[2];
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_zero(sum_h[k]);
        uniskip_acc_zero(sum_c[k]);
      }
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        bf ah[2], ac[2];
        uniskip_pair_resolve_cached(desc, lane, member.source_a, cache, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[2], bc[2];
          uniskip_pair_resolve_second_cached(desc, lane, member, cache, ah, ac, bh, bc);
          uniskip_acc_group_product(desc, member, ah, ac, bh, bc, sum_h, sum_c);
        } else {
          uniskip_acc_group_value(desc, member, ah, ac, sum_h, sum_c);
        }
      }
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, uniskip_acc_fold(sum_h[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, uniskip_acc_fold(sum_c[k]), acc_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf ah[2], ac[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[2], ac[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_second_cached(desc, lane, term, cache, ah, ac, bh, bc);
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
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_cached(desc, lane, term.source_b, cache, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(bh[k], ah[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(bc[k], ac[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_second_cached(desc, lane, term, cache, ah, ac, bh, bc);
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

// The same two accumulator states over R9b's `C+D` walk - the one repair that beat the R9
// drop-in - so the accumulator effect is separable from the repair. Everything outside the
// GROUP_BF member loop is the R9 reordered body's text; inside, D's single runtime three-way
// coefficient test per member dispatches the member's whole sequence at a compile-time kind.
template <typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_regroup_lazy_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane,
                                                                   const uniskip_coset_cache &cache, e4 acc_h[2], e4 acc_c[2]) {
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
      ACC sum_h[2], sum_c[2];
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_zero(sum_h[k]);
        uniskip_acc_zero(sum_c[k]);
      }
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
          uniskip_pair_group_member_lazy<UNISKIP_PAIR_COEFF_ONE>(desc, lane, cache, member, bf::ZERO(), sum_h, sum_c);
        } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
          uniskip_pair_group_member_lazy<UNISKIP_PAIR_COEFF_NEG_ONE>(desc, lane, cache, member, bf::ZERO(), sum_h, sum_c);
        } else {
          uniskip_pair_group_member_lazy<UNISKIP_PAIR_COEFF_IMMEDIATE>(desc, lane, cache, member, desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED],
                                                                       sum_h, sum_c);
        }
      }
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, uniskip_acc_fold(sum_h[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, uniskip_acc_fold(sum_c[k]), acc_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, a[k], acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, a[k], acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, a[k], acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, a[k], acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, bf::mul(a[k], b[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, bf::mul(a[k], b[k]), acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf a[2];
      e4 b[2];
      uniskip_pair_load_h(desc, lane, term.source_b, b);
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, e4::mul(b[k], a[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_b, cache, b);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, e4::mul(b[k], a[k]), acc_c[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_h[k] = e4::fma(coeff, e4::mul(a[k], b[k]), acc_h[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        acc_c[k] = e4::fma(coeff, e4::mul(a[k], b[k]), acc_c[k]);
      break;
    }
    }
    ++pc;
  }
}

template <u32 WARPS, typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_lazy(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_lazy_body<ACC>(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

template <u32 WARPS, typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_regroup_lazy(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_regroup_lazy_body<ACC>(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

// The R10 GRID: two accumulator states x two parent walks x three register budgets. `w96` / `a64`
// name the state, an absent parent tag is the incumbent walk and `reorder_cd` is R9b's `C+D`, and
// the budget suffixes are R9b's - `_lb` = `(128, 7)`, `_lb6` = `(128, 6)`, bare = unbounded - so
// the two rungs' static tables compose cell for cell. Written out per symbol rather than
// macro-generated: the gate tables and the Rust launchers key on these exact names.

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                  const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                   const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                          const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                  const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                   const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                          const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                             const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                              const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                     const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                             const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                              const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                     const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_lazy<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

// v3 R10 OUTER-LEVEL WIDE ACCUMULATION over the INCUMBENT walk. The walk, the resolves and the
// grouped member sums are `uniskip_eval_pair_cached_body`'s text unchanged - the member sums stay
// CANONICAL `bf`, which is what keeps this a pure LEVEL contrast against the group-level arms. What
// changes is the four outer accumulators: they are `uniskip_acc_e4<ACC>` for the whole pass and fold
// once at the end, so `e4::fma`'s four reductions per term per accumulator disappear. The body still
// hands the epilogue plain `e4`, so nothing downstream moves.
template <typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_outer_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                            e4 acc_h[2], e4 acc_c[2]) {
  uniskip_acc_e4<ACC> wide_h[2], wide_c[2];
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    uniskip_acc_e4_zero(wide_h[k]);
    uniskip_acc_e4_zero(wide_c[k]);
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
        uniskip_pair_resolve_cached(desc, lane, member.source_a, cache, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[2], bc[2];
          uniskip_pair_resolve_second_cached(desc, lane, member, cache, ah, ac, bh, bc);
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
        uniskip_acc_e4_bf(wide_h[k], coeff, sum_h[k]);
        uniskip_acc_e4_bf(wide_c[k], coeff, sum_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf ah[2], ac[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_e4_bf(wide_h[k], coeff, ah[k]);
        uniskip_acc_e4_bf(wide_c[k], coeff, ac[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[2], ac[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_e4_e4(wide_h[k], coeff, ah[k]);
        uniskip_acc_e4_e4(wide_c[k], coeff, ac[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_second_cached(desc, lane, term, cache, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_e4_bf(wide_h[k], coeff, bf::mul(ah[k], bh[k]));
        uniskip_acc_e4_bf(wide_c[k], coeff, bf::mul(ac[k], bc[k]));
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf ah[2], ac[2];
      e4 bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_cached(desc, lane, term.source_b, cache, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_e4_e4(wide_h[k], coeff, e4::mul(bh[k], ah[k]));
        uniskip_acc_e4_e4(wide_c[k], coeff, e4::mul(bc[k], ac[k]));
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[2], ac[2], bh[2], bc[2];
      uniskip_pair_resolve_cached(desc, lane, term.source_a, cache, ah, ac);
      uniskip_pair_resolve_second_cached(desc, lane, term, cache, ah, ac, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_e4_e4(wide_h[k], coeff, e4::mul(ah[k], bh[k]));
        uniskip_acc_e4_e4(wide_c[k], coeff, e4::mul(ac[k], bc[k]));
      }
      break;
    }
    }
    ++pc;
  }
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = uniskip_acc_e4_fold(wide_h[k]);
    acc_c[k] = uniskip_acc_e4_fold(wide_c[k]);
  }
}

// The same outer-level accumulators over R9b's `C+D` walk. Everything is
// `uniskip_eval_pair_cached_regroup_body<false, BRANCH>`'s text - including its canonical `bf`
// member sums - with the four outer accumulators held wide.
template <typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_regroup_outer_body(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane,
                                                                    const uniskip_coset_cache &cache, e4 acc_h[2], e4 acc_c[2]) {
  uniskip_acc_e4<ACC> wide_h[2], wide_c[2];
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    uniskip_acc_e4_zero(wide_h[k]);
    uniskip_acc_e4_zero(wide_c[k]);
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
        if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
          uniskip_pair_group_member_reorder<UNISKIP_PAIR_COEFF_ONE, false>(desc, lane, cache, member, bf::ZERO(), sum_h, sum_c);
        } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
          uniskip_pair_group_member_reorder<UNISKIP_PAIR_COEFF_NEG_ONE, false>(desc, lane, cache, member, bf::ZERO(), sum_h, sum_c);
        } else {
          uniskip_pair_group_member_reorder<UNISKIP_PAIR_COEFF_IMMEDIATE, false>(desc, lane, cache, member,
                                                                                 desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED], sum_h, sum_c);
        }
      }
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        uniskip_acc_e4_bf(wide_h[k], coeff, sum_h[k]);
        uniskip_acc_e4_bf(wide_c[k], coeff, sum_c[k]);
      }
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF: {
      bf a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_bf(wide_h[k], coeff, a[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_bf(wide_c[k], coeff, a[k]);
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 a[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_e4(wide_h[k], coeff, a[k]);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_e4(wide_c[k], coeff, a[k]);
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_bf(wide_h[k], coeff, bf::mul(a[k], b[k]));
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_bf(wide_c[k], coeff, bf::mul(a[k], b[k]));
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_E4: {
      bf a[2];
      e4 b[2];
      uniskip_pair_load_h(desc, lane, term.source_b, b);
      uniskip_pair_load_h(desc, lane, term.source_a, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_e4(wide_h[k], coeff, e4::mul(b[k], a[k]));
      uniskip_pair_coset_reorder(desc, lane, term.source_b, cache, b);
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_e4(wide_c[k], coeff, e4::mul(b[k], a[k]));
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 a[2], b[2];
      uniskip_pair_load_h(desc, lane, term.source_a, a);
      uniskip_pair_load_h_second_reorder(desc, lane, term, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_e4(wide_h[k], coeff, e4::mul(a[k], b[k]));
      uniskip_pair_coset_reorder(desc, lane, term.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, term, cache, a, b);
#pragma unroll
      for (u32 k = 0; k < 2; ++k)
        uniskip_acc_e4_e4(wide_c[k], coeff, e4::mul(a[k], b[k]));
      break;
    }
    }
    ++pc;
  }
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = uniskip_acc_e4_fold(wide_h[k]);
    acc_c[k] = uniskip_acc_e4_fold(wide_c[k]);
  }
}

template <u32 WARPS, typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_outer(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_outer_body<ACC>(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

template <u32 WARPS, typename ACC>
DEVICE_FORCEINLINE void uniskip_eval_pair_cached_regroup_outer(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, e4 *plane) {
  const uniskip_pair_lane lane = uniskip_pair_lane_of<WARPS>(threadIdx.x);
  uniskip_coset_cache cache;
  uniskip_coset_prologue(desc, plan, lane, cache);
  e4 acc_h[2], acc_c[2];
  uniskip_eval_pair_cached_regroup_outer_body<ACC>(desc, lane, cache, acc_h, acc_c);
  uniskip_pair_epilogue<WARPS>(desc, lane, acc_h, acc_c, plane);
}

// The OUTER-LEVEL grid, `o` for outer: `ow96` / `oa64` are the same two states holding the walk's
// four `e4` accumulators instead of a group's member sums, over the same two parent walks at the
// same three budgets. Twelve more symbols, so the level axis is readable against the group-level
// twelve above.

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_ow96_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                   const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_ow96_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                    const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_ow96_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                           const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_oa64_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                   const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    6) void ab_gkr_uniskip_eval_lsb_pair_cached_oa64_128_lb6_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                    const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_oa64_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                           const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_ow96_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                              const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_ow96_128_lb6_kernel(
    const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_ow96_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                      const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_w96>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32,
                                    7) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_oa64_128_lb_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                                              const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 6) void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_oa64_128_lb6_kernel(
    const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

EXTERN __global__ void ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_oa64_128_kernel(const __grid_constant__ uniskip_pair_desc desc,
                                                                                      const __grid_constant__ uniskip_cache_desc plan) {
  __shared__ e4 plane[UNISKIP_PAIR_WARPS_128 * UNISKIP_CELLS];
  uniskip_eval_pair_cached_regroup_outer<UNISKIP_PAIR_WARPS_128, uniskip_acc_a64>(desc, plan, plane);
}

} // namespace airbender::gkr_uniskip_bench
