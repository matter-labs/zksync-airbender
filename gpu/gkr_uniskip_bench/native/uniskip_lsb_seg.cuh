#pragma once

#include "uniskip_lsb_pair.cuh"

namespace airbender::gkr_uniskip_bench {

// v3 R7 SEGMENTED PAIR. The block's four warps each walk their OWN atom list over the SAME
// cohort of rows, so a produced coset pair is shared by all four instead of retained per
// thread: the carrier is a block-wide slab, not a local frame. Group `g` of ANY warp maps to
// cohort row `cohort * UNISKIP_SEG_COHORT_ROWS + g`, which is why the warp index must never
// reach a row address - `uniskip_seg_set_row` overwrites the lane map's own row formula.
static_assert(offsetof(uniskip_seg_desc, list_offset) == 0);
static_assert(offsetof(uniskip_seg_desc, reserved0) == 10);
static_assert(offsetof(uniskip_seg_desc, slab_base) == 16);
static_assert(offsetof(uniskip_seg_desc, slab_stride_words) == 24);
static_assert(offsetof(uniskip_seg_desc, reserved1) == 28);
static_assert(UNISKIP_SEG_K == UNISKIP_PAIR_WARPS_128);
static_assert(UNISKIP_SEG_COHORT_ROWS == UNISKIP_PAIR_GROUPS_PER_WARP);
static_assert(UNISKIP_SEG_COHORTS * UNISKIP_SEG_COHORT_ROWS == UNISKIP_PAIR_ROWS_PER_BLOCK_128);

// Slab addressing (both carriers share the layout; the WORD pointer differs).
// unit = 8 B per lane identity; a source's span starts at plan cache_slot (multiple of 4 for E4).
DEVICE_FORCEINLINE void uniskip_seg_slab_store(u32 *slab, const u32 base, const u32 lane32, const bf c[2]) {
  uint2 v = make_uint2(bf::into_raw_u32(c[0]), bf::into_raw_u32(c[1]));
#if AB_UNISKIP_WINDOW_DIAG_ON
  // POISON HOOK, diagnostic builds only: corrupt what the prologue stored so any later
  // slab READ must change `q`. A cached arm that does not diverge under this is not
  // reading the slab it filled.
  if (ab_gkr_uniskip_poison_slots) {
    v.x = bf::into_raw_u32(bf::add(c[0], bf::ONE()));
    v.y = bf::into_raw_u32(bf::add(c[1], bf::ONE()));
  }
#endif
  reinterpret_cast<uint2 *>(slab)[base * 32 + lane32] = v;
}

DEVICE_FORCEINLINE void uniskip_seg_slab_load(const u32 *slab, const u32 base, const u32 lane32, bf c[2]) {
  const uint2 v = reinterpret_cast<const uint2 *>(slab)[base * 32 + lane32];
  c[0] = bf(v.x);
  c[1] = bf(v.y);
}

// E4: [c-object][lane32][4 limbs] inside the 4-unit span; base*32*8 is 1,024 B aligned.
DEVICE_FORCEINLINE void uniskip_seg_slab_store(u32 *slab, const u32 base, const u32 lane32, const e4 c[2]) {
  uint4 *span = reinterpret_cast<uint4 *>(slab + base * 64);
  uint4 lo = uniskip_coset_pack(c[0]);
  uint4 hi = uniskip_coset_pack(c[1]);
#if AB_UNISKIP_WINDOW_DIAG_ON
  if (ab_gkr_uniskip_poison_slots) {
    lo.x = bf::into_raw_u32(bf::add(bf(lo.x), bf::ONE()));
    hi.x = bf::into_raw_u32(bf::add(bf(hi.x), bf::ONE()));
  }
#endif
  span[lane32] = lo;
  span[32 + lane32] = hi;
}

DEVICE_FORCEINLINE void uniskip_seg_slab_load(const u32 *slab, const u32 base, const u32 lane32, e4 c[2]) {
  const uint4 *span = reinterpret_cast<const uint4 *>(slab + base * 64);
  c[0] = uniskip_coset_unpack(span[lane32]);
  c[1] = uniskip_coset_unpack(span[32 + lane32]);
}

// The same addressing through the cached global path. `st.wb` keeps a block's fills in its
// own L1 for the `ld.ca` re-reads, which is what makes a device-memory slab a carrier rather
// than a round trip to DRAM - the seg-VM production pattern (gkr/backward/segmented_vm.cu).
DEVICE_FORCEINLINE void uniskip_seg_gmem_store(u32 *slab, const u32 base, const u32 lane32, const bf c[2]) {
  uint2 v = make_uint2(bf::into_raw_u32(c[0]), bf::into_raw_u32(c[1]));
#if AB_UNISKIP_WINDOW_DIAG_ON
  if (ab_gkr_uniskip_poison_slots) {
    v.x = bf::into_raw_u32(bf::add(c[0], bf::ONE()));
    v.y = bf::into_raw_u32(bf::add(c[1], bf::ONE()));
  }
#endif
  store<uint2, st_modifier::wb>(reinterpret_cast<uint2 *>(slab), v, base * 32 + lane32);
}

DEVICE_FORCEINLINE void uniskip_seg_gmem_load(const u32 *slab, const u32 base, const u32 lane32, bf c[2]) {
  const uint2 v = load<uint2, ld_modifier::ca>(reinterpret_cast<const uint2 *>(slab), base * 32 + lane32);
  c[0] = bf(v.x);
  c[1] = bf(v.y);
}

DEVICE_FORCEINLINE void uniskip_seg_gmem_store(u32 *slab, const u32 base, const u32 lane32, const e4 c[2]) {
  uint4 *span = reinterpret_cast<uint4 *>(slab + base * 64);
  uint4 lo = uniskip_coset_pack(c[0]);
  uint4 hi = uniskip_coset_pack(c[1]);
#if AB_UNISKIP_WINDOW_DIAG_ON
  if (ab_gkr_uniskip_poison_slots) {
    lo.x = bf::into_raw_u32(bf::add(bf(lo.x), bf::ONE()));
    hi.x = bf::into_raw_u32(bf::add(bf(hi.x), bf::ONE()));
  }
#endif
  store<uint4, st_modifier::wb>(span, lo, lane32);
  store<uint4, st_modifier::wb>(span, hi, 32 + lane32);
}

DEVICE_FORCEINLINE void uniskip_seg_gmem_load(const u32 *slab, const u32 base, const u32 lane32, e4 c[2]) {
  const uint4 *span = reinterpret_cast<const uint4 *>(slab + base * 64);
  c[0] = uniskip_coset_unpack(load<uint4, ld_modifier::ca>(span, lane32));
  c[1] = uniskip_coset_unpack(load<uint4, ld_modifier::ca>(span, 32 + lane32));
}

struct uniskip_seg_carrier_smem {
  u32 *slab; // dynamic extern __shared__, plane aliases its first 2,048 B
  template <typename T> DEVICE_FORCEINLINE void store(u32 b, u32 l, const T c[2]) const { uniskip_seg_slab_store(slab, b, l, c); }
  template <typename T> DEVICE_FORCEINLINE void load(u32 b, u32 l, T c[2]) const { uniskip_seg_slab_load(slab, b, l, c); }
};

struct uniskip_seg_carrier_gmem {
  u32 *slab; // slab_base + blockIdx.x * slab_stride_words
  template <typename T> DEVICE_FORCEINLINE void store(u32 b, u32 l, const T c[2]) const { uniskip_seg_gmem_store(slab, b, l, c); }
  template <typename T> DEVICE_FORCEINLINE void load(u32 b, u32 l, T c[2]) const { uniskip_seg_gmem_load(slab, b, l, c); }
};

DEVICE_FORCEINLINE void uniskip_seg_set_row(uniskip_pair_lane &lane, const u32 cohort) {
  lane.row = blockIdx.x * u64{UNISKIP_PAIR_ROWS_PER_BLOCK_128} + cohort * UNISKIP_SEG_COHORT_ROWS + lane.group;
}

// The owner stripe: warp `w` produces exactly the plan rows the harness stamped for it, in
// the order the host emitted the table. The class branch stays warp-uniform, so production
// order remains a host-side property (`uniskip_coset_prologue`'s argument, unchanged).
template <typename Carrier>
DEVICE_FORCEINLINE void uniskip_seg_prologue(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, const uniskip_pair_lane &lane, const u32 warp,
                                             const Carrier &car) {
  const u32 lane32 = threadIdx.x & 31;
  for (u32 i = 0; i < plan.count; ++i) {
    const uniskip_prologue_entry row = plan.entry[i];
    if (u32{row.reserved} != warp)
      continue;
    if (desc.source[row.source].source_class == UNISKIP_SRC_E4_GLOBAL) {
      e4 h[2], c[2];
      uniskip_pair_resolve(desc, lane, row.source, h, c);
      car.store(row.base, lane32, c);
    } else {
      bf h[2], c[2];
      uniskip_pair_resolve(desc, lane, row.source, h, c);
      car.store(row.base, lane32, c);
    }
  }
}

// `uniskip_pair_resolve_cached` with the carrier in place of the local frame. `h` is loaded
// exactly as the control loads it; only `c` changes provenance.
template <typename Carrier, typename T>
DEVICE_FORCEINLINE void uniskip_seg_resolve(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id, const Carrier &car, T h[2],
                                            T c[2]) {
  const u32 base = desc.source[source_id].cache_slot;
  if (base == UNISKIP_CACHE_SLOT_NONE) {
    uniskip_pair_resolve(desc, lane, source_id, h, c);
    return;
  }
  uniskip_pair_load_h(desc, lane, source_id, h);
  car.load(base, threadIdx.x & 31, c);
}

// W = 0 duplicate rule under the carrier: a repeated operand inside one term still resolves
// once, so a self-product performs no second load and no second chain.
template <typename Carrier, typename T>
DEVICE_FORCEINLINE void uniskip_seg_resolve_second(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_term term, const Carrier &car,
                                                   const T ah[2], const T ac[2], T bh[2], T bc[2]) {
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      bh[k] = ah[k];
      bc[k] = ac[k];
    }
    return;
  }
  uniskip_seg_resolve(desc, lane, term.source_b, car, bh, bc);
}

// `uniskip_eval_pair_cached_body` over ONE warp's atom list: the walk bounds come from the
// seg descriptor, the resolves take the carrier, and the accumulators arrive zeroed from the
// caller because a cohort loop owns them. Everything else is the cached body verbatim.
template <typename Carrier>
DEVICE_FORCEINLINE void uniskip_seg_eval_body(const uniskip_pair_desc &desc, const uniskip_seg_desc &seg, const uniskip_pair_lane &lane, const u32 warp,
                                              const Carrier &car, e4 acc_h[2], e4 acc_c[2]) {
  for (u32 pc = u32{seg.list_offset[warp]}; pc < u32{seg.list_offset[warp + 1]};) {
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
        uniskip_seg_resolve(desc, lane, member.source_a, car, ah, ac);
        if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
          bf bh[2], bc[2];
          uniskip_seg_resolve_second(desc, lane, member, car, ah, ac, bh, bc);
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
      uniskip_seg_resolve(desc, lane, term.source_a, car, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_LINEAR_E4: {
      e4 ah[2], ac[2];
      uniskip_seg_resolve(desc, lane, term.source_a, car, ah, ac);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, ah[k], acc_h[k]);
        acc_c[k] = e4::fma(coeff, ac[k], acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_BF_BF: {
      bf ah[2], ac[2], bh[2], bc[2];
      uniskip_seg_resolve(desc, lane, term.source_a, car, ah, ac);
      uniskip_seg_resolve_second(desc, lane, term, car, ah, ac, bh, bc);
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
      uniskip_seg_resolve(desc, lane, term.source_a, car, ah, ac);
      uniskip_seg_resolve(desc, lane, term.source_b, car, bh, bc);
#pragma unroll
      for (u32 k = 0; k < 2; ++k) {
        acc_h[k] = e4::fma(coeff, e4::mul(bh[k], ah[k]), acc_h[k]);
        acc_c[k] = e4::fma(coeff, e4::mul(bc[k], ac[k]), acc_c[k]);
      }
      break;
    }
    case UNISKIP_CLASS_PRODUCT_E4_E4: {
      e4 ah[2], ac[2], bh[2], bc[2];
      uniskip_seg_resolve(desc, lane, term.source_a, car, ah, ac);
      uniskip_seg_resolve_second(desc, lane, term, car, ah, ac, bh, bc);
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

// The cohort tail: cohort 0 writes the block's partials cell, the rest add into it.
DEVICE_FORCEINLINE void uniskip_seg_rmw(e4 *slot, const u32 cohort, const e4 value) { *slot = cohort == 0 ? value : e4::add(*slot, value); }

// FOLD-FIRST. The pair epilogue's prefix - eq at the cohort row, then the two cross-group
// shuffles - and an RMW tail: cohort 0 writes the block's partials, the rest add into them.
DEVICE_FORCEINLINE void uniskip_seg_epilogue(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const u32 cohort, e4 acc_h[2], e4 acc_c[2],
                                             e4 *plane) {
  const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.row));
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::mul(acc_h[k], eq);
    acc_c[k] = e4::mul(acc_c[k], eq);
  }
#pragma unroll
  for (int mask = UNISKIP_PAIR_LANES; mask < 32; mask <<= 1)
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      acc_h[k] = e4::add(acc_h[k], uniskip_lsb_shfl_xor_e4(acc_h[k], mask));
      acc_c[k] = e4::add(acc_c[k], uniskip_lsb_shfl_xor_e4(acc_c[k], mask));
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
    for (u32 w = 1; w < UNISKIP_SEG_K; ++w)
      total = e4::add(total, plane[w * UNISKIP_CELLS + threadIdx.x]);
    e4 *slot = desc.partials + blockIdx.x * UNISKIP_CELLS + threadIdx.x;
    *slot = cohort == 0 ? total : e4::add(*slot, total);
  }
}

// ACCUMULATOR-FIRST DIAGNOSTIC. The four warps hold TERM-DISJOINT partials of the same four
// rows, so their accumulators can meet before either shuffle: warps 1..3 publish four `e4`
// per thread, warp 0 absorbs them and finishes the reduction alone. It prices the fold-first
// epilogue's two extra shuffles per warp against a wider plane.
//
// `eq` is applied PRE-PUBLISH by all four warps, not post-barrier by warp 0. Exact by
// linearity - `eq` is a function of the cohort row, which is warp-independent, so
// `(sum_w a_w) * eq == sum_w (a_w * eq)` - and load-bearing twice: it holds the arm at 72
// registers with no spill, and it makes the eq work identical to the fold-first arm's, so
// the A/B prices the shuffles alone.
DEVICE_FORCEINLINE void uniskip_seg_epilogue_acc(const uniskip_pair_desc &desc, const uniskip_pair_lane &lane, const u32 cohort, e4 acc_h[2], e4 acc_c[2],
                                                 e4 *plane) {
  const u32 warp = threadIdx.x / 32;
  const u32 lane32 = threadIdx.x & 31;
  const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.row));
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::mul(acc_h[k], eq);
    acc_c[k] = e4::mul(acc_c[k], eq);
  }
  if (warp != 0) {
    e4 *slot = plane + (warp - 1) * 128 + lane32 * 4;
    slot[0] = acc_h[0];
    slot[1] = acc_h[1];
    slot[2] = acc_c[0];
    slot[3] = acc_c[1];
  }
  __syncthreads();
  if (warp != 0)
    return;
#pragma unroll
  for (u32 w = 1; w < UNISKIP_SEG_K; ++w) {
    const e4 *slot = plane + (w - 1) * 128 + lane32 * 4;
    acc_h[0] = e4::add(acc_h[0], slot[0]);
    acc_h[1] = e4::add(acc_h[1], slot[1]);
    acc_c[0] = e4::add(acc_c[0], slot[2]);
    acc_c[1] = e4::add(acc_c[1], slot[3]);
  }
#pragma unroll
  for (int mask = UNISKIP_PAIR_LANES; mask < 32; mask <<= 1)
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      acc_h[k] = e4::add(acc_h[k], uniskip_lsb_shfl_xor_e4(acc_h[k], mask));
      acc_c[k] = e4::add(acc_c[k], uniskip_lsb_shfl_xor_e4(acc_c[k], mask));
    }
  if (lane.group != 0)
    return;
  e4 *out = desc.partials + blockIdx.x * UNISKIP_CELLS;
  uniskip_seg_rmw(out + lane.lane, cohort, acc_h[0]);
  uniskip_seg_rmw(out + lane.lane + UNISKIP_PAIR_LANES, cohort, acc_h[1]);
  uniskip_seg_rmw(out + UNISKIP_TAPS + lane.lane, cohort, acc_c[0]);
  uniskip_seg_rmw(out + UNISKIP_TAPS + lane.lane + UNISKIP_PAIR_LANES, cohort, acc_c[1]);
}

// BARRIER LEDGER (normative): a cached body executes 3 per cohort - fill-release,
// cache-retire, and the epilogue's own - times four cohorts, plus 3 conditional
// transitions = 15. Recompute skips fill-release and executes 11. An unconditional
// transition would be 16; do not write one.
template <typename Carrier, bool RECOMPUTE, bool ACC_FIRST = false>
DEVICE_FORCEINLINE void uniskip_seg_body(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, const uniskip_seg_desc &seg, const Carrier &car,
                                         e4 *plane) {
  uniskip_pair_lane lane = uniskip_pair_lane_of<UNISKIP_SEG_K>(threadIdx.x);
  const u32 warp = threadIdx.x / 32;
#pragma unroll 1
  for (u32 cohort = 0; cohort < UNISKIP_SEG_COHORTS; ++cohort) {
    uniskip_seg_set_row(lane, cohort);
    if constexpr (!RECOMPUTE) {
      uniskip_seg_prologue(desc, plan, lane, warp, car);
      __syncthreads(); // fill-release
    }
    e4 acc_h[2] = {e4::ZERO(), e4::ZERO()};
    e4 acc_c[2] = {e4::ZERO(), e4::ZERO()};
    uniskip_seg_eval_body(desc, seg, lane, warp, car, acc_h, acc_c);
    __syncthreads(); // cache-retire: slab dead before the plane overwrites it (S)
    if constexpr (ACC_FIRST)
      uniskip_seg_epilogue_acc(desc, lane, cohort, acc_h, acc_c, plane);
    else
      uniskip_seg_epilogue(desc, lane, cohort, acc_h, acc_c, plane);
    if (cohort + 1 < UNISKIP_SEG_COHORTS)
      __syncthreads(); // transition: RMW + plane consumed before the next fill
  }
}

template <typename Carrier, bool RECOMPUTE>
DEVICE_FORCEINLINE void uniskip_segb_body(const uniskip_pair_desc &desc, const uniskip_cache_desc &plan, const uniskip_seg_desc &seg, const Carrier &car) {
  uniskip_pair_lane lane = uniskip_pair_lane_of<UNISKIP_SEG_K>(threadIdx.x);
  lane.row = blockIdx.x * u64{UNISKIP_SEG_COHORT_ROWS} + lane.group; // 4 rows/block, warp id NEVER enters
  const u32 warp = threadIdx.x / 32;
  if constexpr (!RECOMPUTE) {
    uniskip_seg_prologue(desc, plan, lane, warp, car);
    __syncthreads(); // the ONLY barrier
  }
  e4 acc_h[2] = {e4::ZERO(), e4::ZERO()};
  e4 acc_c[2] = {e4::ZERO(), e4::ZERO()};
  uniskip_seg_eval_body(desc, seg, lane, warp, car, acc_h, acc_c);
  const e4 eq = uniskip_lsb_eq_at(desc, static_cast<u32>(lane.row));
#pragma unroll
  for (u32 k = 0; k < 2; ++k) {
    acc_h[k] = e4::mul(acc_h[k], eq);
    acc_c[k] = e4::mul(acc_c[k], eq);
  }
#pragma unroll
  for (int mask = UNISKIP_PAIR_LANES; mask < 32; mask <<= 1)
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      acc_h[k] = e4::add(acc_h[k], uniskip_lsb_shfl_xor_e4(acc_h[k], mask));
      acc_c[k] = e4::add(acc_c[k], uniskip_lsb_shfl_xor_e4(acc_c[k], mask));
    }
  if (lane.group == 0) {
    e4 *slot = desc.partials + (u64{blockIdx.x} * UNISKIP_SEG_K + warp) * UNISKIP_CELLS;
    slot[lane.lane] = acc_h[0];
    slot[lane.lane + UNISKIP_PAIR_LANES] = acc_h[1];
    slot[UNISKIP_TAPS + lane.lane] = acc_c[0];
    slot[UNISKIP_TAPS + lane.lane + UNISKIP_PAIR_LANES] = acc_c[1];
  }
}

} // namespace airbender::gkr_uniskip_bench
