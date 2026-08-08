#pragma once

#include "uniskip_lsb.cuh"

namespace airbender::gkr_uniskip_bench {

// v3 R1 GEOMETRY. R0 binds lane = tap and keeps a group's 16 values in 16 lanes'
// registers, so a stage's twiddle is a per-lane constant and the ~62 unity multiplies of
// the 112 a group issues are LANE-DIVERGENT - one warp instruction has to serve unity and
// non-unity lanes at once, so a unity slot cannot be skipped. Staging the group vectors
// in shared memory dissolves that binding: an element is an address, any lane can own
// any element, and a static schedule packs only the 50 real multiplies per group into
// ceil(G * m_s / 32) rounds per stage.
//
// A warp owns G groups (G = 4 or 8, compile-time). Lane l holds G / 2 elements, ALL at
// tap l & 15: element k is group (l >> 4) + 2k. So the lane keeps its R0 cell identity -
// cell t on H and cell 16 + t on the coset, per row - and one program walk serves G rows,
// amortizing decode G / 2x better than R0.
constexpr u32 UNISKIP_COMPACT_MAX_ROUNDS = 20;

// BANK PERMUTATION. An element sits at `bank_perm(tap) * G + group`: group in the LOW
// bits so a round's lanes hit consecutive banks, and the tap permuted so the 32 / G slots
// a round touches have distinct `bank_perm` modulo 32 / G. The GF(2)-linear map with
// column images [1, 2, 5, 14]; the identity collides (`{0,1,2,3,8,9,10,11}` pairwise mod
// 8) and cost 79 % excess shared wavefronts in the first build of this mode. Derivation
// and the measured conflict-freedom proof: `src/compact.rs`. Evaluated once per thread.
DEVICE_FORCEINLINE u32 uniskip_compact_bank_perm(const u32 tap) {
  return ((tap & 1) ^ ((tap >> 2) & 1)) | ((((tap >> 1) & 1) ^ ((tap >> 3) & 1)) << 1) | ((((tap >> 2) & 1) ^ ((tap >> 3) & 1)) << 2) | (((tap >> 3) & 1) << 3);
}

// One lane's work in one round: the two staging offsets it owns and the twiddle it
// multiplies by, or 0 for "nothing to multiply". A twiddle is never zero, so the sentinel
// is unambiguous. 8 bytes, align 8, so the read is one LDS.64. Host builder and its
// coverage proof: `src/compact.rs`.
struct alignas(8) uniskip_compact_slot {
  u16 lo;
  u16 hi;
  u32 tw;
};
static_assert(sizeof(uniskip_compact_slot) == 8);
static_assert(alignof(uniskip_compact_slot) == 8);

} // namespace airbender::gkr_uniskip_bench

EXTERN __device__ __constant__
    airbender::gkr_uniskip_bench::uniskip_compact_slot ab_gkr_uniskip_compact_sched[airbender::gkr_uniskip_bench::UNISKIP_COMPACT_MAX_ROUNDS * 32];

namespace airbender::gkr_uniskip_bench {

struct uniskip_compact_desc : uniskip_vm_desc {};
static_assert(sizeof(uniskip_compact_desc) == sizeof(uniskip_vm_desc));
static_assert(offsetof(uniskip_compact_desc, eq_sizes) == 2492);

enum uniskip_compact_kind { COMPACT_DIF, COMPACT_PLAIN, COMPACT_TWIST, COMPACT_DIT };

constexpr u32 uniskip_compact_pair_rounds(const u32 groups) { return groups * (UNISKIP_TAPS / 2) / 32; }
constexpr u32 uniskip_compact_twist_rounds(const u32 groups) { return groups * UNISKIP_TAPS / 32; }
// Rounds of a phase that carry a multiply instruction. Compile-time, so a round past it
// emits NO multiply code at all - unity work costs nothing rather than being predicated.
constexpr u32 uniskip_compact_mul_rounds(const u32 groups, const u32 non_unity) { return (groups * non_unity + 31) / 32; }
constexpr u32 uniskip_compact_total_rounds(const u32 groups) { return 8 * uniskip_compact_pair_rounds(groups) + uniskip_compact_twist_rounds(groups); }

// One phase: ROUNDS passes over the warp's G * 16 staged elements, 32 lanes at a time.
// The pairs a round covers are disjoint, so a round needs no barrier inside it; phases do.
template <uniskip_compact_kind KIND, u32 ROUNDS, u32 MUL_ROUNDS>
DEVICE_FORCEINLINE void uniskip_compact_phase(bf *stage, const uniskip_compact_slot *sched, const u32 lane_id) {
#pragma unroll
  for (u32 r = 0; r < ROUNDS; ++r) {
    const uniskip_compact_slot s = sched[r * 32 + lane_id];
    if constexpr (KIND == COMPACT_TWIST) {
      stage[s.lo] = bf::mul(stage[s.lo], bf::from_reduced_raw_repr(s.tw));
    } else {
      const bf lo = stage[s.lo];
      bf hi = stage[s.hi];
      if constexpr (KIND == COMPACT_DIT) {
        if (r < MUL_ROUNDS && s.tw)
          hi = bf::mul(hi, bf::from_reduced_raw_repr(s.tw));
      }
      bf high = bf::sub(lo, hi);
      if constexpr (KIND == COMPACT_DIF) {
        if (r < MUL_ROUNDS && s.tw)
          high = bf::mul(high, bf::from_reduced_raw_repr(s.tw));
      }
      stage[s.lo] = bf::add(lo, hi);
      stage[s.hi] = high;
    }
  }
  __syncwarp();
}

// THE PRODUCER, compacted. Same pinned chain as R0 - iDIF with omega^-1, folded
// normalize+twist, DIT with omega - and the same 8 exchange stages; only the binding
// changes. Multiply instructions per warp: 14 at G = 8 (56 lane-multiplies per group) and
// 8 at G = 4 (64), against R0's 7 per 16-lane group = 112.
template <u32 G> DEVICE_FORCEINLINE void uniskip_compact_chain(bf *stage, const uniskip_compact_slot *sched, const u32 lane_id) {
  constexpr u32 PR = uniskip_compact_pair_rounds(G);
  constexpr u32 TR = uniskip_compact_twist_rounds(G);
  uniskip_compact_phase<COMPACT_DIF, PR, uniskip_compact_mul_rounds(G, 7)>(stage, sched, lane_id);
  uniskip_compact_phase<COMPACT_DIF, PR, uniskip_compact_mul_rounds(G, 6)>(stage, sched + 1 * PR * 32, lane_id);
  uniskip_compact_phase<COMPACT_DIF, PR, uniskip_compact_mul_rounds(G, 4)>(stage, sched + 2 * PR * 32, lane_id);
  uniskip_compact_phase<COMPACT_PLAIN, PR, 0>(stage, sched + 3 * PR * 32, lane_id);
  uniskip_compact_phase<COMPACT_TWIST, TR, TR>(stage, sched + 4 * PR * 32, lane_id);
  uniskip_compact_phase<COMPACT_PLAIN, PR, 0>(stage, sched + 4 * PR * 32 + TR * 32, lane_id);
  uniskip_compact_phase<COMPACT_DIT, PR, uniskip_compact_mul_rounds(G, 4)>(stage, sched + 5 * PR * 32 + TR * 32, lane_id);
  uniskip_compact_phase<COMPACT_DIT, PR, uniskip_compact_mul_rounds(G, 6)>(stage, sched + 6 * PR * 32 + TR * 32, lane_id);
  uniskip_compact_phase<COMPACT_DIT, PR, uniskip_compact_mul_rounds(G, 7)>(stage, sched + 7 * PR * 32 + TR * 32, lane_id);
}

// Everything a lane needs. `stage` is this warp's slice of the staging buffer, `sched`
// the block's shared copy of the schedule - both must be shared memory, because a
// lane-indexed `__constant__` read in the hot path serializes.
template <u32 G> struct uniskip_compact_lane {
  static constexpr u32 ELEMENTS = G / 2;
  u32 tap;
  u32 perm_tap;
  u32 half;
  u64 row_base;
  bf *stage;
  const uniskip_compact_slot *sched;

  DEVICE_FORCEINLINE u32 group(const u32 k) const { return half + 2 * k; }
  DEVICE_FORCEINLINE u32 slot(const u32 k) const { return perm_tap * G + group(k); }
  DEVICE_FORCEINLINE u64 row(const u32 k) const { return row_base + group(k); }
};

// Element index of (source, this lane's k-th group, this lane's tap) in the LSB ordering.
// For a fixed k the warp reads 32 CONSECUTIVE elements - lanes 0..15 are one group and
// 16..31 the next - so a `bf` round is one 128 B run and an `e4` round one 512 B run.
template <u32 G>
DEVICE_FORCEINLINE size_t uniskip_compact_element(const uniskip_vm_desc &desc, const uniskip_source_record rec, const uniskip_compact_lane<G> &lane,
                                                  const u32 k) {
  const size_t column = rec.addr & 0x7f;
  return (((column << desc.log_rows) + lane.row(k)) << UNISKIP_LOG_TAPS) + lane.tap;
}

// H is never staged: it is the loaded value and stays in registers, so the transform is
// free to run in place and destroy the buffer. Only the coset comes back out of it.
template <u32 G>
DEVICE_FORCEINLINE void uniskip_compact_resolve(const uniskip_vm_desc &desc, const uniskip_compact_lane<G> &lane, const u16 source_id,
                                                bf h[uniskip_compact_lane<G>::ELEMENTS], bf c[uniskip_compact_lane<G>::ELEMENTS]) {
  constexpr u32 ELEMENTS = uniskip_compact_lane<G>::ELEMENTS;
  const uniskip_source_record rec = desc.source[source_id];
  const bf *base = reinterpret_cast<const bf *>(desc.tap_bases[rec.addr >> 7].base);
#pragma unroll
  for (u32 k = 0; k < ELEMENTS; ++k) {
    h[k] = load<bf, ld_modifier::ca>(base, uniskip_compact_element<G>(desc, rec, lane, k));
    lane.stage[lane.slot(k)] = h[k];
  }
  __syncwarp();
  uniskip_compact_chain<G>(lane.stage, lane.sched, threadIdx.x % 32);
#pragma unroll
  for (u32 k = 0; k < ELEMENTS; ++k)
    c[k] = lane.stage[lane.slot(k)];
  __syncwarp();
}

// An `e4` source runs the identical chain limb-sequentially, reusing the one staging
// buffer - which is what keeps shared memory independent of the field class.
template <u32 G>
DEVICE_FORCEINLINE void uniskip_compact_resolve(const uniskip_vm_desc &desc, const uniskip_compact_lane<G> &lane, const u16 source_id,
                                                e4 h[uniskip_compact_lane<G>::ELEMENTS], e4 c[uniskip_compact_lane<G>::ELEMENTS]) {
  constexpr u32 ELEMENTS = uniskip_compact_lane<G>::ELEMENTS;
  const uniskip_source_record rec = desc.source[source_id];
  const e4 *base = reinterpret_cast<const e4 *>(desc.tap_bases[rec.addr >> 7].base);
#pragma unroll
  for (u32 k = 0; k < ELEMENTS; ++k)
    h[k] = load<e4, ld_modifier::ca>(base, uniskip_compact_element<G>(desc, rec, lane, k));
  bf limbs[ELEMENTS][4];
#pragma unroll
  for (u32 l = 0; l < 4; ++l) {
#pragma unroll
    for (u32 k = 0; k < ELEMENTS; ++k)
      lane.stage[lane.slot(k)] = h[k].base_coefficient_from_flat_idx(l);
    __syncwarp();
    uniskip_compact_chain<G>(lane.stage, lane.sched, threadIdx.x % 32);
#pragma unroll
    for (u32 k = 0; k < ELEMENTS; ++k)
      limbs[k][l] = lane.stage[lane.slot(k)];
    __syncwarp();
  }
#pragma unroll
  for (u32 k = 0; k < ELEMENTS; ++k)
    c[k] = e4(limbs[k]);
}

// W = 0 duplicate rule, unchanged from R0: a repeated operand inside one term is produced
// once.
template <u32 G, typename T>
DEVICE_FORCEINLINE void uniskip_compact_resolve_second(const uniskip_vm_desc &desc, const uniskip_compact_lane<G> &lane, const uniskip_term term,
                                                       const T ah[uniskip_compact_lane<G>::ELEMENTS], const T ac[uniskip_compact_lane<G>::ELEMENTS],
                                                       T bh[uniskip_compact_lane<G>::ELEMENTS], T bc[uniskip_compact_lane<G>::ELEMENTS]) {
  constexpr u32 ELEMENTS = uniskip_compact_lane<G>::ELEMENTS;
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < ELEMENTS; ++k) {
      bh[k] = ah[k];
      bc[k] = ac[k];
    }
    return;
  }
  uniskip_compact_resolve<G>(desc, lane, term.source_b, bh, bc);
}

} // namespace airbender::gkr_uniskip_bench
