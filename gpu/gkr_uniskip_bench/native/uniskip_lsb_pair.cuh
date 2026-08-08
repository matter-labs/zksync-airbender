#pragma once

#include "uniskip_lsb.cuh"

namespace airbender::gkr_uniskip_bench {

// v3 R2 GEOMETRY: PAIR-RESIDENT radix-2. R0 binds lane = tap, so a butterfly's two halves
// sit in different lanes and the stage must be written as a select plus an UNCONDITIONAL
// multiply - unity on half the lanes, unskippable because the halves are lane-divergent.
// Put the pair in one lane and the stage becomes `lo = u + v; hi = (u - v) * w`: the low
// output's unity multiply never exists in the code, at every stage, with no shared memory
// and no schedule table.
//
// A group's 16 taps live on 8 lanes, two per lane; a warp holds 4 groups, so a block of
// 256 threads covers 32 logical rows - twice R0's decode amortization, free. Lane l of a
// group owns taps l and l + 8 on the way in, and (because the chain ends on the map it
// started on) coset cells l and l + 8 on the way out, so H and the coset share one layout.
// Derivation, re-pair masks and the host executor: `src/pair.rs`.
constexpr u32 UNISKIP_PAIR_LANES = UNISKIP_TAPS / 2;
constexpr u32 UNISKIP_PAIR_GROUPS_PER_WARP = 32 / UNISKIP_PAIR_LANES;
constexpr u32 UNISKIP_PAIR_ROWS_PER_BLOCK = UNISKIP_WARPS_PER_BLOCK * UNISKIP_PAIR_GROUPS_PER_WARP;
constexpr u32 UNISKIP_PAIR_TWIDDLES = 8; // six stage twiddles + two twist values
static_assert(UNISKIP_PAIR_LANES == 8);
static_assert(UNISKIP_PAIR_GROUPS_PER_WARP == 4);
static_assert(UNISKIP_PAIR_ROWS_PER_BLOCK == 32);

struct uniskip_pair_desc : uniskip_vm_desc {};
static_assert(sizeof(uniskip_pair_desc) == sizeof(uniskip_vm_desc));
static_assert(offsetof(uniskip_pair_desc, eq_sizes) == 2492);

// Element index of (lane, slot) while the chain pairs on `bit`: the lane supplies every
// tap bit except `bit`, the slot supplies `bit`.
DEVICE_FORCEINLINE u32 uniskip_pair_element(const u32 lane, const u32 bit, const u32 slot) {
  return ((lane >> bit) << (bit + 1)) | (slot << bit) | (lane & ((1u << bit) - 1));
}

// The lane's two values through the chain. `p` caches which side of each re-pair this lane
// is on; the masks are compile-time so `p` costs one AND per stage, not a lookup.
struct uniskip_pair_regs {
  bf lo;
  bf hi;
};

// RE-PAIR. Each lane keeps one output and trades the other with `lane ^ MASK`: one
// `shfl_xor` for a whole pair, against R0's one partner-fetch per element per stage.
// Both sides run the same three selects; `MASK` is a template argument so the predicate
// folds.
template <u32 MASK> DEVICE_FORCEINLINE void uniskip_pair_repair(uniskip_pair_regs &x, const u32 lane) {
  const bool high = (lane & MASK) != 0;
  const bf sent = high ? x.lo : x.hi;
  const bf recv = bf::from_reduced_raw_repr(shfl_xor(0xffffffffu, bf::into_raw_u32(sent), static_cast<int>(MASK)));
  x.lo = high ? recv : x.lo;
  x.hi = high ? x.hi : recv;
}

// THE THREE STAGE SHAPES. Note what is absent: no select on the butterfly, and no multiply
// at all on the low output.
DEVICE_FORCEINLINE void uniskip_pair_dif(uniskip_pair_regs &x, const bf tw) {
  const bf u = x.lo, v = x.hi;
  x.lo = bf::add(u, v);
  x.hi = bf::mul(bf::sub(u, v), tw);
}

DEVICE_FORCEINLINE void uniskip_pair_plain(uniskip_pair_regs &x) {
  const bf u = x.lo, v = x.hi;
  x.lo = bf::add(u, v);
  x.hi = bf::sub(u, v);
}

DEVICE_FORCEINLINE void uniskip_pair_dit(uniskip_pair_regs &x, const bf tw) {
  const bf u = x.lo, v = bf::mul(x.hi, tw);
  x.lo = bf::add(u, v);
  x.hi = bf::sub(u, v);
}

// THE PRODUCER. Six twiddled butterfly stages at one multiply per lane, two distance-1
// stages at none, and a twist at two - 6 * 8 + 16 = 64 issued multiplies per group against
// R0's 7 * 16 = 112. Six re-pair shuffles against R0's eight partner-fetches, and each
// serves a pair rather than an element.
DEVICE_FORCEINLINE void uniskip_pair_chain(uniskip_pair_regs &x, const u32 lane, const bf tw[UNISKIP_PAIR_TWIDDLES]) {
  uniskip_pair_dif(x, tw[0]); // bit 3
  uniskip_pair_repair<4>(x, lane);
  uniskip_pair_dif(x, tw[1]); // bit 2
  uniskip_pair_repair<2>(x, lane);
  uniskip_pair_dif(x, tw[2]); // bit 1
  uniskip_pair_repair<1>(x, lane);
  uniskip_pair_plain(x); // bit 0, twiddle unity everywhere
  x.lo = bf::mul(x.lo, tw[3]);
  x.hi = bf::mul(x.hi, tw[4]);
  uniskip_pair_plain(x); // bit 0 again, still unity
  uniskip_pair_repair<1>(x, lane);
  uniskip_pair_dit(x, tw[5]); // bit 1
  uniskip_pair_repair<2>(x, lane);
  uniskip_pair_dit(x, tw[6]); // bit 2
  uniskip_pair_repair<4>(x, lane);
  uniskip_pair_dit(x, tw[7]); // bit 3
}

// Everything a lane needs. The eight twiddles are read from `__constant__` ONCE at entry
// into registers - a hot-path lane-indexed constant read serializes.
struct uniskip_pair_lane {
  u32 lane;  // 0..7 inside the group
  u32 group; // 0..3 inside the warp
  u64 row;
  bf tw[UNISKIP_PAIR_TWIDDLES];
};

DEVICE_FORCEINLINE uniskip_pair_lane uniskip_pair_lane_of(const u32 thread) {
  const u32 warp = thread / 32;
  const u32 id = thread % 32;
  uniskip_pair_lane out;
  out.lane = id & (UNISKIP_PAIR_LANES - 1);
  out.group = id / UNISKIP_PAIR_LANES;
  out.row = blockIdx.x * u64{UNISKIP_PAIR_ROWS_PER_BLOCK} + warp * UNISKIP_PAIR_GROUPS_PER_WARP + out.group;
  const u32 bits[6] = {3, 2, 1, 1, 2, 3};
  const u32 tables[6] = {0, 1, 2, 4, 5, 6};
  u32 at = 0;
#pragma unroll
  for (u32 s = 0; s < 3; ++s)
    out.tw[at++] = ab_gkr_uniskip_ntt_twiddles[tables[s] * UNISKIP_TAPS + uniskip_pair_element(out.lane, bits[s], 1)];
  out.tw[at++] = ab_gkr_uniskip_ntt_twiddles[3 * UNISKIP_TAPS + uniskip_pair_element(out.lane, 0, 0)];
  out.tw[at++] = ab_gkr_uniskip_ntt_twiddles[3 * UNISKIP_TAPS + uniskip_pair_element(out.lane, 0, 1)];
#pragma unroll
  for (u32 s = 3; s < 6; ++s)
    out.tw[at++] = ab_gkr_uniskip_ntt_twiddles[tables[s] * UNISKIP_TAPS + uniskip_pair_element(out.lane, bits[s], 1)];
  return out;
}

// Element index of the lane's slot-`s` tap. For a fixed slot the warp reads four runs of
// eight consecutive elements - one per group - each 32 B aligned for `bf` and 128 B for
// `e4`, so both are at the minimum sector count.
DEVICE_FORCEINLINE size_t uniskip_pair_offset(const uniskip_vm_desc &desc, const uniskip_source_record rec, const uniskip_pair_lane &lane, const u32 slot) {
  const size_t column = rec.addr & 0x7f;
  return (((column << desc.log_rows) + lane.row) << UNISKIP_LOG_TAPS) + uniskip_pair_element(lane.lane, 3, slot);
}

// H is the loaded value and never enters the chain's working registers, so the transform
// runs in place on its own copy.
DEVICE_FORCEINLINE void uniskip_pair_resolve(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id, bf h[2], bf c[2]) {
  const uniskip_source_record rec = desc.source[source_id];
  const bf *base = reinterpret_cast<const bf *>(desc.tap_bases[rec.addr >> 7].base);
  h[0] = load<bf, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 0));
  h[1] = load<bf, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 1));
  uniskip_pair_regs x{h[0], h[1]};
  uniskip_pair_chain(x, lane.lane, lane.tw);
  c[0] = x.lo;
  c[1] = x.hi;
}

// An `e4` source runs the identical chain limb-sequentially off its two loaded elements.
DEVICE_FORCEINLINE void uniskip_pair_resolve(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id, e4 h[2], e4 c[2]) {
  const uniskip_source_record rec = desc.source[source_id];
  const e4 *base = reinterpret_cast<const e4 *>(desc.tap_bases[rec.addr >> 7].base);
  h[0] = load<e4, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 0));
  h[1] = load<e4, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 1));
  bf limbs[2][4];
#pragma unroll
  for (u32 l = 0; l < 4; ++l) {
    uniskip_pair_regs x{h[0].base_coefficient_from_flat_idx(l), h[1].base_coefficient_from_flat_idx(l)};
    uniskip_pair_chain(x, lane.lane, lane.tw);
    limbs[0][l] = x.lo;
    limbs[1][l] = x.hi;
  }
  c[0] = e4(limbs[0]);
  c[1] = e4(limbs[1]);
}

// W = 0 duplicate rule, unchanged: a repeated operand inside one term is produced once.
template <typename T>
DEVICE_FORCEINLINE void uniskip_pair_resolve_second(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_term term, const T ah[2],
                                                    const T ac[2], T bh[2], T bc[2]) {
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      bh[k] = ah[k];
      bc[k] = ac[k];
    }
    return;
  }
  uniskip_pair_resolve(desc, lane, term.source_b, bh, bc);
}

} // namespace airbender::gkr_uniskip_bench
