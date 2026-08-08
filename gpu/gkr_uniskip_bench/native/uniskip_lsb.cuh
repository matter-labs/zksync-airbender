#pragma once

#include "uniskip_abi.cuh"

namespace airbender::gkr_uniskip_bench {

// v3 R0 GEOMETRY. The v1/v2 kernels put lane = row and made a warp own four of the 32
// cells; this one inverts both the layout and the assignment. A GROUP is the 16
// adjacent elements of one logical row of one column - the evaluations of one
// degree-<=15 polynomial on H - and a 16-lane half-warp owns one group with lane = tap.
// Lane t therefore owns TWO cells of its group: H cell t (the tap it loaded) and coset
// cell UNISKIP_TAPS + t (produced). Two groups per warp, eight warps per block, so a
// block covers UNISKIP_LSB_ROWS_PER_BLOCK logical rows and the grid is rows / 16.
constexpr u32 UNISKIP_LOG_TAPS = 4;
constexpr u32 UNISKIP_LSB_GROUPS_PER_WARP = 32 / UNISKIP_TAPS;
constexpr u32 UNISKIP_LSB_ROWS_PER_BLOCK = UNISKIP_WARPS_PER_BLOCK * UNISKIP_LSB_GROUPS_PER_WARP;
static_assert((1u << UNISKIP_LOG_TAPS) == UNISKIP_TAPS);
static_assert(UNISKIP_LSB_GROUPS_PER_WARP == 2, "a warp holds exactly two 16-lane groups");
static_assert(UNISKIP_LSB_ROWS_PER_BLOCK == 16);

// Lane-indexed twiddle tables of the FACTORIZED coset transform, in stage order:
// 0..2 = iDIF with omega^-1 at butterfly distance 8 / 4 / 2, 3 = the folded
// normalize+twist inv16 * gamma^bitrev(lane), 4..6 = DIT with omega at distance 2 / 4 / 8.
// The two distance-1 stages carry only unity (exponent 0 * 8) and are elided on both
// sides, which is why 8 exchange stages need 7 tables. Host mirror and derivation:
// `src/domain.rs::ntt_twiddles`, pinned against the dense 16x16 apply by
// `cpu_factorized_coset_matches_matrix`.
constexpr u32 UNISKIP_NTT_TABLES = 7;

} // namespace airbender::gkr_uniskip_bench

EXTERN __device__ __constant__ bf ab_gkr_uniskip_ntt_twiddles[airbender::gkr_uniskip_bench::UNISKIP_NTT_TABLES * airbender::gkr_uniskip_bench::UNISKIP_TAPS];

namespace airbender::gkr_uniskip_bench {

// KERNEL-ENTRY TYPE TAG, the fourth empty derived class of `uniskip_vm_desc`: same
// members, same 2512-byte `__grid_constant__` parameter, shared host wire. Unlike the
// v1/v2 selectors it re-binds no overload - every helper below takes
// `uniskip_vm_desc &` - it only names the LSB ordering at the entry point and carries
// the layout `static_assert`s. The mode reads `tap_bases` alone; there is no coset
// allocation to point at.
struct uniskip_lsb_desc : uniskip_vm_desc {};
static_assert(sizeof(uniskip_lsb_desc) == sizeof(uniskip_vm_desc));
static_assert(alignof(uniskip_lsb_desc) == alignof(uniskip_vm_desc));
static_assert(offsetof(uniskip_lsb_desc, eq_sizes) == 2492);

// Everything a lane needs to resolve any source: its tap, its group's logical row, and
// the seven twiddles it will multiply by. The twiddles are read from `__constant__` ONCE
// per thread into registers - the tables are lane-indexed, so a hot-path read would be a
// 16-way divergent constant access on every stage of every reference.
struct uniskip_lsb_lane {
  u32 tap;
  u64 group;
  bf tw[UNISKIP_NTT_TABLES];
};

DEVICE_FORCEINLINE uniskip_lsb_lane uniskip_lsb_lane_of(const u32 thread) {
  const u32 warp = thread / 32;
  const u32 lane = thread % 32;
  uniskip_lsb_lane out;
  out.tap = lane & (UNISKIP_TAPS - 1);
  out.group = blockIdx.x * u64{UNISKIP_LSB_ROWS_PER_BLOCK} + warp * UNISKIP_LSB_GROUPS_PER_WARP + (lane >> UNISKIP_LOG_TAPS);
#pragma unroll
  for (u32 s = 0; s < UNISKIP_NTT_TABLES; ++s)
    out.tw[s] = ab_gkr_uniskip_ntt_twiddles[s * UNISKIP_TAPS + out.tap];
  return out;
}

// One radix-2 butterfly layer at distance `d` inside the 16-lane group: the upper lane
// of a pair keeps u + v, the lower u - v. `d <= 8` and groups are 16-lane aligned, so
// `lane ^ d` never leaves the group and the full-warp shuffle is the segment shuffle.
DEVICE_FORCEINLINE bf uniskip_lsb_butterfly(const bf v, const int d, const bool lower) {
  const bf partner = bf::from_reduced_raw_repr(shfl_xor(0xffffffffu, bf::into_raw_u32(v), d));
  return lower ? bf::sub(partner, v) : bf::add(v, partner);
}

// THE PRODUCER. Lane `tap` holds P(omega^tap); the half-warp exchanges through the
// pinned chain - iDIF with omega^-1 -> bit-reversed coefficients -> folded
// normalize+twist -> DIT with omega - and lane `tap` ends holding P(gamma * omega^tap),
// which is coset cell UNISKIP_TAPS + tap. Natural order in, natural order out: the
// transform terminates directly in the consumption map, so term execution never sees the
// producer's internals.
//
// 8 exchange stages and 7 generic multiplies per component pass (the two distance-1
// stages are unity). Adds and subtracts stay canonical - `bf::add`/`bf::sub` are one
// conditional subtract each, not a lazy widening - so the only reduction chain is the
// one inside `bf::mul`, and no accumulator ever exceeds `red`'s p*2^32 range.
DEVICE_FORCEINLINE bf uniskip_lsb_coset(bf v, const u32 tap, const bf tw[UNISKIP_NTT_TABLES]) {
#pragma unroll
  for (u32 s = 0; s < 3; ++s) {
    const u32 d = UNISKIP_TAPS >> (s + 1); // 8, 4, 2
    v = uniskip_lsb_butterfly(v, static_cast<int>(d), (tap & d) != 0);
    v = bf::mul(v, tw[s]);
  }
  v = uniskip_lsb_butterfly(v, 1, (tap & 1) != 0);
  v = bf::mul(v, tw[3]);
  v = uniskip_lsb_butterfly(v, 1, (tap & 1) != 0);
#pragma unroll
  for (u32 s = 0; s < 3; ++s) {
    const u32 d = 2u << s; // 2, 4, 8
    v = bf::mul(v, tw[UNISKIP_NTT_TABLES - 3 + s]);
    v = uniskip_lsb_butterfly(v, static_cast<int>(d), (tap & d) != 0);
  }
  return v;
}

// THE ACCESSOR, W = 0: one coalesced group load per reference, then the transform.
// Element offset is `column * (16 << log_rows) + (group << 4) + tap`, so a `bf` group is
// one 64 B run (lane issues a u32) and an `e4` group one 256 B run (lane issues one
// v4.u32; e4 is align-16 and the window base is 16 B aligned). The `H` cell is the loaded
// value itself - there is no separate tap read anywhere in this mode.
DEVICE_FORCEINLINE size_t uniskip_lsb_element(const uniskip_vm_desc &desc, const uniskip_source_record rec, const uniskip_lsb_lane &lane) {
  const size_t column = rec.addr & 0x7f; // widen BEFORE the shift
  return (((column << desc.log_rows) + lane.group) << UNISKIP_LOG_TAPS) + lane.tap;
}

DEVICE_FORCEINLINE void uniskip_lsb_resolve(const uniskip_vm_desc &desc, const uniskip_lsb_lane &lane, const u16 source_id, bf &h, bf &c) {
  const uniskip_source_record rec = desc.source[source_id];
  const bf *base = reinterpret_cast<const bf *>(desc.tap_bases[rec.addr >> 7].base);
  h = load<bf, ld_modifier::ca>(base, uniskip_lsb_element(desc, rec, lane));
  c = uniskip_lsb_coset(h, lane.tap, lane.tw);
}

// An `e4` source runs the IDENTICAL producer limb-sequentially: the lane's one v4 load
// parks four limbs, pass l transforms limb l, and every exchange is still 4 B. No wide
// shuffles, no transposes, no per-class producer code.
DEVICE_FORCEINLINE void uniskip_lsb_resolve(const uniskip_vm_desc &desc, const uniskip_lsb_lane &lane, const u16 source_id, e4 &h, e4 &c) {
  const uniskip_source_record rec = desc.source[source_id];
  const e4 *base = reinterpret_cast<const e4 *>(desc.tap_bases[rec.addr >> 7].base);
  h = load<e4, ld_modifier::ca>(base, uniskip_lsb_element(desc, rec, lane));
  bf limbs[4];
#pragma unroll
  for (u32 l = 0; l < 4; ++l)
    limbs[l] = uniskip_lsb_coset(h.base_coefficient_from_flat_idx(l), lane.tap, lane.tw);
  c = e4(limbs);
}

// W = 0 DUPLICATE RULE (spec 2.5): nothing is retained across references, but a repeated
// operand INSIDE one term is produced once - `x * x` costs one transform, not two.
template <typename T>
DEVICE_FORCEINLINE void uniskip_lsb_resolve_second(const uniskip_vm_desc &desc, const uniskip_lsb_lane &lane, const uniskip_term term, const T ah, const T ac,
                                                   T &bh, T &bc) {
  if (term.source_b == term.source_a) {
    bh = ah;
    bc = ac;
    return;
  }
  uniskip_lsb_resolve(desc, lane, term.source_b, bh, bc);
}

// eq and the e4 warp exchange, spelled here rather than shared with `uniskip.cu`: the v2
// kernels' copies are `DEVICE_FORCEINLINE` in that translation unit, and this rung must
// leave them byte-for-byte alone. The `q` oracle composes eq the same way, so a drift
// between the two shows up as a validation failure, not as a silent divergence.
DEVICE_FORCEINLINE e4 uniskip_lsb_eq_at(const uniskip_vm_desc &desc, const u32 row) {
  const u32 low_bits = desc.eq_sizes.low;
  const u32 high1_bits = desc.eq_sizes.high[1];
  const u32 low = row & ((1u << low_bits) - 1);
  const u32 high1 = (row >> low_bits) & ((1u << high1_bits) - 1);
  const u32 high0 = row >> (low_bits + high1_bits);
  const e4 high = e4::mul(ab_gkr_uniskip_eq_high[high0], ab_gkr_uniskip_eq_high[UNISKIP_EQ_HIGH + high1]);
  return e4::mul(high, load<e4, ld_modifier::ca>(desc.eq_low, low));
}

DEVICE_FORCEINLINE e4 uniskip_lsb_shfl_xor_e4(const e4 value, const int lane_mask) {
  static_assert(sizeof(e4) == sizeof(uint4));
  e4 result;
  *reinterpret_cast<uint4 *>(&result) = shfl_xor(0xffffffffu, *reinterpret_cast<const uint4 *>(&value), lane_mask);
  return result;
}

} // namespace airbender::gkr_uniskip_bench
