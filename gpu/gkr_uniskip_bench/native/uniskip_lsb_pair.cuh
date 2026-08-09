#pragma once

#include "uniskip_lsb.cuh"

// WINDOW DIAGNOSTICS, compile-gated. `AB_UNISKIP_WINDOW_DIAG` is never defined in a
// shipped build, so the emitted SASS is identical with and without this block; the Task 2
// gate checks exactly that. `ab_gkr_uniskip_chain_calls` counts chain EXECUTIONS once per
// warp (the chain's control flow is warp-uniform), which is the decisive proof that a
// reuse tag actually skips production. `ab_gkr_uniskip_poison_slots` corrupts a slot's
// RETAINED copy after the fill has already handed its own `c` back, so only a later reuse
// can see it.
#ifdef AB_UNISKIP_WINDOW_DIAG
#define AB_UNISKIP_WINDOW_DIAG_ON 1
#else
#define AB_UNISKIP_WINDOW_DIAG_ON 0
#endif

// Declared and defined ONLY in a diagnostic build; the Rust side is gated by the same
// switch (`cfg(window_diag)`), so a shipped binary carries neither the symbols nor a
// reference to them.
#if AB_UNISKIP_WINDOW_DIAG_ON
EXTERN __device__ unsigned long long ab_gkr_uniskip_chain_calls;
EXTERN __device__ __constant__ u32 ab_gkr_uniskip_poison_slots;
#endif

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
// The v3 R4 second block size (spec 3.5). Only the BLOCK shape changes: per-warp geometry,
// the lane map and the program walk are identical, so a 4-warp block covers 16 rows and
// the grid doubles.
constexpr u32 UNISKIP_PAIR_WARPS_128 = 4;
constexpr u32 UNISKIP_PAIR_ROWS_PER_BLOCK_128 = UNISKIP_PAIR_WARPS_128 * UNISKIP_PAIR_GROUPS_PER_WARP;
static_assert(UNISKIP_PAIR_ROWS_PER_BLOCK_128 == 16);
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

// The lane's two values through the chain.
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
#if AB_UNISKIP_WINDOW_DIAG_ON
  if ((threadIdx.x & 31) == 0)
    atomicAdd(&ab_gkr_uniskip_chain_calls, 1ull);
#endif
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

// Everything a lane needs. The eight twiddles are read from `__constant__` into
// registers at entry (a hot-path lane-indexed constant read serializes); ptxas
// rematerializes some of these loads inside the record loop under register pressure.
struct uniskip_pair_lane {
  u32 lane;  // 0..7 inside the group
  u32 group; // 0..3 inside the warp
  u64 row;
  bf tw[UNISKIP_PAIR_TWIDDLES];
};

// WARPS is the block's warp count; the default keeps every existing call site and its
// emitted SASS untouched, and 4 is the R4 128-thread baseline. It reaches only the row
// origin - a block covers WARPS * GROUPS_PER_WARP rows - never the lane map.
template <u32 WARPS = UNISKIP_WARPS_PER_BLOCK> DEVICE_FORCEINLINE uniskip_pair_lane uniskip_pair_lane_of(const u32 thread) {
  const u32 warp = thread / 32;
  const u32 id = thread % 32;
  uniskip_pair_lane out;
  out.lane = id & (UNISKIP_PAIR_LANES - 1);
  out.group = id / UNISKIP_PAIR_LANES;
  out.row = blockIdx.x * u64{WARPS * UNISKIP_PAIR_GROUPS_PER_WARP} + warp * UNISKIP_PAIR_GROUPS_PER_WARP + out.group;
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

// ---------------------------------------------------------------------------------------
// v3 R4 COSET CACHE. Per-thread local frame holding produced coset pairs for the admitted
// sources. `h[2]` is still loaded at every reference; only the chain is skipped.
// ---------------------------------------------------------------------------------------

// The frame. `u32` words rather than `bf` so every access states its WIDTH: a `bf` unit is
// one `uint2` (LDL.64/STL.64) and an `e4` span is two `uint4` (LDL.128/STL.128). A base is
// a multiple of four units for `e4`, i.e. a multiple of 32 B, so both halves are aligned.
struct alignas(16) uniskip_coset_cache {
  u32 word[2 * UNISKIP_COSET_FRAME_UNITS];
};
static_assert(sizeof(uniskip_coset_cache) == 736);
static_assert(alignof(uniskip_coset_cache) == 16);

DEVICE_FORCEINLINE void uniskip_coset_store(uniskip_coset_cache &cache, const u32 base, const bf c[2]) {
  *reinterpret_cast<uint2 *>(&cache.word[2 * base]) = make_uint2(bf::into_raw_u32(c[0]), bf::into_raw_u32(c[1]));
}

DEVICE_FORCEINLINE void uniskip_coset_load(const uniskip_coset_cache &cache, const u32 base, bf c[2]) {
  const uint2 v = *reinterpret_cast<const uint2 *>(&cache.word[2 * base]);
  c[0] = bf(v.x);
  c[1] = bf(v.y);
}

// c-object-major: `c[0]` occupies the span's first 16 B and `c[1]` the second. Limb-major
// would force a repack after the two loads - exactly the register motion this rung avoids.
DEVICE_FORCEINLINE uint4 uniskip_coset_pack(const e4 x) {
  uint4 v;
  v.x = bf::into_raw_u32(x.base_coefficient_from_flat_idx(0));
  v.y = bf::into_raw_u32(x.base_coefficient_from_flat_idx(1));
  v.z = bf::into_raw_u32(x.base_coefficient_from_flat_idx(2));
  v.w = bf::into_raw_u32(x.base_coefficient_from_flat_idx(3));
  return v;
}

DEVICE_FORCEINLINE e4 uniskip_coset_unpack(const uint4 v) {
  const bf limbs[4] = {bf(v.x), bf(v.y), bf(v.z), bf(v.w)};
  return e4(limbs);
}

DEVICE_FORCEINLINE void uniskip_coset_store(uniskip_coset_cache &cache, const u32 base, const e4 c[2]) {
  *reinterpret_cast<uint4 *>(&cache.word[2 * base]) = uniskip_coset_pack(c[0]);
  *reinterpret_cast<uint4 *>(&cache.word[2 * base + 4]) = uniskip_coset_pack(c[1]);
}

DEVICE_FORCEINLINE void uniskip_coset_load(const uniskip_coset_cache &cache, const u32 base, e4 c[2]) {
  c[0] = uniskip_coset_unpack(*reinterpret_cast<const uint4 *>(&cache.word[2 * base]));
  c[1] = uniskip_coset_unpack(*reinterpret_cast<const uint4 *>(&cache.word[2 * base + 4]));
}

// The H load alone. Same text as the control's first two lines, duplicated rather than
// extracted so that `uniskip_pair_resolve` - and with it the frozen control's SASS - is
// not touched. A cached reference still reloads H from `addr`; only `c` is retained.
DEVICE_FORCEINLINE void uniskip_pair_load_h(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id, bf h[2]) {
  const uniskip_source_record rec = desc.source[source_id];
  const bf *base = reinterpret_cast<const bf *>(desc.tap_bases[rec.addr >> 7].base);
  h[0] = load<bf, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 0));
  h[1] = load<bf, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 1));
}

DEVICE_FORCEINLINE void uniskip_pair_load_h(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id, e4 h[2]) {
  const uniskip_source_record rec = desc.source[source_id];
  const e4 *base = reinterpret_cast<const e4 *>(desc.tap_bases[rec.addr >> 7].base);
  h[0] = load<e4, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 0));
  h[1] = load<e4, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 1));
}

// The prologue: produce each admitted source once into this thread's frame, in the order
// the HOST emitted the table. The store happens ONCE after the resolver returns, never per
// limb - the e4 resolver only has `c[0]`/`c[1]` complete at that point.
//
// ONE walking loop with a class branch, not two typed loops. The class branch is
// warp-uniform (every thread walks the same rows), and this is what makes PRODUCTION ORDER
// a host-side property: the alternate BF-first variant is a different upload of the same
// table, not a second kernel. Two typed loops would pin the class order in the kernel text
// and the diagnostic would need its own SASS body. Both bodies appear once either way.
DEVICE_FORCEINLINE void uniskip_coset_prologue(const uniskip_vm_desc &desc, const uniskip_cache_desc &plan, const uniskip_pair_lane &lane,
                                               uniskip_coset_cache &cache) {
  for (u32 i = 0; i < plan.count; ++i) {
    const uniskip_prologue_entry row = plan.entry[i];
    if (desc.source[row.source].source_class == UNISKIP_SRC_E4_GLOBAL) {
      e4 h[2], c[2];
      uniskip_pair_resolve(desc, lane, row.source, h, c);
      uniskip_coset_store(cache, row.base, c);
    } else {
      bf h[2], c[2];
      uniskip_pair_resolve(desc, lane, row.source, h, c);
      uniskip_coset_store(cache, row.base, c);
    }
  }
}

// The cached resolve. `h` is loaded exactly as the control loads it; only `c` changes
// provenance. Admission is source-global, so the disposition rides the record byte the
// resolver already fetches - there is no per-record tag and no two-operand problem.
template <typename T>
DEVICE_FORCEINLINE void uniskip_pair_resolve_cached(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id,
                                                    const uniskip_coset_cache &cache, T h[2], T c[2]) {
  const u32 base = desc.source[source_id].cache_slot;
  if (base == UNISKIP_CACHE_SLOT_NONE) {
    uniskip_pair_resolve(desc, lane, source_id, h, c);
    return;
  }
  uniskip_pair_load_h(desc, lane, source_id, h);
  uniskip_coset_load(cache, base, c);
}

// W = 0 duplicate rule under the cache: a repeated operand inside one term still resolves
// once, so a self-product performs no second load and no second chain.
template <typename T>
DEVICE_FORCEINLINE void uniskip_pair_resolve_second_cached(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_term term,
                                                           const uniskip_coset_cache &cache, const T ah[2], const T ac[2], T bh[2], T bc[2]) {
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      bh[k] = ah[k];
      bc[k] = ac[k];
    }
    return;
  }
  uniskip_pair_resolve_cached(desc, lane, term.source_b, cache, bh, bc);
}

// ---------------------------------------------------------------------------------------
// v3 R3 WINDOW. Coset-only: a slot retains one BF source's produced `c[2]` (2 regs/lane);
// `h[2]` is still loaded on reuse. A reuse therefore skips exactly the shuffle-NTT chain
// and its twist for that operand resolution, which is the whole saving.
// ---------------------------------------------------------------------------------------

// Tag nibble decode. Encoding is `src/window.rs::WindowTag::encode`: 0 = none,
// 1 + slot = fill, 1 + SLOTS + slot = reuse. With SLOTS a power of two the slot number is
// `(n - 1) & (SLOTS - 1)` for both kinds.
DEVICE_FORCEINLINE u32 uniskip_win_tag_a(const u8 byte) { return byte & 0xf; }
DEVICE_FORCEINLINE u32 uniskip_win_tag_b(const u8 byte) { return byte >> 4; }
DEVICE_FORCEINLINE bool uniskip_win_is_fill(const u32 tag) { return tag != 0 && tag <= UNISKIP_WINDOW_SLOTS; }
DEVICE_FORCEINLINE bool uniskip_win_is_reuse(const u32 tag) { return tag > UNISKIP_WINDOW_SLOTS; }
DEVICE_FORCEINLINE u32 uniskip_win_slot(const u32 tag) { return (tag - 1) & (UNISKIP_WINDOW_SLOTS - 1); }

// NAMED SLOT REGISTERS. Eight `bf` members, never an indexable array: a register array
// under a runtime index becomes local memory. The slot number is warp-uniform (it comes
// from a record's tag and `pc` is warp-uniform), so the switch is uniform control flow and
// each case is a literal member reference.
struct uniskip_win_slots {
  bf lo0, hi0, lo1, hi1, lo2, hi2, lo3, hi3;
};

DEVICE_FORCEINLINE void uniskip_win_store(uniskip_win_slots &s, const u32 slot, bf lo, bf hi) {
#if AB_UNISKIP_WINDOW_DIAG_ON
  if (ab_gkr_uniskip_poison_slots) {
    lo = bf::add(lo, bf::ONE());
    hi = bf::add(hi, bf::ONE());
  }
#endif
  switch (slot) {
  case 0:
    s.lo0 = lo;
    s.hi0 = hi;
    break;
  case 1:
    s.lo1 = lo;
    s.hi1 = hi;
    break;
  case 2:
    s.lo2 = lo;
    s.hi2 = hi;
    break;
  default:
    s.lo3 = lo;
    s.hi3 = hi;
    break;
  }
}

DEVICE_FORCEINLINE void uniskip_win_load(const uniskip_win_slots &s, const u32 slot, bf &lo, bf &hi) {
  switch (slot) {
  case 0:
    lo = s.lo0;
    hi = s.hi0;
    break;
  case 1:
    lo = s.lo1;
    hi = s.hi1;
    break;
  case 2:
    lo = s.lo2;
    hi = s.hi2;
    break;
  default:
    lo = s.lo3;
    hi = s.hi3;
    break;
  }
}

// The windowed `bf` resolve. `h` is always loaded. On reuse the chain is skipped entirely
// and `c` comes from the slot; otherwise the chain runs ONCE — before the store switch, so
// no slot case carries a copy of it — and a fill hands `c` to the slot.
//
// The fill store happens HERE, inside the resolve, which is what keeps it correct for
// group members: a grouped `PRODUCT_BF_BF` multiplies `ac[k]` in place after both operands
// resolve, so a slot captured any later would retain the product instead of the operand.
DEVICE_FORCEINLINE void uniskip_pair_resolve_win(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id, const u32 tag,
                                                 uniskip_win_slots &slots, bf h[2], bf c[2]) {
  const uniskip_source_record rec = desc.source[source_id];
  const bf *base = reinterpret_cast<const bf *>(desc.tap_bases[rec.addr >> 7].base);
  h[0] = load<bf, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 0));
  h[1] = load<bf, ld_modifier::ca>(base, uniskip_pair_offset(desc, rec, lane, 1));
  if (uniskip_win_is_reuse(tag)) {
    uniskip_win_load(slots, uniskip_win_slot(tag), c[0], c[1]);
    return;
  }
  uniskip_pair_regs x{h[0], h[1]};
  uniskip_pair_chain(x, lane.lane, lane.tw);
  c[0] = x.lo;
  c[1] = x.hi;
  if (uniskip_win_is_fill(tag))
    uniskip_win_store(slots, uniskip_win_slot(tag), c[0], c[1]);
}

// Operand B under the window. A self-product performs no second access, so Task 0 leaves
// its B tag `none` and this never runs for one.
DEVICE_FORCEINLINE void uniskip_pair_resolve_second_win(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_term term, const u32 tag,
                                                        uniskip_win_slots &slots, const bf ah[2], const bf ac[2], bf bh[2], bf bc[2]) {
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k) {
      bh[k] = ah[k];
      bc[k] = ac[k];
    }
    return;
  }
  uniskip_pair_resolve_win(desc, lane, term.source_b, tag, slots, bh, bc);
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
