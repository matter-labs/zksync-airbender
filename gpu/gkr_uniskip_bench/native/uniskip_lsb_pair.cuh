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
  uint2 v = make_uint2(bf::into_raw_u32(c[0]), bf::into_raw_u32(c[1]));
#if AB_UNISKIP_WINDOW_DIAG_ON
  // POISON HOOK, diagnostic builds only: corrupt what the prologue stored so any later
  // cached READ must change `q`. A cached arm that does not diverge under this is not
  // reading the frame it filled.
  if (ab_gkr_uniskip_poison_slots) {
    v.x = bf::into_raw_u32(bf::add(c[0], bf::ONE()));
    v.y = bf::into_raw_u32(bf::add(c[1], bf::ONE()));
  }
#endif
  *reinterpret_cast<uint2 *>(&cache.word[2 * base]) = v;
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
  uint4 lo = uniskip_coset_pack(c[0]);
  uint4 hi = uniskip_coset_pack(c[1]);
#if AB_UNISKIP_WINDOW_DIAG_ON
  if (ab_gkr_uniskip_poison_slots) {
    lo.x = bf::into_raw_u32(bf::add(bf(lo.x), bf::ONE()));
    hi.x = bf::into_raw_u32(bf::add(bf(hi.x), bf::ONE()));
  }
#endif
  *reinterpret_cast<uint4 *>(&cache.word[2 * base]) = lo;
  *reinterpret_cast<uint4 *>(&cache.word[2 * base + 4]) = hi;
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
  // WATCH ITEM (no change needed today): the uncached leg re-fetches `desc.source[id]`
  // inside `uniskip_pair_resolve`, so an uncached reference reads the record TWICE. ptxas
  // is free to CSE it and the record is a constant-bank read either way, but `cache0` -
  // whose every reference takes this leg - is the arm that would show it if ptxas does not.
  // Read cache0's LDC delta against control before attributing its cost to the frame.
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
// v3 R9 GATE-FIRST REORDER. The cached resolve above fills `h[2]` AND `c[2]` before the
// gate, so both domains of both operands are live at every multiply. These helpers split
// that into two halves of one program walk: load H, gate on H, then turn THAT storage into
// C (chain in place, or a cache load for an admitted source) and gate on C. Nothing about
// what an accumulator sees changes - only the interleaving between `acc_h` and `acc_c`.
// ---------------------------------------------------------------------------------------

// The chain, run destructively over the operand's own storage: `v` enters as H and leaves
// as C. Identical text to the control resolve's transform, so the produced `c` is bit-equal.
DEVICE_FORCEINLINE void uniskip_pair_chain_reorder(const uniskip_pair_lane &lane, bf v[2]) {
  uniskip_pair_regs x{v[0], v[1]};
  uniskip_pair_chain(x, lane.lane, lane.tw);
  v[0] = x.lo;
  v[1] = x.hi;
}

// The `e4` counterpart: all eight limbs are read into the chain before either output is
// written back, so the in-place form cannot clobber a limb it still needs.
DEVICE_FORCEINLINE void uniskip_pair_chain_reorder(const uniskip_pair_lane &lane, e4 v[2]) {
  bf limbs[2][4];
#pragma unroll
  for (u32 l = 0; l < 4; ++l) {
    uniskip_pair_regs x{v[0].base_coefficient_from_flat_idx(l), v[1].base_coefficient_from_flat_idx(l)};
    uniskip_pair_chain(x, lane.lane, lane.tw);
    limbs[0][l] = x.lo;
    limbs[1][l] = x.hi;
  }
  v[0] = e4(limbs[0]);
  v[1] = e4(limbs[1]);
}

// H -> C for one factor. An admitted source replaces the chain with its frame load; an
// uncached one chains in place. Same disposition byte the cached resolve reads.
template <typename T>
DEVICE_FORCEINLINE void uniskip_pair_coset_reorder(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const u16 source_id,
                                                   const uniskip_coset_cache &cache, T v[2]) {
  const u32 base = desc.source[source_id].cache_slot;
  if (base == UNISKIP_CACHE_SLOT_NONE) {
    uniskip_pair_chain_reorder(lane, v);
    return;
  }
  uniskip_coset_load(cache, base, v);
}

// Operand B's H. The W = 0 duplicate rule transfers: a self-product copies A's H and
// performs no second load.
template <typename T>
DEVICE_FORCEINLINE void uniskip_pair_load_h_second_reorder(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_term term, const T a[2],
                                                           T b[2]) {
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      b[k] = a[k];
    return;
  }
  uniskip_pair_load_h(desc, lane, term.source_b, b);
}

// Operand B's H -> C, taking A's ALREADY promoted storage: a self-product copies A's `c`
// and performs no second chain, which is the duplicate rule's other half.
template <typename T>
DEVICE_FORCEINLINE void uniskip_pair_coset_second_reorder(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_term term,
                                                          const uniskip_coset_cache &cache, const T a[2], T b[2]) {
  if (term.source_b == term.source_a) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      b[k] = a[k];
    return;
  }
  uniskip_pair_coset_reorder(desc, lane, term.source_b, cache, b);
}

// One group member's contribution to ONE sum. Extracted rather than duplicated per domain
// so the immediate / add / sub / FMA order is the control's by construction, twice.
DEVICE_FORCEINLINE void uniskip_pair_group_sum_reorder(const uniskip_vm_desc &desc, const uniskip_term member, const bf v[2], bf sum[2]) {
  if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      sum[k] = bf::add(sum[k], v[k]);
  } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      sum[k] = bf::sub(sum[k], v[k]);
  } else {
    const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      sum[k] = bf::fma(immediate, v[k], sum[k]);
  }
}

// ---------------------------------------------------------------------------------------
// v3 R9b GROUPED-PATH DECODE. The R9 dispatch above runs once per accumulator, so a member's
// coefficient is re-tested and its immediate re-loaded on the second visit. These helpers
// resolve it ONCE per member into a kind plus the immediate; the apply then selects the same
// add / sub / FMA in the same order, twice. The `uniskip_term` form is R9's dispatch, kept so
// the same body can be built with the hoist off.
// ---------------------------------------------------------------------------------------

constexpr u32 UNISKIP_PAIR_COEFF_ONE = 0;
constexpr u32 UNISKIP_PAIR_COEFF_NEG_ONE = 1;
constexpr u32 UNISKIP_PAIR_COEFF_IMMEDIATE = 2;

struct uniskip_pair_coeff_reorder {
  bf immediate;
  u32 kind;
};

// The immediate is read only on the leg that has one: `member.coeff - RESERVED` underflows
// for the one / minus-one cases.
DEVICE_FORCEINLINE uniskip_pair_coeff_reorder uniskip_pair_coeff_decode_reorder(const uniskip_vm_desc &desc, const uniskip_term member) {
  uniskip_pair_coeff_reorder out;
  if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
    out.kind = UNISKIP_PAIR_COEFF_ONE;
    out.immediate = bf::ZERO();
  } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
    out.kind = UNISKIP_PAIR_COEFF_NEG_ONE;
    out.immediate = bf::ZERO();
  } else {
    out.kind = UNISKIP_PAIR_COEFF_IMMEDIATE;
    out.immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
  }
  return out;
}

DEVICE_FORCEINLINE void uniskip_pair_group_sum_decoded_reorder(const uniskip_pair_coeff_reorder coeff, const bf v[2], bf sum[2]) {
  if (coeff.kind == UNISKIP_PAIR_COEFF_ONE) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      sum[k] = bf::add(sum[k], v[k]);
  } else if (coeff.kind == UNISKIP_PAIR_COEFF_NEG_ONE) {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      sum[k] = bf::sub(sum[k], v[k]);
  } else {
#pragma unroll
    for (u32 k = 0; k < 2; ++k)
      sum[k] = bf::fma(coeff.immediate, v[k], sum[k]);
  }
}

// The apply with its case chosen at COMPILE time, and its value taken BY VALUE so a product can
// be multiplied straight into the accumulate. This is what lets ONE runtime three-way test
// enclose a whole member sequence - H accumulate, in-place transform, C accumulate - instead of
// being re-run per accumulate.
template <u32 KIND> DEVICE_FORCEINLINE void uniskip_pair_coeff_apply_reorder(const bf immediate, const bf v0, const bf v1, bf sum[2]) {
  if constexpr (KIND == UNISKIP_PAIR_COEFF_ONE) {
    sum[0] = bf::add(sum[0], v0);
    sum[1] = bf::add(sum[1], v1);
  } else if constexpr (KIND == UNISKIP_PAIR_COEFF_NEG_ONE) {
    sum[0] = bf::sub(sum[0], v0);
    sum[1] = bf::sub(sum[1], v1);
  } else {
    sum[0] = bf::fma(immediate, v0, sum[0]);
    sum[1] = bf::fma(immediate, v1, sum[1]);
  }
}

// The two RUNTIME coefficient forms behind one call shape, so the decode hoist is a template
// argument of the body rather than a second copy of its member loop. Both still test per
// accumulate; the compile-time form above is the one that does not.
template <bool DECODE_ONCE> struct uniskip_pair_coeff_form_reorder;

template <> struct uniskip_pair_coeff_form_reorder<false> {
  using coeff = uniskip_term;
  static DEVICE_FORCEINLINE coeff resolve(const uniskip_vm_desc &, const uniskip_term member) { return member; }
  static DEVICE_FORCEINLINE void sum(const uniskip_vm_desc &desc, const coeff c, const bf v[2], bf s[2]) { uniskip_pair_group_sum_reorder(desc, c, v, s); }
};

template <> struct uniskip_pair_coeff_form_reorder<true> {
  using coeff = uniskip_pair_coeff_reorder;
  static DEVICE_FORCEINLINE coeff resolve(const uniskip_vm_desc &desc, const uniskip_term member) { return uniskip_pair_coeff_decode_reorder(desc, member); }
  static DEVICE_FORCEINLINE void sum(const uniskip_vm_desc &, const coeff c, const bf v[2], bf s[2]) { uniskip_pair_group_sum_decoded_reorder(c, v, s); }
};

// How a body treats a member's coefficient: `R9` re-tests `member.coeff` at each accumulate (the
// R9 dispatch, unchanged), `KIND` resolves it once into a kind and still branches on that kind at
// each accumulate, `BRANCH` runs ONE runtime three-way test per member enclosing the member's
// whole sequence, so no coefficient test happens between the two accumulates at all.
constexpr u32 UNISKIP_PAIR_COEFF_FORM_R9 = 0;
constexpr u32 UNISKIP_PAIR_COEFF_FORM_KIND = 1;
constexpr u32 UNISKIP_PAIR_COEFF_FORM_BRANCH = 2;

// One group member's WHOLE sequence under a COMPILE-TIME coefficient kind: gate on H, turn the
// operands into their coset in place, gate on C. `HOIST_CLASS` = true is lever B - one class
// branch covering both phases, and no convergence slot, since each leg multiplies its product
// straight into the accumulate. false is lever C: the accumuland converges on `p` so both class
// branches stay. Either way the product is ephemeral because the transform overwrites its
// operands' storage.
template <u32 KIND, bool HOIST_CLASS>
DEVICE_FORCEINLINE void uniskip_pair_group_member_reorder(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                          const uniskip_term member, const bf immediate, bf sum_h[2], bf sum_c[2]) {
  bf a[2];
  uniskip_pair_load_h(desc, lane, member.source_a, a);
  if constexpr (HOIST_CLASS) {
    if (member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF) {
      bf b[2];
      uniskip_pair_load_h_second_reorder(desc, lane, member, a, b);
      uniskip_pair_coeff_apply_reorder<KIND>(immediate, bf::mul(a[0], b[0]), bf::mul(a[1], b[1]), sum_h);
      uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
      uniskip_pair_coset_second_reorder(desc, lane, member, cache, a, b);
      uniskip_pair_coeff_apply_reorder<KIND>(immediate, bf::mul(a[0], b[0]), bf::mul(a[1], b[1]), sum_c);
    } else {
      uniskip_pair_coeff_apply_reorder<KIND>(immediate, a[0], a[1], sum_h);
      uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
      uniskip_pair_coeff_apply_reorder<KIND>(immediate, a[0], a[1], sum_c);
    }
    return;
  }
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
  uniskip_pair_coeff_apply_reorder<KIND>(immediate, p[0], p[1], sum_h);
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
  uniskip_pair_coeff_apply_reorder<KIND>(immediate, p[0], p[1], sum_c);
}

// ---------------------------------------------------------------------------------------
// v3 R10 LAZY BF ACCUMULATORS. The grouped path above reduces after every product; these two
// accumulator states defer that to ONE fold per member sum. Both hold their value at Montgomery
// level R^2 - one reduction pending - so a raw wide product enters as itself while an existing
// residue `s` enters through the HIGH word (`s * 2^32 == s * R`, the trick `bf::fma` already
// uses). Design record: `2026-08-05-lazy-fma-accumulation-design.md`, §4 = A64, §5 = W96.
//
// Deferring is EXACT, so bit-identity of `q` is simultaneously the correctness gate and the
// overflow tripwire. Integer addition is associative, so unlike R9b's levers these states put no
// ordering constraint on the accumulate at all.
// ---------------------------------------------------------------------------------------

// W96 (design B): u64 plus a u32 carry word, one IADD per product over raw accumulation. No
// invariant and no comparison, so the term count is unbounded for any realistic arity.
struct uniskip_acc_w96 {
  u32 lo;
  u32 hi;
  u32 carry;
};

// A64 (design A): u64 under the invariant `acc < ORDER * 2^32`, restored by subtracting that
// same bound after every accumulate. It is a multiple of ORDER, so the subtraction is exact at
// any Montgomery level and costs no multiply, and the invariant IS `bf::red`'s domain - so the
// fold is the cheap reduce rather than `bf::red_wide`. Holds at any arity because the cadence is
// per accumulate; requires canonical operands, which every source here is.
struct uniskip_acc_a64 {
  u64 v;
};

constexpr u64 UNISKIP_ACC_P32 = static_cast<u64>(bf::ORDER) << 32;

DEVICE_FORCEINLINE void uniskip_acc_zero(uniskip_acc_w96 &acc) {
  acc.lo = 0;
  acc.hi = 0;
  acc.carry = 0;
}

DEVICE_FORCEINLINE void uniskip_acc_zero(uniskip_acc_a64 &acc) { acc.v = 0; }

DEVICE_FORCEINLINE void uniskip_acc_product(uniskip_acc_w96 &acc, const bf x, const bf y) {
  acc.lo = mad_lo_cc(x.limb, y.limb, acc.lo);
  acc.hi = madc_hi_cc(x.limb, y.limb, acc.hi);
  acc.carry = addc(acc.carry, 0u);
}

DEVICE_FORCEINLINE void uniskip_acc_product(uniskip_acc_a64 &acc, const bf x, const bf y) {
  acc.v += mul_wide(x.limb, y.limb);
  if (acc.v >= UNISKIP_ACC_P32)
    acc.v -= UNISKIP_ACC_P32;
}

// `word` is added at the HIGH word, i.e. times 2^32, which lifts a level-R residue to the
// accumulator's level. `word <= ORDER` is the widest admitted value (the negated case below), so
// the step adds at most UNISKIP_ACC_P32 and A64's one subtraction still restores the invariant.
DEVICE_FORCEINLINE void uniskip_acc_inject(uniskip_acc_w96 &acc, const u32 word) {
  acc.hi = add_cc(acc.hi, word);
  acc.carry = addc(acc.carry, 0u);
}

DEVICE_FORCEINLINE void uniskip_acc_inject(uniskip_acc_a64 &acc, const u32 word) {
  acc.v += static_cast<u64>(word) << 32;
  if (acc.v >= UNISKIP_ACC_P32)
    acc.v -= UNISKIP_ACC_P32;
}

// The carry word sits at 2^64, and 2^64 * R^-1 == 2^32 == R, so it folds in as `into_mont`.
DEVICE_FORCEINLINE bf uniskip_acc_fold(const uniskip_acc_w96 acc) {
  u64 w;
  reinterpret_cast<u32 *>(&w)[0] = acc.lo;
  reinterpret_cast<u32 *>(&w)[1] = acc.hi;
  return bf::add(bf::red_wide(w), bf::into_mont(bf(acc.carry)));
}

DEVICE_FORCEINLINE bf uniskip_acc_fold(const uniskip_acc_a64 acc) { return bf::red(acc.v); }

// A subtracting member negates one factor instead of the accumulator, so no borrow can reach the
// carry word or the invariant. `ORDER - x.limb` is at most ORDER, so a product against a
// canonical operand still stays under p^2 and §2's budgets hold unchanged.
DEVICE_FORCEINLINE bf uniskip_acc_negate(const bf x) { return bf(bf::ORDER - x.limb); }

// One member's contribution under a COMPILE-TIME coefficient kind. The three cases are where the
// reductions go: a plus / minus product accumulates raw (the reduce disappears), an immediate
// product keeps ONE reduce because three factors do not fit two, and a non-product member either
// injects its residue or becomes a bare `immediate * value` product with no reduce at all.
template <u32 KIND, typename ACC> DEVICE_FORCEINLINE void uniskip_acc_apply_value(const bf immediate, const bf v0, const bf v1, ACC acc[2]) {
  if constexpr (KIND == UNISKIP_PAIR_COEFF_ONE) {
    uniskip_acc_inject(acc[0], v0.limb);
    uniskip_acc_inject(acc[1], v1.limb);
  } else if constexpr (KIND == UNISKIP_PAIR_COEFF_NEG_ONE) {
    uniskip_acc_inject(acc[0], bf::ORDER - v0.limb);
    uniskip_acc_inject(acc[1], bf::ORDER - v1.limb);
  } else {
    uniskip_acc_product(acc[0], immediate, v0);
    uniskip_acc_product(acc[1], immediate, v1);
  }
}

template <u32 KIND, typename ACC>
DEVICE_FORCEINLINE void uniskip_acc_apply_product(const bf immediate, const bf a0, const bf b0, const bf a1, const bf b1, ACC acc[2]) {
  if constexpr (KIND == UNISKIP_PAIR_COEFF_ONE) {
    uniskip_acc_product(acc[0], a0, b0);
    uniskip_acc_product(acc[1], a1, b1);
  } else if constexpr (KIND == UNISKIP_PAIR_COEFF_NEG_ONE) {
    uniskip_acc_product(acc[0], uniskip_acc_negate(a0), b0);
    uniskip_acc_product(acc[1], uniskip_acc_negate(a1), b1);
  } else {
    uniskip_acc_product(acc[0], immediate, bf::mul(a0, b0));
    uniskip_acc_product(acc[1], immediate, bf::mul(a1, b1));
  }
}

// The INCUMBENT walk's grouped path runs ONE coefficient test per member covering both domains,
// so these take both accumulands rather than being called twice - the lazy body keeps the
// incumbent's branch count exactly, one class test and one coefficient test per member.
template <typename ACC>
DEVICE_FORCEINLINE void uniskip_acc_group_value(const uniskip_vm_desc &desc, const uniskip_term member, const bf h[2], const bf c[2], ACC acc_h[2],
                                                ACC acc_c[2]) {
  if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
    uniskip_acc_apply_value<UNISKIP_PAIR_COEFF_ONE>(bf::ZERO(), h[0], h[1], acc_h);
    uniskip_acc_apply_value<UNISKIP_PAIR_COEFF_ONE>(bf::ZERO(), c[0], c[1], acc_c);
  } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
    uniskip_acc_apply_value<UNISKIP_PAIR_COEFF_NEG_ONE>(bf::ZERO(), h[0], h[1], acc_h);
    uniskip_acc_apply_value<UNISKIP_PAIR_COEFF_NEG_ONE>(bf::ZERO(), c[0], c[1], acc_c);
  } else {
    const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
    uniskip_acc_apply_value<UNISKIP_PAIR_COEFF_IMMEDIATE>(immediate, h[0], h[1], acc_h);
    uniskip_acc_apply_value<UNISKIP_PAIR_COEFF_IMMEDIATE>(immediate, c[0], c[1], acc_c);
  }
}

template <typename ACC>
DEVICE_FORCEINLINE void uniskip_acc_group_product(const uniskip_vm_desc &desc, const uniskip_term member, const bf ah[2], const bf ac[2], const bf bh[2],
                                                  const bf bc[2], ACC acc_h[2], ACC acc_c[2]) {
  if (member.coeff == UNISKIP_IMMEDIATE_ONE) {
    uniskip_acc_apply_product<UNISKIP_PAIR_COEFF_ONE>(bf::ZERO(), ah[0], bh[0], ah[1], bh[1], acc_h);
    uniskip_acc_apply_product<UNISKIP_PAIR_COEFF_ONE>(bf::ZERO(), ac[0], bc[0], ac[1], bc[1], acc_c);
  } else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE) {
    uniskip_acc_apply_product<UNISKIP_PAIR_COEFF_NEG_ONE>(bf::ZERO(), ah[0], bh[0], ah[1], bh[1], acc_h);
    uniskip_acc_apply_product<UNISKIP_PAIR_COEFF_NEG_ONE>(bf::ZERO(), ac[0], bc[0], ac[1], bc[1], acc_c);
  } else {
    const bf immediate = desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED];
    uniskip_acc_apply_product<UNISKIP_PAIR_COEFF_IMMEDIATE>(immediate, ah[0], bh[0], ah[1], bh[1], acc_h);
    uniskip_acc_apply_product<UNISKIP_PAIR_COEFF_IMMEDIATE>(immediate, ac[0], bc[0], ac[1], bc[1], acc_c);
  }
}

// The R9b `C+D` walk's member sequence with a lazy accumuland: gate on H, turn the operands into
// their coset in place, gate on C, under ONE runtime coefficient test hoisted to the caller. The
// two `if (product)` tests are lever C's, so the branch count is `C+D`'s exactly. What C's
// convergence slot cannot survive is the accumulate ABSORBING the multiply: a plus / minus
// product never becomes a value, so each phase reaches two call sites instead of one.
template <u32 KIND, typename ACC>
DEVICE_FORCEINLINE void uniskip_pair_group_member_lazy(const uniskip_vm_desc &desc, const uniskip_pair_lane &lane, const uniskip_coset_cache &cache,
                                                       const uniskip_term member, const bf immediate, ACC sum_h[2], ACC sum_c[2]) {
  bf a[2];
  uniskip_pair_load_h(desc, lane, member.source_a, a);
  const bool product = member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF;
  bf b[2];
  if (product) {
    uniskip_pair_load_h_second_reorder(desc, lane, member, a, b);
    uniskip_acc_apply_product<KIND>(immediate, a[0], b[0], a[1], b[1], sum_h);
  } else {
    uniskip_acc_apply_value<KIND>(immediate, a[0], a[1], sum_h);
  }
  uniskip_pair_coset_reorder(desc, lane, member.source_a, cache, a);
  if (product) {
    uniskip_pair_coset_second_reorder(desc, lane, member, cache, a, b);
    uniskip_acc_apply_product<KIND>(immediate, a[0], b[0], a[1], b[1], sum_c);
  } else {
    uniskip_acc_apply_value<KIND>(immediate, a[0], a[1], sum_c);
  }
}

// ---------------------------------------------------------------------------------------
// v3 R10 OUTER-LEVEL WIDE ACCUMULATION. The states above defer a group's ~3 products; this holds
// the WALK's four `e4` accumulators wide instead, so a term's `coeff x value` is never reduced -
// one fold per pass, at green's level (`gpu_gkr_windowed_bench/native/windowed_vm.cu`'s
// `window_u96_fold`, which is `window_u96 values[3][4]` = cells x limbs and the same
// `mad_lo_cc`/`madc_hi_cc`/`addc` step). Our accumulator states are reused verbatim.
//
// E4 ARITHMETIC STAYS CANONICAL, which is green's winning division: an extension-valued term still
// forms `e4::mul(coeff, value)` exactly as the parent does and its four canonical residues enter
// through the mid word. Only the base-field accumulate goes wide.
// ---------------------------------------------------------------------------------------

template <typename ACC> struct uniskip_acc_e4 {
  ACC limb[4];
};

template <typename ACC> DEVICE_FORCEINLINE void uniskip_acc_e4_zero(uniskip_acc_e4<ACC> &acc) {
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    uniskip_acc_zero(acc.limb[i]);
}

// A BASE-valued term: the coefficient's four limbs against one base value, no reduction anywhere.
// Flat limb order is `e4`'s own (`base_coefficient_from_flat_idx`, i.e. [0][0] [0][1] [1][0]
// [1][1]), which is what the `e4(bf[4])` constructor in the fold reads back.
template <typename ACC> DEVICE_FORCEINLINE void uniskip_acc_e4_bf(uniskip_acc_e4<ACC> &acc, const e4 coeff, const bf v) {
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    uniskip_acc_product(acc.limb[i], coeff.base_coefficient_from_flat_idx(i), v);
}

// An EXTENSION-valued term: the `e4 x e4` product is the parent's canonical one, so this accumulate
// costs no reduction of its own - the residues ride in at the mid word.
template <typename ACC> DEVICE_FORCEINLINE void uniskip_acc_e4_e4(uniskip_acc_e4<ACC> &acc, const e4 coeff, const e4 v) {
  const e4 t = e4::mul(coeff, v);
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    uniskip_acc_inject(acc.limb[i], t.base_coefficient_from_flat_idx(i).limb);
}

template <typename ACC> DEVICE_FORCEINLINE e4 uniskip_acc_e4_fold(const uniskip_acc_e4<ACC> &acc) {
  bf limbs[4];
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    limbs[i] = uniskip_acc_fold(acc.limb[i]);
  return e4(limbs);
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
