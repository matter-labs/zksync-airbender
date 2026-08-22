// Segmented backward VM. Warps first publish required folds, synchronize, then
// evaluate their assigned atom lists. Warp 0 reduces the partials and applies eq.
// Every backing is LSB-dense at its own depth: logical index `u = 2 * row + b` sits at `V[u]` (endpoints ADJACENT), and a backing `delta` levels below the
// target depth holds `u`'s 2^delta leaves at `V[(u << delta) + q]`, `q` carrying this round's bound coordinates on its low bits. Fold level d uses
// claim_point[d]. Pre-fold reads use ld.cs, publish stores st.wb, and eval reads ld.ca.

#include "segmented_vm.cuh"

__device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];

__device__ __constant__ e4 ab_gkr_bwd_seg_coeff_bank[airbender::gkr::BWD_SEG_OUTPUT_BANK];

__device__ __constant__ e4 ab_gkr_bwd_seg_fold_weights[airbender::gkr::BWD_SEG_FOLD_WEIGHT_SLOTS];

namespace airbender::gkr {

// ── Lane addressing ─────────────────────────────────────────────────────────
//
// A source record carries two LANES — a read and a destination — into ONE table
// of `(base, log2_stride)` slots. A slot is keyed by BACKING, so two sources
// reading the same matrix share it, and a source whose fold buffer is packed
// differently from its matrix simply names a different slot on its other lane.
// The stride is in elements of the requested type.
template <typename T> DEVICE_FORCEINLINE const T *seg_lane_column(const bwd_seg_desc &desc, const u16 lane) {
  const bwd_seg_addr_slot &slot = desc.slot[bwd_seg_lane_slot(lane)];
  const T *base = reinterpret_cast<const T *>(slot.base);
  return base + (static_cast<size_t>(bwd_seg_lane_column(lane)) << slot.log2_stride);
}

DEVICE_FORCEINLINE e4 *seg_lane_column_mut(const bwd_seg_desc &desc, const u16 lane) { return const_cast<e4 *>(seg_lane_column<e4>(desc, lane)); }

// ── Raw leaf sources ────────────────────────────────────────────────────────
//
// One value of a backing at ITS OWN depth and width. The three shapes differ only
// in where the value comes from, so everything above them — the lift, the flat
// fold, the projections — is written once.

template <ld_modifier HINT> struct seg_raw_bf_column {
  const bf *column;
  DEVICE_FORCEINLINE bf operator()(const u32 index) const { return load<bf, HINT>(column, index); }
};

template <ld_modifier HINT> struct seg_raw_e4_column {
  const e4 *column;
  DEVICE_FORCEINLINE e4 operator()(const u32 index) const { return load<e4, HINT>(column, index); }
};

// A virtual-setup (procedural) source has no matrix: its value is produced from
// the backing INDEX, which is what keeps it row-dependent. Exactly four kinds are
// synthesizable and the census assert lives with them
// (`bwd_coeff_procedural_source_kind`).
struct seg_raw_synthesized {
  gkr_base_source_kind kind;
  DEVICE_FORCEINLINE bf operator()(const u32 index) const { return gkr_virtual_base_value(kind, index); }
};

// The deliberate base -> extension lift, at the ONE place a depth-zero base value
// enters E4 arithmetic.
DEVICE_FORCEINLINE e4 seg_lift(const bf value) { return e4::from_scalar(value); }

DEVICE_FORCEINLINE e4 seg_lift(const e4 &value) { return value; }

// ── Fold weights ────────────────────────────────────────────────────────────

// One thread builds one slot. The round's claim-point update is stream-ordered before this launch. Slot `q` is leaf `q`'s weight: `q`'s bit j is the same bit
// the leaf's backing index carries, so no permutation and `q` walks monotonically.
DEVICE_FORCEINLINE void seg_build_fold_weights(e4 *fold_weights, const u32 round) {
  const u32 slot = threadIdx.x;
  if (blockIdx.x != 0 || slot >= BWD_SEG_FOLD_WEIGHT_SLOTS)
    return;
  const u32 delta = slot < BWD_SEG_FOLD_WEIGHT_BASE_D2 ? 1 : slot < BWD_SEG_FOLD_WEIGHT_BASE_D3 ? 2 : 3;
  const u32 base = delta == 1 ? BWD_SEG_FOLD_WEIGHT_BASE_D1 : delta == 2 ? BWD_SEG_FOLD_WEIGHT_BASE_D2 : BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const u32 q = slot - base + 1;
  if (delta > round) {
    // Unreachable by lowering (delta <= round, seg_lower's InvalidDepths /
    // target == round checks); zeroed rather than left stale.
    fold_weights[slot] = e4::ZERO();
    return;
  }
  const e4 one = e4::from_scalar(bf::ONE());
  e4 w = one;
  for (u32 j = 0; j < delta; j++) {
    const e4 c = ::ab_gkr_main_layer_claim_point[round - delta + j];
    const u32 bit = (q >> j) & 1;
    w = e4::mul(w, bit != 0 ? c : e4::sub(one, c));
  }
  fold_weights[slot] = w;
}

// ── Flat fold ───────────────────────────────────────────────────────────────
// A depth-DELTA fold is a dot product over its 2^DELTA physical leaves with
// challenge-only weights; the Lagrange weights sum to ONE exactly, so it is
// evaluated in DIFFERENCE form with the q = 0 coefficient identically 1:
//
//   fold(u) = leaf0 + sum_{q>=1} w_q * (raw((u << DELTA) + q) - leaf0)
//
// One accumulator, one common subtrahend, 2^DELTA - 1 mixed fmas, no interior e4 x e4 nodes. At DELTA == 1 this is the affine `fma(r, f1 - f0, f0)` form.
template <u32 DELTA, typename Raw> DEVICE_FORCEINLINE e4 seg_fold_flat(const Raw &raw, const u32 u) {
  static_assert(DELTA >= 1 && DELTA <= BWD_SEG_MAX_FOLD_DEPTH, "fold outside 1..BWD_SEG_MAX_FOLD_DEPTH");
  constexpr u32 BASE = DELTA == 1 ? BWD_SEG_FOLD_WEIGHT_BASE_D1 : DELTA == 2 ? BWD_SEG_FOLD_WEIGHT_BASE_D2 : BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const u32 leaf = u << DELTA;
  const auto leaf0 = raw(leaf);
  e4 acc = seg_lift(leaf0);
#pragma unroll 1
  for (u32 q = 1; q < (1u << DELTA); q++) {
    const e4 w = ::ab_gkr_bwd_seg_fold_weights[BASE + q - 1];
    acc = e4::fma(w, decltype(leaf0)::sub(raw(leaf + q), leaf0), acc);
  }
  return acc;
}

// One target-depth value out of a backing `delta` folds behind it.
//
// `MAX_DEPTH` is the deepest fold this call site can need — 3 in the prologue,
// `BWD_SEG_MAX_INLINE_FOLD_DEPTH` in the eval loop (the assignment matrix
// publishes at depth 3 instead of inlining it), 0 at R0 (depth 0 everywhere) — so
// no site compiles a fold it cannot execute.
template <u32 MAX_DEPTH, typename Raw> DEVICE_FORCEINLINE e4 seg_fold(const Raw &raw, const u32 u, const u32 delta) {
  if constexpr (MAX_DEPTH >= 3) {
    if (delta == 3)
      return seg_fold_flat<3>(raw, u);
  }
  if constexpr (MAX_DEPTH >= 2) {
    if (delta == 2)
      return seg_fold_flat<2>(raw, u);
  }
  if constexpr (MAX_DEPTH >= 1) {
    if (delta == 1)
      return seg_fold_flat<1>(raw, u);
  }
  // `delta == 0`: the backing IS at target depth. A delta past `MAX_DEPTH` cannot
  // arrive — `lower_bwd_seg` rejects one (`UnsupportedFoldDelta`, `InvalidDepths`)
  // and `assign_class` is what pairs a class with its depth — and a release
  // kernel has no error channel, so it resolves as depth zero rather than reading
  // an undefined shape.
  return seg_lift(raw(u));
}

// Both target-depth endpoints of one folded source in ONE pass over q: same loads as two seg_fold_flat calls, each weight consumed once, two independent fma
// chains for ILP. Takes the EVEN endpoint `u`, the same index `seg_fold_flat` takes; the odd endpoint's leaf block is `+ 2^DELTA`.
template <u32 DELTA, typename Raw> DEVICE_FORCEINLINE void seg_fold_endpoints_flat(const Raw &raw, const u32 u, e4 &s0, e4 &s1) {
  static_assert(DELTA >= 1 && DELTA <= BWD_SEG_MAX_FOLD_DEPTH, "fold outside 1..BWD_SEG_MAX_FOLD_DEPTH");
  constexpr u32 BASE = DELTA == 1 ? BWD_SEG_FOLD_WEIGHT_BASE_D1 : DELTA == 2 ? BWD_SEG_FOLD_WEIGHT_BASE_D2 : BWD_SEG_FOLD_WEIGHT_BASE_D3;
  constexpr u32 LEAVES = 1u << DELTA;
  const u32 leaf = u << DELTA;
  const auto leaf0_lo = raw(leaf);
  const auto leaf0_hi = raw(leaf + LEAVES);
  s0 = seg_lift(leaf0_lo);
  s1 = seg_lift(leaf0_hi);
#pragma unroll 1
  for (u32 q = 1; q < LEAVES; q++) {
    const e4 w = ::ab_gkr_bwd_seg_fold_weights[BASE + q - 1];
    s0 = e4::fma(w, decltype(leaf0_lo)::sub(raw(leaf + q), leaf0_lo), s0);
    s1 = e4::fma(w, decltype(leaf0_hi)::sub(raw(leaf + LEAVES + q), leaf0_hi), s1);
  }
}

template <u32 MAX_DEPTH, typename Raw> DEVICE_FORCEINLINE void seg_fold_endpoints(const Raw &raw, const u32 u, const u32 delta, e4 &s0, e4 &s1) {
  if constexpr (MAX_DEPTH >= 3)
    if (delta == 3)
      return seg_fold_endpoints_flat<3>(raw, u, s0, s1);
  if constexpr (MAX_DEPTH >= 2)
    if (delta == 2)
      return seg_fold_endpoints_flat<2>(raw, u, s0, s1);
  if constexpr (MAX_DEPTH >= 1)
    if (delta == 1)
      return seg_fold_endpoints_flat<1>(raw, u, s0, s1);
  s0 = seg_lift(raw(u));
  s1 = seg_lift(raw(u | 1));
}

// ── Projections ─────────────────────────────────────────────────────────────

// The projections a term class consumes: `C0Linear` the Endpoint0, `C2Product`
// the Delta, `DualProduct` both. No projection travels on the wire — the class
// implies it — so this is a compile-time axis of the resolvers.
enum seg_projection : u32 {
  SEG_PROJ_ENDPOINT0 = 0,
  SEG_PROJ_DELTA = 1,
  SEG_PROJ_PAIR = 2,
};

template <typename T> struct seg_value {
  T endpoint0;
  T delta;
};

// The unused component is returned as zero rather than left undefined; every caller is fully inlined, so it costs nothing.
template <seg_projection P, typename Value> DEVICE_FORCEINLINE auto seg_project(const Value &value, const u32 row) {
  const u32 u = row << 1;
  using T = decltype(value(u));
  if constexpr (P == SEG_PROJ_ENDPOINT0) {
    return seg_value<T>{value(u), T::ZERO()};
  } else {
    const T s0 = value(u);
    const T s1 = value(u | 1);
    const T delta = T::sub(s1, s0);
    if constexpr (P == SEG_PROJ_DELTA)
      return seg_value<T>{T::ZERO(), delta};
    else
      return seg_value<T>{s0, delta};
  }
}

// The same three projections over a FOLDED source, each fused into a SINGLE pass
// over the leaves instead of folding first and projecting after: a Delta never
// materializes the two endpoints it would subtract, and a Pair walks the leaves
// once for both chains. `seg_project` above serves the DIRECT sources, where a
// leaf read already IS the target-depth value.
template <seg_projection P, u32 MAX_DEPTH, typename Raw> DEVICE_FORCEINLINE seg_value<e4> seg_project_folded(const Raw &raw, const u32 row, const u32 delta) {
  const u32 u = row << 1;
  if constexpr (P == SEG_PROJ_ENDPOINT0) {
    return seg_value<e4>{seg_fold<MAX_DEPTH>(raw, u, delta), e4::ZERO()};
  } else if constexpr (P == SEG_PROJ_DELTA) {
    static_assert(MAX_DEPTH == 0, "delta projection is R0-only");
    return seg_value<e4>{e4::ZERO(), e4::sub(seg_lift(raw(u | 1)), seg_lift(raw(u)))};
  } else {
    e4 s0;
    e4 s1;
    seg_fold_endpoints<MAX_DEPTH>(raw, u, delta, s0, s1);
    return seg_value<e4>{s0, e4::sub(s1, s0)};
  }
}

// ── Operand resolution ──────────────────────────────────────────────────────

// A BASE-FIELD operand, at the projection its class implies.
//
// Base-field operands occur only at R0 and therefore need no fold.
template <seg_projection P> DEVICE_FORCEINLINE seg_value<bf> seg_resolve_bf(const bwd_seg_desc &desc, const u16 slot, const u32 row) {
  const bwd_seg_source_record record = desc.source[slot];
  if (record.source_class == BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE) {
    const bwd_seg_addr_slot &addr = desc.slot[bwd_seg_lane_slot(record.src)];
    return seg_project<P>(seg_raw_synthesized{bwd_coeff_procedural_source_kind(addr.procedural_kind)}, row);
  }
  return seg_project<P>(seg_raw_bf_column<ld_modifier::ca>{seg_lane_column<bf>(desc, record.src)}, row);
}

// An EXTENSION-FIELD operand, at the projection its class implies.
//
// The four live source classes resolve as follows, and the class — not the
// window's origin — is what dispatches, because the class is the per-`(source,
// round)` decision host lowering already made:
//
//   E4Direct          one 16-byte load, from the PUBLISH backing when the
//                     prologue materialized this window and from the read backing
//                     otherwise. There is never a fold here: `assign_class`
//                     publishes every E4Direct window whose delta is nonzero.
//   BfInlineD1/D2     a depth-1 or depth-2 flat fold straight from raw base field,
//                     in registers, `ld.ca` because those raws are re-read across
//                     terms.
//   ProceduralInline  the same fold over synthesized rows.
//   BfDirect          depth zero, so the lift. Reachable only at R0 (see
//                     `seg_resolve_bf`), where `MAX_DEPTH` is zero anyway.
template <seg_projection P, u32 MAX_DEPTH> DEVICE_FORCEINLINE seg_value<e4> seg_resolve_e4(const bwd_seg_desc &desc, const u16 slot, const u32 row) {
  const bwd_seg_source_record record = desc.source[slot];
  if (record.source_class == BWD_SEG_SOURCE_CLASS_E4_DIRECT) {
    // A source that publishes this round is read back from where the prologue
    // PUT it, not from the leaves it folded: `seg_fold_and_publish` has already
    // written `cache` for this row. Reading `src` instead would re-read the raw
    // backing the fold consumed, which is a round behind.
    const u16 lane = record.cache != BWD_SEG_ADDR_NONE ? record.cache : record.src;
    return seg_project<P>(seg_raw_e4_column<ld_modifier::ca>{seg_lane_column<e4>(desc, lane)}, row);
  }
  const u32 delta = u32{record.delta};
  if (record.source_class == BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE) {
    const bwd_seg_addr_slot &addr = desc.slot[bwd_seg_lane_slot(record.src)];
    const seg_raw_synthesized raw{bwd_coeff_procedural_source_kind(addr.procedural_kind)};
    return seg_project_folded<P, MAX_DEPTH>(raw, row, delta);
  }
  const seg_raw_bf_column<ld_modifier::ca> raw{seg_lane_column<bf>(desc, record.src)};
  return seg_project_folded<P, MAX_DEPTH>(raw, row, delta);
}

// ── Fold prologue ───────────────────────────────────────────────────────────

// Fold ONE source's 32-row slice down to the current round and publish both
// endpoints.
//
// The prologue dispatches on the window's ORIGIN rather than on the source class:
// every foldable source is `E4Direct` by construction (that is what publishing
// MEANS in the assignment matrix), so the class carries no information here, while
// the origin is what says whether the leaves are raw base field, a previous
// round's E4 materialization, or row synthesis.
//
// Depth work per origin, all through the same flat fold: an E4 chain step is
// `2xE4 -> E4` at delta 1, a base-field or procedural window at the publication
// depth is an `8xBF -> E4` depth-3 fold, and a base-field window under
// `D2Policy::Materialize` is the depth-2 `4xBF -> E4` case.
DEVICE_FORCEINLINE void seg_fold_and_publish(const bwd_seg_desc &desc, const u16 slot, const u32 row, const bool active) {
  const bwd_seg_source_record record = desc.source[slot];
  const bwd_seg_addr_slot &addr = desc.slot[bwd_seg_lane_slot(record.src)];
  const u32 delta = u32{record.delta};
  const u32 u = row << 1;

  e4 s0;
  e4 s1;
  if (addr.origin == BWD_COEFF_ORIGIN_READ_EXT) {
    const seg_raw_e4_column<ld_modifier::cs> raw{seg_lane_column<e4>(desc, record.src)};
    seg_fold_endpoints<BWD_SEG_MAX_FOLD_DEPTH>(raw, u, delta, s0, s1);
  } else if (addr.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
    const seg_raw_synthesized raw{bwd_coeff_procedural_source_kind(addr.procedural_kind)};
    seg_fold_endpoints<BWD_SEG_MAX_FOLD_DEPTH>(raw, u, delta, s0, s1);
  } else {
    const seg_raw_bf_column<ld_modifier::cs> raw{seg_lane_column<bf>(desc, record.src)};
    seg_fold_endpoints<BWD_SEG_MAX_FOLD_DEPTH>(raw, u, delta, s0, s1);
  }

  // Only a live row publishes. A dead lane of the last tile folded a CLAMPED row
  // (see `seg_body`), and letting it store would write a duplicate of another
  // lane's value.
  if (!active)
    return;
  e4 *publish = seg_lane_column_mut(desc, record.cache);
  // Blocks own disjoint row ranges and exactly one warp folds a given source, so the pair `2 * row`, `2 * row + 1` has a single writer. The destination is
  // never a leaf this launch reads: the host allocates round r's buffer before retiring round r - 1's, and no lowering check enforces that. `wb` keeps the
  // pair in L1 for the eval loop's `ld.ca` re-reads.
  store<e4, st_modifier::wb>(publish, s0, u);
  store<e4, st_modifier::wb>(publish, s1, u | 1);
}

// ── Seed and contribution store ─────────────────────────────────────────────

// The `acc_c0` seed, resolved through the launch's own coefficient bank.
//
DEVICE_FORCEINLINE e4 seg_c_init(const bwd_seg_desc &desc) {
  if (desc.c_init_coeff == BWD_SEG_C_INIT_NONE)
    return e4::ZERO();
  return AB_GKR_BWD_SEG_COEFF(static_cast<u16>(desc.c_init_coeff));
}

DEVICE_FORCEINLINE void seg_store_row(const bwd_seg_desc &desc, const u32 row, const u32 lane, const bool active, const e4 &sum_c0, const e4 &sum_c2) {
  e4 row_c0 = e4::ZERO();
  e4 row_c2 = e4::ZERO();
  if (active) {
    const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, row);
    row_c0 = e4::mul(sum_c0, eq);
    row_c2 = e4::mul(sum_c2, eq);
  }

  const e4 tile_c0 = ::airbender::gkr::gkr_trace_holder_partials_warp_reduce_sum<e4>(row_c0);
  const e4 tile_c2 = ::airbender::gkr::gkr_trace_holder_partials_warp_reduce_sum<e4>(row_c2);
  if (lane == 0) {
    store<e4, st_modifier::cs>(desc.contributions, tile_c0, blockIdx.x * 2u + 0u);
    store<e4, st_modifier::cs>(desc.contributions, tile_c2, blockIdx.x * 2u + 1u);
  }
}

// ── Epilogues ───────────────────────────────────────────────────────────────

// Reduce the `k` per-warp partials of this lane's row into warp 0.
DEVICE_FORCEINLINE void seg_epilogue(const bwd_seg_desc &desc, const u32 k, const u32 lane, const u32 warp_id, const u32 row, const bool active,
                                     const e4 &part_c0, const e4 &part_c2) {
  extern __shared__ e4 plane[];
  if (k == 1) {
    seg_store_row(desc, row, lane, active, part_c0, part_c2);
    return;
  }
  const u32 slot = (warp_id - 1) * BWD_SEG_WARP_LANES + lane;
  if (warp_id != 0)
    plane[slot] = part_c0;
  __syncthreads();
  e4 sum_c0 = part_c0;
  if (warp_id == 0)
    for (u32 w = 0; w < k - 1; w++)
      sum_c0 = e4::add(sum_c0, plane[w * BWD_SEG_WARP_LANES + lane]);
  __syncthreads();
  if (warp_id != 0)
    plane[slot] = part_c2;
  __syncthreads();
  if (warp_id == 0) {
    e4 sum_c2 = part_c2;
    for (u32 w = 0; w < k - 1; w++)
      sum_c2 = e4::add(sum_c2, plane[w * BWD_SEG_WARP_LANES + lane]);
    seg_store_row(desc, row, lane, active, sum_c0, sum_c2);
  }
}

// ── One term ────────────────────────────────────────────────────────────────

// Squared products resolve both operands through the same path.
template <bool IS_R0, u32 MAX_DEPTH>
DEVICE_FORCEINLINE void seg_execute_term(const bwd_seg_desc &desc, const u16 term_class, const u16 coefficient_index, const u16 source_a, const u16 source_b,
                                         const u32 row, e4 &acc_c0, e4 &acc_c2) {
  // Reserved literals occupy the bank head, so every term uses one bank load.
  const e4 coefficient = AB_GKR_BWD_SEG_COEFF(coefficient_index);
  if constexpr (IS_R0) {
    switch (term_class) {
    case BWD_SEG_R0_CLASS_C0_LINEAR_BF: {
      const bf a = seg_resolve_bf<SEG_PROJ_ENDPOINT0>(desc, source_a, row).endpoint0;
      // `e4::fma(e4, bf, e4)` is four fused `bf::fma`s: a base-field operand never
      // gets lifted just to be multiplied.
      acc_c0 = e4::fma(coefficient, a, acc_c0);
      break;
    }
    case BWD_SEG_R0_CLASS_C0_LINEAR_E4: {
      const e4 a = seg_resolve_e4<SEG_PROJ_ENDPOINT0, MAX_DEPTH>(desc, source_a, row).endpoint0;
      acc_c0 = e4::fma(coefficient, a, acc_c0);
      break;
    }
    case BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF: {
      const bf a = seg_resolve_bf<SEG_PROJ_DELTA>(desc, source_a, row).delta;
      const bf b = seg_resolve_bf<SEG_PROJ_DELTA>(desc, source_b, row).delta;
      acc_c2 = e4::fma(coefficient, bf::mul(a, b), acc_c2);
      break;
    }
    case BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4: {
      // The wire normalizes a mixed product to BF-FIRST, so `source_a` is always
      // the base-field factor (an encoder invariant, pinned by
      // `a_mixed_product_puts_the_bf_factor_first`).
      const bf a = seg_resolve_bf<SEG_PROJ_DELTA>(desc, source_a, row).delta;
      const e4 b = seg_resolve_e4<SEG_PROJ_DELTA, MAX_DEPTH>(desc, source_b, row).delta;
      // Keep the base-field factor on the fused multiply-add.
      acc_c2 = e4::fma(e4::mul(coefficient, b), a, acc_c2);
      break;
    }
    case BWD_SEG_R0_CLASS_C2_PRODUCT_E4_E4: {
      const e4 a = seg_resolve_e4<SEG_PROJ_DELTA, MAX_DEPTH>(desc, source_a, row).delta;
      const e4 b = seg_resolve_e4<SEG_PROJ_DELTA, MAX_DEPTH>(desc, source_b, row).delta;
      acc_c2 = e4::fma(coefficient, e4::mul(a, b), acc_c2);
      break;
    }
    default:
      // Classes 5..7 are deliberately dead and a validated program has none. A
      // release kernel has no error channel, so an invalid record contributes
      // nothing rather than resolving an undefined operand shape.
      break;
    }
    return;
  }
  switch (term_class) {
  case BWD_SEG_EXT_CLASS_C0_LINEAR_E4: {
    const e4 a = seg_resolve_e4<SEG_PROJ_ENDPOINT0, MAX_DEPTH>(desc, source_a, row).endpoint0;
    acc_c0 = e4::fma(coefficient, a, acc_c0);
    break;
  }
  case BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4: {
    // ONE coefficient and ONE pair resolution per factor feed BOTH accumulators;
    // splitting this into a C0 and a C2 term would resolve every endpoint twice,
    // which is the whole reason the class is native.
    const seg_value<e4> a = seg_resolve_e4<SEG_PROJ_PAIR, MAX_DEPTH>(desc, source_a, row);
    const seg_value<e4> b = seg_resolve_e4<SEG_PROJ_PAIR, MAX_DEPTH>(desc, source_b, row);
    acc_c0 = e4::fma(coefficient, e4::mul(a.endpoint0, b.endpoint0), acc_c0);
    acc_c2 = e4::fma(coefficient, e4::mul(a.delta, b.delta), acc_c2);
    break;
  }
  default:
    break;
  }
}

// ── One grouped member ──────────────────────────────────────────────────────

// Add `immediate * value` to one of a group's per-side sums.
DEVICE_FORCEINLINE void seg_apply_immediate(const bwd_seg_desc &desc, const u16 immediate_id, const e4 &value, e4 &sum) {
  if (immediate_id == BWD_SEG_IMMEDIATE_ONE) {
    sum = e4::add(sum, value);
  } else if (immediate_id == BWD_SEG_IMMEDIATE_NEG_ONE) {
    sum = e4::sub(sum, value);
  } else {
    sum = e4::fma(value, bf::from_reduced_raw_repr(desc.immediates[immediate_id - BWD_SEG_IMMEDIATE_RESERVED]), sum);
  }
}

// Accumulate one continuation group member into its per-side sums.
template <u32 MAX_DEPTH>
DEVICE_FORCEINLINE void seg_execute_group_member(const bwd_seg_desc &desc, const u16 member_class, const u16 immediate_id, const u16 source_a,
                                                 const u16 source_b, const u32 row, e4 &s_c0, e4 &s_c2) {
  switch (member_class) {
  case BWD_SEG_EXT_CLASS_C0_LINEAR_E4: {
    const e4 a = seg_resolve_e4<SEG_PROJ_ENDPOINT0, MAX_DEPTH>(desc, source_a, row).endpoint0;
    seg_apply_immediate(desc, immediate_id, a, s_c0);
    break;
  }
  case BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4: {
    const seg_value<e4> a = seg_resolve_e4<SEG_PROJ_PAIR, MAX_DEPTH>(desc, source_a, row);
    const seg_value<e4> b = seg_resolve_e4<SEG_PROJ_PAIR, MAX_DEPTH>(desc, source_b, row);
    seg_apply_immediate(desc, immediate_id, e4::mul(a.endpoint0, b.endpoint0), s_c0);
    seg_apply_immediate(desc, immediate_id, e4::mul(a.delta, b.delta), s_c2);
    break;
  }
  default:
    // As in `seg_execute_term`: a validated program has no member at a dead class
    // (`lean::validate_program`'s `ClassNotInRegime`, and `NestedGroupHeader` for
    // the control code itself), and a release kernel has no error channel — so an
    // invalid record contributes nothing rather than resolving an undefined operand
    // shape.
    break;
  }
}

DEVICE_FORCEINLINE void seg_apply_group_core(const e4 &core, const u16 flags, const e4 &s_c0, const e4 &s_c2, e4 &acc_c0, e4 &acc_c2) {
  if ((flags & BWD_SEG_GROUP_FLAG_C0) != 0)
    acc_c0 = e4::fma(core, s_c0, acc_c0);
  if ((flags & BWD_SEG_GROUP_FLAG_C2) != 0)
    acc_c2 = e4::fma(core, s_c2, acc_c2);
}

// ── The executor body ───────────────────────────────────────────────────────

template <bool IS_R0> DEVICE_FORCEINLINE void seg_body(const bwd_seg_desc &desc) {
  // R0 is depth 0 everywhere: no prologue, and no inline fold either.
  constexpr u32 MAX_DEPTH = IS_R0 ? 0u : BWD_SEG_MAX_INLINE_FOLD_DEPTH;

  const u32 rows = desc.logical_rows;
  const u32 k = desc.k;
  const u32 lane = threadIdx.x & BWD_SEG_LANE_INDEX_MASK;
  const u32 warp_id = threadIdx.x >> BWD_SEG_WARP_SHIFT;
  const u32 tile_row = blockIdx.x * BWD_SEG_WARP_LANES + lane;
  // Clamp partial-tile lanes to keep the block-wide barriers uniform.
  const bool active = tile_row < rows;
  const u32 row = active ? tile_row : rows - 1;

  if constexpr (!IS_R0) {
    // Warps stripe over the fold list in host order.
    for (u32 s = warp_id; s < u32{desc.num_foldable}; s += k)
      seg_fold_and_publish(desc, desc.fold_source[s], row, active);
    // THE fold -> eval barrier, and the only one outside the epilogue. It is also
    // the release of the publish stores: warp `w` reads at its own lane a value
    // another warp of this block wrote, and both live in this SM's L1.
    __syncthreads();
  }

  // Exactly one partial may carry the seed: `k` seeded partials would
  // reduce to `k * c_init`. R0 has no seed path at all — R0 lowering drops the
  // spine's scalar addends, so seeding one would double-count it (enforced by
  // `lower_bwd_seg`'s `R0CarriesCInit`).
  e4 acc_c0 = e4::ZERO();
  e4 acc_c2 = e4::ZERO();
  if constexpr (!IS_R0) {
    if (warp_id == 0)
      acc_c0 = seg_c_init(desc);
  }

  // Warp `w` walks its own contiguous list. `blockDim == 32 * k`, so `warp_id < k`
  // and `warp_id + 1` is inside `list_offset`.
  const u32 pc_end = desc.list_offset[warp_id + 1];
#pragma unroll 1
  for (u32 pc = desc.list_offset[warp_id]; pc < pc_end; pc += BWD_SEG_WORDS_PER_TERM) {
    const u16 header = desc.program[pc];
    const u16 term_class = (header >> BWD_SEG_CLASS_SHIFT) & BWD_SEG_CLASS_MASK;
    const u16 coefficient_index = (header >> BWD_SEG_COEFFICIENT_SHIFT) & BWD_SEG_COEFFICIENT_MASK;
    const u16 source_a = desc.program[pc + 1];
    const u16 source_b = desc.program[pc + 2];
    if constexpr (!IS_R0) {
      // Group headers carry the member count and accumulator-side flags.
      if (term_class == BWD_SEG_EXT_CLASS_GROUP_HEADER) {
        const u16 n_members = source_a;
        const u16 flags = source_b;
        e4 s_c0 = e4::ZERO();
        e4 s_c2 = e4::ZERO();
#pragma unroll 1
        for (u16 member = 0; member < n_members; member++) {
          // Members are contiguous after the header (host lowering deals whole
          // atoms), so the sub-loop advances the WALK's own `pc`: it ends on the
          // LAST member and the outer loop's `pc += BWD_SEG_WORDS_PER_TERM` steps to
          // the record after the group. Nothing else adjusts `pc`.
          pc += BWD_SEG_WORDS_PER_TERM;
          const u16 member_header = desc.program[pc];
          const u16 member_class = (member_header >> BWD_SEG_CLASS_SHIFT) & BWD_SEG_CLASS_MASK;
          // The same thirteen bits a plain record spends on a recipe id are the
          // member's IMMEDIATE id.
          const u16 immediate_id = (member_header >> BWD_SEG_COEFFICIENT_SHIFT) & BWD_SEG_COEFFICIENT_MASK;
          seg_execute_group_member<MAX_DEPTH>(desc, member_class, immediate_id, desc.program[pc + 1], desc.program[pc + 2], row, s_c0, s_c2);
        }
        // ONE uniform bank load for the whole group, the header's core id indexed
        // raw exactly as a term's coefficient id is.
        const e4 core = AB_GKR_BWD_SEG_COEFF(coefficient_index);
        seg_apply_group_core(core, flags, s_c0, s_c2, acc_c0, acc_c2);
        continue;
      }
    }
    seg_execute_term<IS_R0, MAX_DEPTH>(desc, term_class, coefficient_index, source_a, source_b, row, acc_c0, acc_c2);
  }

  seg_epilogue(desc, k, lane, warp_id, row, active, acc_c0, acc_c2);
}

} // namespace airbender::gkr

//
#if !defined(CUDART_VERSION) || CUDART_VERSION < 12040
#error "the segmented VM's register pins require CUDA >= 12.4 (__maxnreg__)"
#endif

EXTERN __global__ void __maxnreg__(40) ab_gkr_bwd_seg_r0_const_epi_plane_kernel(const __grid_constant__ airbender::gkr::bwd_seg_desc desc) {
  airbender::gkr::seg_body<true>(desc);
}

EXTERN __global__ void ab_gkr_bwd_seg_cont_const_epi_plane_kernel(const __grid_constant__ airbender::gkr::bwd_seg_desc desc) {
  airbender::gkr::seg_body<false>(desc);
}

EXTERN __global__ void ab_gkr_bwd_seg_build_fold_weights_kernel(e4 *const fold_weights, const u32 round) {
  airbender::gkr::seg_build_fold_weights(fold_weights, round);
}
