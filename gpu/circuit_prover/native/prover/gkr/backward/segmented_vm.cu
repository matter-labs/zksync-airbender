// SEGMENTED lean VM executor (segmented-lean-VM design sections 3, 4, 6, 7).
//
// One launch per (layer, round). A block is K warps by 32 lanes, a lane IS a row
// of the block's 32-row tile, and the grid covers `rows / 32` tiles. Two phases
// inside one kernel:
//
//   1. the JAOT FOLD PROLOGUE — warps stripe over `desc.fold_source`, each
//      folding this block's 32-row slice of one source down to the current round
//      and storing BOTH endpoint halves to that source's publish backing (the
//      prologue is the publisher);
//   2. one `__syncthreads()`; then
//   3. SEGMENTED EVAL — warp `w` walks `program[list_offset[w] ..
//      list_offset[w + 1]]`, decoding fixed-width header-first records and
//      accumulating a per-warp `(acc_c0, acc_c2)` partial in registers.
//
// The cross-warp reduction, the eq weight and the contribution store are the
// epilogue's, in one of three shapes (`bwd_seg_epilogue`); warp 0 applies eq ONCE
// to the consolidated row, never per partial.
//
// What is deliberately absent, and must stay absent: a cell file, residency
// modes, a fold-capable load path inside the term loop, a +-1 coefficient fast
// path (RR ruling 2026-07-27: the bank materializes both reserved literals at
// its head and every coefficient is one uniform `bank[coeff_idx]` load), and any
// validation in a release kernel.
//
// FOLD WEIGHTS come from a PRELUDE, not from the term loop. The flat fold weighs
// each of a delta-step catch-up's `2^delta` endpoints by a product of
// claim-point challenges, so those products are built once per round by
// `ab_gkr_bwd_seg_build_fold_weights_kernel` into `ab_gkr_bwd_seg_fold_weights`
// — writing through the symbol's own device address, the only way device code
// can store to a `__constant__`. That launch is continuation-only (round 0 has
// no challenges and no folds) and stays OUTSIDE the term loop: the prelude is
// the bank's only writer, and no executor kernel ever builds a weight.
//
// ENDPOINT LAYOUT. A source at target depth is `2 * logical_rows` values with the
// two endpoints in SPLIT HALVES: `s0 = V[row]`, `s1 = V[rows + row]`. That is the
// incumbent production layout (`flat_cont_fold_and_load` reads `index` and
// `fold_stride + index`), and every fold, read and publish here inherits it.
//
// CHALLENGE INDEXING. A fold level that lifts depth `d` to depth `d + 1` weights
// with `ab_gkr_main_layer_claim_point[d]`, so a delta-step catch-up at round `r`
// consumes indices `[r - delta, r)` — front-indexed, exactly what the incumbent
// does (`launch_round3_kernels_from_symbol` passes `folding_challenge_slot =
// step - 1`, and round 1 folds with `claim_point[0]`), and exactly what host
// lowering assumes when it requires `claim_point.len() >= round`
// (`BwdSegLowerError::ClaimPointTooShort`).
//
// CACHE HINTS (the incumbent discipline, `continuation.cuh:82-92`): the
// prologue's PRE-FOLD raw reads use `ld.cs` — those values are dead for this
// launch once folded — its publish stores use `st.wb`, and every EVAL read uses
// `ld.ca`, including the raw base-field reads of an inline fold, which exist
// precisely to be re-read across terms.

#include "segmented_vm.cuh"

__device__ __constant__ e4 ab_gkr_bwd_seg_coeff_bank[airbender::prover::gkr::BWD_SEG_CONST_BANK];

__device__ __constant__ e4 ab_gkr_bwd_seg_fold_weights[airbender::prover::gkr::BWD_SEG_FOLD_WEIGHT_SLOTS];

namespace airbender::prover::gkr {

// ── Coefficient loaders (section 4) ─────────────────────────────────────────
//
// The bank is selected launch-wide; no term carries an address-space tag. Both
// loaders index RAW with the wire's thirteen-bit id: the payload is
// reserved-inclusive (`[ONE, NEG_ONE, recipes...]`), so there is no reserved-index
// branch and no offset subtraction anywhere on this path.

// Reads this lineage's own `__constant__` bank. Direct symbol access is required
// for LDC emission, so this loader is not templated.
struct seg_coeff_bank_constant {
  DEVICE_FORCEINLINE e4 operator[](const u16 index) const { return ::ab_gkr_bwd_seg_coeff_bank[index]; }
};

// Reads the descriptor's coefficient pointer. The constant specialization ignores
// that pointer entirely.
struct seg_coeff_bank_pointer {
  const e4 *base;
  DEVICE_FORCEINLINE e4 operator[](const u16 index) const { return load<e4, ld_modifier::ca>(base, index); }
};

// ── Program sources (section 5) ─────────────────────────────────────────────
//
// The inline accessor indexes the `__grid_constant__` member ARRAY rather than a
// pointer into it, which is what keeps the access in parameter space.

template <typename Desc> struct seg_program_inline {
  const Desc &desc;
  DEVICE_FORCEINLINE u16 word(const u32 pc) const { return desc.program[pc]; }
};

// A plain indexed read, not a hinted `load<>`: the hinted family's payload unit is
// four bytes or wider (`load_unit`), so a u16 has no hinted form at all. The
// default global load caches in L1, which is the hint this stream would ask for
// anyway. Widening the record to one 8-byte vector load would add a host-side
// alignment obligation to a spike-only path, so it is left to whatever the A/B
// finds worth measuring.
struct seg_program_devptr {
  const u16 *words;
  DEVICE_FORCEINLINE u16 word(const u32 pc) const { return words[pc]; }
};

// ── Window addressing ───────────────────────────────────────────────────────
//
// A bound coordinate resolves to `base + column * stride_bytes`; `*_base` already
// points at the window's first column. `bwd_coeff_source_window` keeps its name
// from the retired cell-era lineage it was rehomed out of; there is one backward
// coefficient-ISA executor now, and these helpers are its only window addressing.
// (The incumbent FLAT lineage is a separate thing entirely and does not use them.)

DEVICE_FORCEINLINE const bf *seg_read_bf_column(const bwd_coeff_source_window &window, const u32 column) {
  return reinterpret_cast<const bf *>(window.read_base + static_cast<size_t>(column) * window.read_stride_bytes);
}

DEVICE_FORCEINLINE const e4 *seg_read_e4_column(const bwd_coeff_source_window &window, const u32 column) {
  return reinterpret_cast<const e4 *>(window.read_base + static_cast<size_t>(column) * window.read_stride_bytes);
}

DEVICE_FORCEINLINE e4 *seg_publish_column(const bwd_coeff_source_window &window, const u32 column) {
  return reinterpret_cast<e4 *>(window.publish_base + static_cast<size_t>(column) * window.publish_stride_bytes);
}

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

// ── Fold-weight prelude (flat fold, spec 2026-07-28) ────────────────────────

// One thread builds one slot. Challenges come from the claim-point constant —
// the round's update is stream-ordered before this launch — and the store
// permutation here is the ONLY place the physical-order convention exists.
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
    const u32 bit = (q >> (delta - 1 - j)) & 1;
    w = e4::mul(w, bit != 0 ? c : e4::sub(one, c));
  }
  fold_weights[slot] = w;
}

// ── The flat fold (spec 2026-07-28 §3, §5.1) ────────────────────────────────
//
// A depth-DELTA fold is a dot product over its 2^DELTA physical leaves with
// challenge-only weights; the Lagrange weights sum to ONE exactly, so it is
// evaluated in DIFFERENCE form with the q = 0 coefficient identically 1:
//
//   fold(base) = leaf0 + sum_{q>=1} w_q * (raw(base + q*span) - leaf0)
//
// One accumulator, one common subtrahend, 2^DELTA - 1 mixed fmas, no interior
// e4 x e4 nodes. Leaf `q` sits at `index + q * span`: the SPLIT-HALVES layout,
// not an interleaving, with `span` the target-depth stride (`2 * rows`, both
// endpoint halves). The weights live in `ab_gkr_bwd_seg_fold_weights` in
// PHYSICAL-offset order — the bit reversal is baked into the prelude's store
// permutation (`seg_build_fold_weights`), so this loop walks q monotonically and
// has no ordering convention left to violate; the truth-table pin and the parity
// ladder are the authority. At DELTA == 1 this is instruction-for-instruction the
// affine `fma(r, f1 - f0, f0)` form, for e4 chain leaves too.
//
// HISTORICAL: the recursive pyramid this replaced (and its stride/challenge
// pairing derivation) is in git history under `seg_fold_level`.
template <u32 DELTA, typename Raw> DEVICE_FORCEINLINE e4 seg_fold_flat(const Raw &raw, const u32 index, const u32 span) {
  static_assert(DELTA >= 1 && DELTA <= BWD_SEG_MAX_FOLD_DEPTH, "fold outside 1..BWD_SEG_MAX_FOLD_DEPTH");
  constexpr u32 BASE = DELTA == 1 ? BWD_SEG_FOLD_WEIGHT_BASE_D1 : DELTA == 2 ? BWD_SEG_FOLD_WEIGHT_BASE_D2 : BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const auto leaf0 = raw(index);
  e4 acc = seg_lift(leaf0);
  // ROLLED deliberately, and measured: fully unrolled, all `2^DELTA - 1` leaves and
  // their weights are live at once and the continuation executors allocate 72
  // registers — above the 64 per thread a 1024-thread block gets, which makes
  // `K = 32` unlaunchable. One leaf per trip holds the band to 50-64, so the
  // continuation family reaches the `K` geometry cap
  // (`bwd_seg_k_ceiling_is_measured_not_assumed` pins that reach over the executor
  // symbols it probes; the band's 64-end is arithmetic rather than a launch that pin
  // confirms, since the AccPlacement rungs sit outside its probed set). The trip
  // count is 1, 3 or 7, and the weight stays a uniform constant-bank broadcast.
  // The roll is not free on the clock: at DELTA == 3 with `K = 24` — one block per
  // SM, so the 7-trip chain has no co-resident work to hide its latency behind — it
  // costs 13-66%, which buys `K = 32` plus the `K = 16` two-block occupancy step and
  // so does not justify restoring the blanket unroll; a per-depth loop form (rolled
  // at DELTA <= 2, unrolled at 3) is an open follow-up.
#pragma unroll 1
  for (u32 q = 1; q < (1u << DELTA); q++) {
    const e4 w = ::ab_gkr_bwd_seg_fold_weights[BASE + q - 1];
    acc = e4::fma(w, decltype(leaf0)::sub(raw(index + q * span), leaf0), acc);
  }
  return acc;
}

// One target-depth value out of a backing `delta` folds behind it.
//
// `MAX_DEPTH` is the deepest fold this call site can need — 3 in the prologue,
// `BWD_SEG_MAX_INLINE_FOLD_DEPTH` in the eval loop (the assignment matrix
// publishes at depth 3 instead of inlining it), 0 at R0 (depth 0 everywhere) — so
// no site compiles a fold it cannot execute.
template <u32 MAX_DEPTH, typename Raw> DEVICE_FORCEINLINE e4 seg_fold(const Raw &raw, const u32 index, const u32 span, const u32 delta) {
  if constexpr (MAX_DEPTH >= 3) {
    if (delta == 3)
      return seg_fold_flat<3>(raw, index, span);
  }
  if constexpr (MAX_DEPTH >= 2) {
    if (delta == 2)
      return seg_fold_flat<2>(raw, index, span);
  }
  if constexpr (MAX_DEPTH >= 1) {
    if (delta == 1)
      return seg_fold_flat<1>(raw, index, span);
  }
  // `delta == 0`: the backing IS at target depth. A delta past `MAX_DEPTH` cannot
  // arrive — `lower_bwd_seg` rejects one (`UnsupportedFoldDelta`, `InvalidDepths`)
  // and `assign_class` is what pairs a class with its depth — and a release
  // kernel has no error channel, so it resolves as depth zero rather than reading
  // an undefined shape.
  return seg_lift(raw(index));
}

// Both target-depth endpoints of one folded source in ONE pass over q: same
// loads as two seg_fold_flat calls, each weight consumed once, two
// independent fma chains for ILP. This is also the prologue's shape — fold
// then publish both halves — so it is written once here.
template <u32 DELTA, typename Raw>
DEVICE_FORCEINLINE void seg_fold_endpoints_flat(const Raw &raw, const u32 row, const u32 rows, const u32 span, e4 &s0, e4 &s1) {
  static_assert(DELTA >= 1 && DELTA <= BWD_SEG_MAX_FOLD_DEPTH, "fold outside 1..BWD_SEG_MAX_FOLD_DEPTH");
  constexpr u32 BASE = DELTA == 1 ? BWD_SEG_FOLD_WEIGHT_BASE_D1 : DELTA == 2 ? BWD_SEG_FOLD_WEIGHT_BASE_D2 : BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const auto leaf0_lo = raw(row);
  const auto leaf0_hi = raw(rows + row);
  s0 = seg_lift(leaf0_lo);
  s1 = seg_lift(leaf0_hi);
  // Rolled for the register reason `seg_fold_flat` spells out — more so here: two
  // chains would double the live leaf set an unroll keeps resident.
#pragma unroll 1
  for (u32 q = 1; q < (1u << DELTA); q++) {
    const e4 w = ::ab_gkr_bwd_seg_fold_weights[BASE + q - 1];
    s0 = e4::fma(w, decltype(leaf0_lo)::sub(raw(row + q * span), leaf0_lo), s0);
    s1 = e4::fma(w, decltype(leaf0_hi)::sub(raw(rows + row + q * span), leaf0_hi), s1);
  }
}

template <u32 MAX_DEPTH, typename Raw>
DEVICE_FORCEINLINE void seg_fold_endpoints(const Raw &raw, const u32 row, const u32 rows, const u32 span, const u32 delta, e4 &s0, e4 &s1) {
  if constexpr (MAX_DEPTH >= 3)
    if (delta == 3)
      return seg_fold_endpoints_flat<3>(raw, row, rows, span, s0, s1);
  if constexpr (MAX_DEPTH >= 2)
    if (delta == 2)
      return seg_fold_endpoints_flat<2>(raw, row, rows, span, s0, s1);
  if constexpr (MAX_DEPTH >= 1)
    if (delta == 1)
      return seg_fold_endpoints_flat<1>(raw, row, rows, span, s0, s1);
  s0 = seg_lift(raw(row));
  s1 = seg_lift(raw(rows + row));
}

// The Delta projection of a folded source, folding the DIFFERENCE leaves
// d_q = raw(hi) - raw(lo) directly: they are a valid leaf set and the weights
// sum to one, so the same difference form applies with ONE accumulator.
template <u32 DELTA, typename Raw> DEVICE_FORCEINLINE e4 seg_fold_delta_flat(const Raw &raw, const u32 row, const u32 rows, const u32 span) {
  static_assert(DELTA >= 1 && DELTA <= BWD_SEG_MAX_FOLD_DEPTH, "fold outside 1..BWD_SEG_MAX_FOLD_DEPTH");
  constexpr u32 BASE = DELTA == 1 ? BWD_SEG_FOLD_WEIGHT_BASE_D1 : DELTA == 2 ? BWD_SEG_FOLD_WEIGHT_BASE_D2 : BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const auto d0 = decltype(raw(0))::sub(raw(rows + row), raw(row));
  e4 acc = seg_lift(d0);
  // Rolled for the register reason `seg_fold_flat` spells out.
#pragma unroll 1
  for (u32 q = 1; q < (1u << DELTA); q++) {
    const e4 w = ::ab_gkr_bwd_seg_fold_weights[BASE + q - 1];
    const auto dq = decltype(d0)::sub(raw(rows + row + q * span), raw(row + q * span));
    acc = e4::fma(w, decltype(d0)::sub(dq, d0), acc);
  }
  return acc;
}

template <u32 MAX_DEPTH, typename Raw> DEVICE_FORCEINLINE e4 seg_fold_delta(const Raw &raw, const u32 row, const u32 rows, const u32 span, const u32 delta) {
  if constexpr (MAX_DEPTH >= 3)
    if (delta == 3)
      return seg_fold_delta_flat<3>(raw, row, rows, span);
  if constexpr (MAX_DEPTH >= 2)
    if (delta == 2)
      return seg_fold_delta_flat<2>(raw, row, rows, span);
  if constexpr (MAX_DEPTH >= 1)
    if (delta == 1)
      return seg_fold_delta_flat<1>(raw, row, rows, span);
  return e4::sub(seg_lift(raw(rows + row)), seg_lift(raw(row)));
}

// ── Projections (section 4) ─────────────────────────────────────────────────

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

// Resolve only the halves the projection needs: an Endpoint0 use reads ONE half.
// The unused half is returned as zero rather than left undefined; every caller is
// fully inlined, so the dead half costs nothing.
template <seg_projection P, typename Value> DEVICE_FORCEINLINE auto seg_project(const Value &value, const u32 row, const u32 rows) {
  using T = decltype(value(row));
  if constexpr (P == SEG_PROJ_ENDPOINT0) {
    return seg_value<T>{value(row), T::ZERO()};
  } else {
    const T s0 = value(row);
    const T s1 = value(rows + row);
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
template <seg_projection P, u32 MAX_DEPTH, typename Raw>
DEVICE_FORCEINLINE seg_value<e4> seg_project_folded(const Raw &raw, const u32 row, const u32 rows, const u32 span, const u32 delta) {
  if constexpr (P == SEG_PROJ_ENDPOINT0) {
    return seg_value<e4>{seg_fold<MAX_DEPTH>(raw, row, span, delta), e4::ZERO()};
  } else if constexpr (P == SEG_PROJ_DELTA) {
    return seg_value<e4>{e4::ZERO(), seg_fold_delta<MAX_DEPTH>(raw, row, rows, span, delta)};
  } else {
    e4 s0;
    e4 s1;
    seg_fold_endpoints<MAX_DEPTH>(raw, row, rows, span, delta, s0, s1);
    return seg_value<e4>{s0, e4::sub(s1, s0)};
  }
}

// ── Operand resolution (section 4) ──────────────────────────────────────────

// A BASE-FIELD operand, at the projection its class implies.
//
// R0 only, and no fold path: R0 is round zero, so every window is AT target depth
// (`assign_class(BF, 0) == BfDirect`), and a base-field read at a nonzero depth is
// a host rejection (`BwdSegLowerError::BaseReadAtFoldedDepth`) precisely because a
// folded value is E4. So a BF operand costs four bytes of traffic and a base-field
// subtract — never a lift.
//
// That the operand behind a BF term class really is base-field-resolved is an
// ENCODER invariant, not a validated one (`lean::validate_program`'s doc says so:
// it checks well-formedness, and operand widths are pinned by
// `a_mixed_product_puts_the_bf_factor_first`). This resolver trusts it.
template <seg_projection P, typename Desc> DEVICE_FORCEINLINE seg_value<bf> seg_resolve_bf(const Desc &desc, const u16 slot, const u32 row, const u32 rows) {
  const bwd_seg_source_record record = desc.source[slot];
  const bwd_coeff_source_window &window = desc.window[record.window];
  if (record.source_class == BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE)
    return seg_project<P>(seg_raw_synthesized{bwd_coeff_procedural_source_kind(window.procedural_kind)}, row, rows);
  return seg_project<P>(seg_raw_bf_column<ld_modifier::ca>{seg_read_bf_column(window, record.column)}, row, rows);
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
//   ProceduralInline  the same fold over row synthesis; no DRAM read at all.
//   BfDirect          depth zero, so the lift. Reachable only at R0 (see
//                     `seg_resolve_bf`), where `MAX_DEPTH` is zero anyway.
template <seg_projection P, u32 MAX_DEPTH, typename Desc>
DEVICE_FORCEINLINE seg_value<e4> seg_resolve_e4(const Desc &desc, const u16 slot, const u32 row, const u32 rows) {
  const bwd_seg_source_record record = desc.source[slot];
  const bwd_coeff_source_window &window = desc.window[record.window];
  if (record.source_class == BWD_SEG_SOURCE_CLASS_E4_DIRECT) {
    const e4 *column = window.materialize != 0 ? seg_publish_column(window, record.column) : seg_read_e4_column(window, record.column);
    return seg_project<P>(seg_raw_e4_column<ld_modifier::ca>{column}, row, rows);
  }
  const u32 span = rows << 1;
  const u32 delta = u32{window.target_depth} - u32{window.backing_depth};
  if (record.source_class == BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE) {
    const seg_raw_synthesized raw{bwd_coeff_procedural_source_kind(window.procedural_kind)};
    return seg_project_folded<P, MAX_DEPTH>(raw, row, rows, span, delta);
  }
  const seg_raw_bf_column<ld_modifier::ca> raw{seg_read_bf_column(window, record.column)};
  return seg_project_folded<P, MAX_DEPTH>(raw, row, rows, span, delta);
}

// ── The JAOT fold prologue (section 3) ──────────────────────────────────────

// Fold ONE source's 32-row slice down to the current round and publish both
// endpoint halves.
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
template <typename Desc> DEVICE_FORCEINLINE void seg_fold_and_publish(const Desc &desc, const u16 slot, const u32 row, const u32 rows, const bool active) {
  const bwd_seg_source_record record = desc.source[slot];
  const bwd_coeff_source_window &window = desc.window[record.window];
  const u32 span = rows << 1;
  const u32 delta = u32{window.target_depth} - u32{window.backing_depth};

  e4 s0;
  e4 s1;
  if (window.origin == BWD_COEFF_ORIGIN_READ_EXT) {
    const seg_raw_e4_column<ld_modifier::cs> raw{seg_read_e4_column(window, record.column)};
    seg_fold_endpoints<BWD_SEG_MAX_FOLD_DEPTH>(raw, row, rows, span, delta, s0, s1);
  } else if (window.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
    const seg_raw_synthesized raw{bwd_coeff_procedural_source_kind(window.procedural_kind)};
    seg_fold_endpoints<BWD_SEG_MAX_FOLD_DEPTH>(raw, row, rows, span, delta, s0, s1);
  } else {
    const seg_raw_bf_column<ld_modifier::cs> raw{seg_read_bf_column(window, record.column)};
    seg_fold_endpoints<BWD_SEG_MAX_FOLD_DEPTH>(raw, row, rows, span, delta, s0, s1);
  }

  // Only a live row publishes. A dead lane of the last tile folded a CLAMPED row
  // (see `seg_body`), and letting it store would write a duplicate of another
  // lane's value.
  if (!active)
    return;
  e4 *publish = seg_publish_column(window, record.column);
  // Blocks own disjoint row ranges and exactly one warp folds a given source, so
  // both stores have a single writer. `wb` keeps them in L1 for the eval loop's
  // same-block `ld.ca` re-reads.
  store<e4, st_modifier::wb>(publish, s0, row);
  store<e4, st_modifier::wb>(publish, s1, rows + row);
}

// ── The seed and the contribution store (section 3) ─────────────────────────

// The `acc_c0` seed, reinterpreted rather than converted: the descriptor carries
// the value's IN-MEMORY (Montgomery) limbs, i.e. exactly the bytes a device load
// of an `e4` would have seen, so the seed path needs no bank lookup.
//
// Spelled limb by limb rather than as a 16-byte reinterpret_cast because `c_init`
// is only 8-byte aligned in the progptr twin, where a vector load would be
// misaligned.
template <typename Desc> DEVICE_FORCEINLINE e4 seg_c_init(const Desc &desc) {
  return e4(e2(bf::from_reduced_raw_repr(desc.c_init[0]), bf::from_reduced_raw_repr(desc.c_init[1])),
            e2(bf::from_reduced_raw_repr(desc.c_init[2]), bf::from_reduced_raw_repr(desc.c_init[3])));
}

// Warp 0's one write per row: eq applied ONCE to the consolidated pair, then the
// incumbent contribution layout — `acc_c0 * eq` in `[0, rows)` and `acc_c2 * eq`
// in `[rows, 2 * rows)`.
template <typename Desc> DEVICE_FORCEINLINE void seg_store_row(const Desc &desc, const u32 row, const bool active, const e4 &sum_c0, const e4 &sum_c2) {
  if (!active)
    return;
  // `lower_bwd_seg` rejects a null `contributions` or `eq_low`
  // (`BwdSegLowerError::NullRuntimePointer`), so this is defence in depth against
  // a hand-built descriptor, NOT a supported "evaluate but do not store" mode.
  // Silently producing nothing is the safest response a release kernel can give:
  // it has no error channel.
  if (desc.contributions == nullptr || desc.eq_low == nullptr)
    return;
  const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, row);
  store<e4, st_modifier::cs>(desc.contributions, e4::mul(sum_c0, eq), row);
  store<e4, st_modifier::cs>(desc.contributions + desc.logical_rows, e4::mul(sum_c2, eq), row);
}

// ── Epilogues (section 3) ───────────────────────────────────────────────────

// Reduce the `k` per-warp partials of this lane's row into warp 0 and store.
//
// Field addition is exact and associative, so every shape below — and every `K` —
// produces bit-identical sums. That is what makes `K` a pure performance axis and
// lets the CPU oracle be the parity reference at any `K`.
template <u32 EPILOGUE, typename Desc>
DEVICE_FORCEINLINE void seg_epilogue(const Desc &desc, const u32 k, const u32 lane, const u32 warp_id, const u32 row, const bool active, const e4 &part_c0,
                                     const e4 &part_c2) {
  // The plane pair lives in DYNAMIC shared memory because `K` is a launch
  // parameter, so no static declaration could size it;
  // `bwd_seg_epilogue_smem_bytes` (mirrored in the Rust launcher) is the number of
  // bytes the launch must pass, and this is the only declaration of the array.
  extern __shared__ e4 ab_gkr_bwd_seg_plane[];

  // `k` is descriptor metadata, so this is block-uniform: at K == 1 warp 0's
  // register partials ARE the block result — no shared memory and no barrier.
  if (k == 1) {
    seg_store_row(desc, row, active, part_c0, part_c2);
    return;
  }

  if constexpr (EPILOGUE == BWD_SEG_EPILOGUE_STAGED) {
    // Serial read-modify-write through ONE plane pair, K - 1 barriers total.
    //
    // Warp 1 BOOTSTRAPS by storing rather than accumulating, so no warp ever
    // reads an uninitialized plane; from there the reader of each barrier is the
    // next writer, so consecutive RMWs are separated by exactly one barrier. A
    // produce-then-consume staging (every warp stores, warp 0 sums) is the shape
    // that would need 2 * (K - 1) barriers to be race-free.
    e4 *plane_c0 = ab_gkr_bwd_seg_plane;
    e4 *plane_c2 = ab_gkr_bwd_seg_plane + BWD_SEG_WARP_LANES;
    if (warp_id == 1) {
      plane_c0[lane] = part_c0;
      plane_c2[lane] = part_c2;
    }
    __syncthreads();
    for (u32 w = 2; w < k; w++) {
      if (warp_id == w) {
        plane_c0[lane] = e4::add(plane_c0[lane], part_c0);
        plane_c2[lane] = e4::add(plane_c2[lane], part_c2);
      }
      __syncthreads();
    }
    if (warp_id == 0)
      seg_store_row(desc, row, active, e4::add(part_c0, plane_c0[lane]), e4::add(part_c2, plane_c2[lane]));
    return;
  }

  if constexpr (EPILOGUE == BWD_SEG_EPILOGUE_PLANE) {
    // The incumbent shape (`flat_store_unified_contributions`): one `[K - 1][32]`
    // plane, REUSED for c0 and then c2, three barriers.
    e4 *plane = ab_gkr_bwd_seg_plane;
    // Warp 0 owns no plane row, so its `warp_id - 1` wraps. Every USE is inside a
    // `warp_id != 0` guard, which makes the wrap dead arithmetic rather than an
    // address.
    const u32 slot = (warp_id - 1) * BWD_SEG_WARP_LANES + lane;
    if (warp_id != 0)
      plane[slot] = part_c0;
    __syncthreads();
    e4 sum_c0 = part_c0;
    if (warp_id == 0)
      for (u32 w = 0; w < k - 1; w++)
        sum_c0 = e4::add(sum_c0, plane[w * BWD_SEG_WARP_LANES + lane]);
    // Separates warp 0's reads of the c0 plane from the c2 stores that overwrite
    // it.
    __syncthreads();
    if (warp_id != 0)
      plane[slot] = part_c2;
    __syncthreads();
    if (warp_id == 0) {
      e4 sum_c2 = part_c2;
      for (u32 w = 0; w < k - 1; w++)
        sum_c2 = e4::add(sum_c2, plane[w * BWD_SEG_WARP_LANES + lane]);
      seg_store_row(desc, row, active, sum_c0, sum_c2);
    }
    return;
  }

  // BWD_SEG_EPILOGUE_WIDE: both planes at once, ONE barrier, twice the carveout.
  e4 *plane_c0 = ab_gkr_bwd_seg_plane;
  e4 *plane_c2 = ab_gkr_bwd_seg_plane + (k - 1) * BWD_SEG_WARP_LANES;
  // See the plane variant: warp 0's `warp_id - 1` wraps and is never used as an
  // address.
  const u32 slot = (warp_id - 1) * BWD_SEG_WARP_LANES + lane;
  if (warp_id != 0) {
    plane_c0[slot] = part_c0;
    plane_c2[slot] = part_c2;
  }
  __syncthreads();
  if (warp_id == 0) {
    e4 sum_c0 = part_c0;
    e4 sum_c2 = part_c2;
    for (u32 w = 0; w < k - 1; w++) {
      const u32 read = w * BWD_SEG_WARP_LANES + lane;
      sum_c0 = e4::add(sum_c0, plane_c0[read]);
      sum_c2 = e4::add(sum_c2, plane_c2[read]);
    }
    seg_store_row(desc, row, active, sum_c0, sum_c2);
  }
}

// ── One term (sections 3, 4) ────────────────────────────────────────────────

// A squared product (`source_a == source_b`) is resolved TWICE and not tested for.
// In the cell-era ISA the squared rule was a SAFETY property — re-executing the
// second record would re-run its residency actions — and here there is no resident
// state, so the two resolutions are simply equal. The branch that would save one
// of them costs registers in the hot loop for a saving nothing has measured, and
// the CPU oracle resolves twice as well.
template <bool IS_R0, u32 MAX_DEPTH, typename Desc, typename Bank>
DEVICE_FORCEINLINE void seg_execute_term(const Desc &desc, const Bank &bank, const u16 term_class, const u16 coefficient_index, const u16 source_a,
                                         const u16 source_b, const u32 row, const u32 rows, e4 &acc_c0, e4 &acc_c2) {
  // ONE uniform bank load per term: the reserved literals are materialized at the
  // bank head, so there is no branch and no offset here (RR ruling 2026-07-27).
  const e4 coefficient = bank[coefficient_index];
  if constexpr (IS_R0) {
    switch (term_class) {
    case BWD_SEG_R0_CLASS_C0_LINEAR_BF: {
      const bf a = seg_resolve_bf<SEG_PROJ_ENDPOINT0>(desc, source_a, row, rows).endpoint0;
      // `e4::fma(e4, bf, e4)` is four fused `bf::fma`s: a base-field operand never
      // gets lifted just to be multiplied.
      acc_c0 = e4::fma(coefficient, a, acc_c0);
      break;
    }
    case BWD_SEG_R0_CLASS_C0_LINEAR_E4: {
      const e4 a = seg_resolve_e4<SEG_PROJ_ENDPOINT0, MAX_DEPTH>(desc, source_a, row, rows).endpoint0;
      acc_c0 = e4::fma(coefficient, a, acc_c0);
      break;
    }
    case BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF: {
      const bf a = seg_resolve_bf<SEG_PROJ_DELTA>(desc, source_a, row, rows).delta;
      const bf b = seg_resolve_bf<SEG_PROJ_DELTA>(desc, source_b, row, rows).delta;
      acc_c2 = e4::fma(coefficient, bf::mul(a, b), acc_c2);
      break;
    }
    case BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4: {
      // The wire normalizes a mixed product to BF-FIRST, so `source_a` is always
      // the base-field factor (an encoder invariant, pinned by
      // `a_mixed_product_puts_the_bf_factor_first`).
      const bf a = seg_resolve_bf<SEG_PROJ_DELTA>(desc, source_a, row, rows).delta;
      const e4 b = seg_resolve_e4<SEG_PROJ_DELTA, MAX_DEPTH>(desc, source_b, row, rows).delta;
      acc_c2 = e4::fma(coefficient, e4::mul(b, a), acc_c2);
      break;
    }
    case BWD_SEG_R0_CLASS_C2_PRODUCT_E4_E4: {
      const e4 a = seg_resolve_e4<SEG_PROJ_DELTA, MAX_DEPTH>(desc, source_a, row, rows).delta;
      const e4 b = seg_resolve_e4<SEG_PROJ_DELTA, MAX_DEPTH>(desc, source_b, row, rows).delta;
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
    const e4 a = seg_resolve_e4<SEG_PROJ_ENDPOINT0, MAX_DEPTH>(desc, source_a, row, rows).endpoint0;
    acc_c0 = e4::fma(coefficient, a, acc_c0);
    break;
  }
  case BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4: {
    // ONE coefficient and ONE pair resolution per factor feed BOTH accumulators;
    // splitting this into a C0 and a C2 term would resolve every endpoint twice,
    // which is the whole reason the class is native.
    const seg_value<e4> a = seg_resolve_e4<SEG_PROJ_PAIR, MAX_DEPTH>(desc, source_a, row, rows);
    const seg_value<e4> b = seg_resolve_e4<SEG_PROJ_PAIR, MAX_DEPTH>(desc, source_b, row, rows);
    acc_c0 = e4::fma(coefficient, e4::mul(a.endpoint0, b.endpoint0), acc_c0);
    acc_c2 = e4::fma(coefficient, e4::mul(a.delta, b.delta), acc_c2);
    break;
  }
  default:
    break;
  }
}

// ── AccPlacement: one accumulator in shared memory (section 6's ladder) ─────

// A per-thread accumulator slot in the dynamic shared-memory carveout, in the
// conflict-free `[word][lane]` layout `bwd_seg_acc_smem_bytes` sizes.
//
// Word `w` of thread `t` sits at `words[w * threads + t]`, so a warp's 32 lanes
// touch 32 CONSECUTIVE 4-byte banks in each of the four accesses. The obvious
// `e4`-per-thread layout would give a 16-byte stride and put four lanes on every
// bank — a four-way conflict on every access, which is the cost this placement
// exists to avoid paying on top of the traffic it already adds.
struct seg_acc_slot {
  bf *words;
  u32 threads;
  u32 tid;

  DEVICE_FORCEINLINE e4 load() const {
    const bf c[4] = {words[tid], words[threads + tid], words[2 * threads + tid], words[3 * threads + tid]};
    return e4(c);
  }

  DEVICE_FORCEINLINE void store(const e4 &value) const {
    words[tid] = value.base_coefficient_from_flat_idx(0);
    words[threads + tid] = value.base_coefficient_from_flat_idx(1);
    words[2 * threads + tid] = value.base_coefficient_from_flat_idx(2);
    words[3 * threads + tid] = value.base_coefficient_from_flat_idx(3);
  }
};

// ── The executor body ───────────────────────────────────────────────────────

template <bool IS_R0, u32 EPILOGUE, u32 ACC, typename Desc, typename Bank, typename Program>
DEVICE_FORCEINLINE void seg_body(const Desc &desc, const Bank &bank, const Program &program) {
  static_assert(EPILOGUE <= BWD_SEG_EPILOGUE_WIDE, "unknown epilogue specialization");
  static_assert(ACC <= BWD_SEG_ACC_BOTH_SMEM, "unknown accumulator placement");
  // R0 is depth 0 everywhere: no prologue, and no inline fold either.
  constexpr u32 MAX_DEPTH = IS_R0 ? 0u : BWD_SEG_MAX_INLINE_FOLD_DEPTH;

  const u32 rows = desc.logical_rows;
  // Block-uniform and ahead of every barrier. `lower_bwd_seg` rejects a zero row
  // count (`BwdSegLowerError::RowsOutOfRange`); this keeps the clamp below from
  // underflowing on a hand-built descriptor.
  if (rows == 0)
    return;
  const u32 k = desc.k;
  const u32 lane = threadIdx.x & BWD_SEG_LANE_INDEX_MASK;
  const u32 warp_id = threadIdx.x >> BWD_SEG_WARP_SHIFT;
  const u32 tile_row = blockIdx.x * BWD_SEG_WARP_LANES + lane;
  // The last tile can be partial. A dead lane is CLAMPED onto the last live row
  // instead of returning, which keeps every `__syncthreads()` below block-uniform
  // — the incumbent `warp_split` kernels return from dead lanes instead and are
  // safe only because their row counts are whole tiles. A clamped lane reads
  // in-bounds, reduces into its own lane's plane slot, and stores nothing.
  const bool active = tile_row < rows;
  const u32 row = active ? tile_row : rows - 1;

  if constexpr (!IS_R0) {
    // Phase 1. Warps stripe over the fold list in the order the host committed
    // (section 7: earliest-eval-first-use sources fold LAST, so they are warmest
    // in L1 when eval starts).
    for (u32 s = warp_id; s < u32{desc.num_foldable}; s += k)
      seg_fold_and_publish(desc, desc.fold_source[s], row, rows, active);
    // THE fold -> eval barrier, and the only one outside the epilogue. It is also
    // the release of the publish stores: warp `w` reads at its own lane a value
    // another warp of this block wrote, and both live in this SM's L1.
    __syncthreads();
  }

  // Phase 2. Exactly ONE partial may carry the seed: `k` seeded partials would
  // reduce to `k * c_init`. R0 has no seed path at all — R0 lowering drops the
  // spine's scalar addends, so seeding one would double-count it (enforced by
  // `lower_bwd_seg`'s `R0CarriesCInit`).
  //
  // Under a shared-memory placement the corresponding register below is written
  // once, never read inside the loop, and dead by the time ptxas allocates — which
  // is the whole point of the rung. Its declaration stays unconditional because
  // the epilogue consumes an `e4` either way.
  e4 acc_c0 = e4::ZERO();
  e4 acc_c2 = e4::ZERO();
  const u32 threads = k * BWD_SEG_WARP_LANES;
  seg_acc_slot slot_c0{};
  seg_acc_slot slot_c2{};
  if constexpr (ACC != BWD_SEG_ACC_IN_REGISTERS) {
    // The one dynamic-shared allocation of the launch, re-declared here because
    // `seg_epilogue` declares the same `extern __shared__` array for its planes —
    // both names alias the same block, which is exactly what makes the carveout
    // addressable as "after the planes".
    extern __shared__ e4 ab_gkr_bwd_seg_plane[];
    // The carveout sits AFTER the epilogue's planes in the same dynamic
    // allocation, so the epilogue's own addressing is untouched.
    bf *carveout = reinterpret_cast<bf *>(reinterpret_cast<char *>(ab_gkr_bwd_seg_plane) + bwd_seg_epilogue_smem_bytes(EPILOGUE, k));
    slot_c2 = seg_acc_slot{carveout, threads, threadIdx.x};
    if constexpr (ACC == BWD_SEG_ACC_BOTH_SMEM)
      slot_c0 = seg_acc_slot{carveout + 4 * threads, threads, threadIdx.x};
  }
  if constexpr (!IS_R0) {
    if (warp_id == 0)
      acc_c0 = seg_c_init(desc);
  }
  if constexpr (ACC != BWD_SEG_ACC_IN_REGISTERS)
    slot_c2.store(acc_c2);
  if constexpr (ACC == BWD_SEG_ACC_BOTH_SMEM)
    slot_c0.store(acc_c0);

  // Warp `w` walks its own contiguous list. `blockDim == 32 * k`, so `warp_id < k`
  // and `warp_id + 1` is inside `list_offset`.
  const u32 pc_end = desc.list_offset[warp_id + 1];
  // NOT a concession: the record width is fixed, so the compiler COULD unroll,
  // and duplicating the class switch would raise the register peak this design is
  // measured against for no fewer loads — consecutive terms in a list share
  // nothing the unroll could hoist.
#pragma unroll 1
  for (u32 pc = desc.list_offset[warp_id]; pc < pc_end; pc += BWD_SEG_WORDS_PER_TERM) {
    // Header-first: the class arrives before the words whose meaning it fixes.
    // Both source words are read unconditionally — a one-source class carries
    // `BWD_SEG_SOURCE_NONE` in the second, and the class is what decides whether
    // it is looked at. `word3` is reserved and never read.
    const u16 header = program.word(pc);
    const u16 term_class = (header >> BWD_SEG_CLASS_SHIFT) & BWD_SEG_CLASS_MASK;
    const u16 coefficient_index = (header >> BWD_SEG_COEFFICIENT_SHIFT) & BWD_SEG_COEFFICIENT_MASK;
    const u16 source_a = program.word(pc + 1);
    const u16 source_b = program.word(pc + 2);
    // `seg_execute_term` is placement-BLIND on purpose: the ladder is about where
    // the accumulator LIVES between terms, and wrapping it here keeps the register
    // placement's instruction stream byte-identical to what the fifteen release
    // symbols compile today.
    if constexpr (ACC == BWD_SEG_ACC_IN_REGISTERS) {
      seg_execute_term<IS_R0, MAX_DEPTH>(desc, bank, term_class, coefficient_index, source_a, source_b, row, rows, acc_c0, acc_c2);
    } else if constexpr (ACC == BWD_SEG_ACC_C2_SMEM) {
      e4 live_c2 = slot_c2.load();
      seg_execute_term<IS_R0, MAX_DEPTH>(desc, bank, term_class, coefficient_index, source_a, source_b, row, rows, acc_c0, live_c2);
      slot_c2.store(live_c2);
    } else {
      e4 live_c0 = slot_c0.load();
      e4 live_c2 = slot_c2.load();
      seg_execute_term<IS_R0, MAX_DEPTH>(desc, bank, term_class, coefficient_index, source_a, source_b, row, rows, live_c0, live_c2);
      slot_c0.store(live_c0);
      slot_c2.store(live_c2);
    }
  }

  if constexpr (ACC != BWD_SEG_ACC_IN_REGISTERS) {
    // The eval loop and the epilogue are separated by no barrier, and none is
    // needed: every slot is PRIVATE to its thread, so the read below is of this
    // thread's own last write.
    acc_c2 = slot_c2.load();
    if constexpr (ACC == BWD_SEG_ACC_BOTH_SMEM)
      acc_c0 = slot_c0.load();
  }

  // Phase 3.
  seg_epilogue<EPILOGUE>(desc, k, lane, warp_id, row, active, acc_c0, acc_c2);
}

// ── Specialization wrappers ─────────────────────────────────────────────────

template <bool IS_R0, u32 EPILOGUE, u32 ACC = BWD_SEG_ACC_IN_REGISTERS> DEVICE_FORCEINLINE void seg_body_const_inline(const bwd_seg_desc &desc) {
  seg_body<IS_R0, EPILOGUE, ACC>(desc, seg_coeff_bank_constant{}, seg_program_inline<bwd_seg_desc>{desc});
}

template <bool IS_R0, u32 EPILOGUE> DEVICE_FORCEINLINE void seg_body_ptr_inline(const bwd_seg_desc &desc) {
  seg_body<IS_R0, EPILOGUE, BWD_SEG_ACC_IN_REGISTERS>(desc, seg_coeff_bank_pointer{desc.coefficients}, seg_program_inline<bwd_seg_desc>{desc});
}

template <bool IS_R0, u32 EPILOGUE> DEVICE_FORCEINLINE void seg_body_const_progptr(const bwd_seg_progptr_desc &desc) {
  seg_body<IS_R0, EPILOGUE, BWD_SEG_ACC_IN_REGISTERS>(desc, seg_coeff_bank_constant{}, seg_program_devptr{desc.program});
}

// The Task-9 Stage-B rungs, instantiated ON the Stage-A winner's epilogue and
// coefficient loader only: `plane` + `const`. Every other cell would be a kernel
// with no comparison point, and the ladder's question is whether moving an
// accumulator out of registers pays where the register count is the binding
// occupancy limiter — not whether it pays in general.
template <bool IS_R0> DEVICE_FORCEINLINE void seg_body_const_inline_acc2smem(const bwd_seg_desc &desc) {
  seg_body_const_inline<IS_R0, BWD_SEG_EPILOGUE_PLANE, BWD_SEG_ACC_C2_SMEM>(desc);
}

template <bool IS_R0> DEVICE_FORCEINLINE void seg_body_const_inline_accbothsmem(const bwd_seg_desc &desc) {
  seg_body_const_inline<IS_R0, BWD_SEG_EPILOGUE_PLANE, BWD_SEG_ACC_BOTH_SMEM>(desc);
}

} // namespace airbender::prover::gkr

// The kernel matrix. `__launch_bounds__` is deliberately UNSET: this task records
// the natural register count, and buying blocks with the second argument forces
// spills (section 15).
#define AB_GKR_BWD_SEG_KERNEL(symbol, desc_type, body, is_r0, epilogue)                                                                                        \
  EXTERN __global__ void symbol(const __grid_constant__ airbender::prover::gkr::desc_type desc) {                                                              \
    airbender::prover::gkr::body<is_r0, airbender::prover::gkr::epilogue>(desc);                                                                               \
  }

AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_r0_const_epi_staged_kernel, bwd_seg_desc, seg_body_const_inline, true, BWD_SEG_EPILOGUE_STAGED)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_r0_const_epi_plane_kernel, bwd_seg_desc, seg_body_const_inline, true, BWD_SEG_EPILOGUE_PLANE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_r0_const_epi_wide_kernel, bwd_seg_desc, seg_body_const_inline, true, BWD_SEG_EPILOGUE_WIDE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_r0_ptr_epi_staged_kernel, bwd_seg_desc, seg_body_ptr_inline, true, BWD_SEG_EPILOGUE_STAGED)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_r0_ptr_epi_plane_kernel, bwd_seg_desc, seg_body_ptr_inline, true, BWD_SEG_EPILOGUE_PLANE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_r0_ptr_epi_wide_kernel, bwd_seg_desc, seg_body_ptr_inline, true, BWD_SEG_EPILOGUE_WIDE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_const_epi_staged_kernel, bwd_seg_desc, seg_body_const_inline, false, BWD_SEG_EPILOGUE_STAGED)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_const_epi_plane_kernel, bwd_seg_desc, seg_body_const_inline, false, BWD_SEG_EPILOGUE_PLANE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_const_epi_wide_kernel, bwd_seg_desc, seg_body_const_inline, false, BWD_SEG_EPILOGUE_WIDE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_ptr_epi_staged_kernel, bwd_seg_desc, seg_body_ptr_inline, false, BWD_SEG_EPILOGUE_STAGED)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_ptr_epi_plane_kernel, bwd_seg_desc, seg_body_ptr_inline, false, BWD_SEG_EPILOGUE_PLANE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_ptr_epi_wide_kernel, bwd_seg_desc, seg_body_ptr_inline, false, BWD_SEG_EPILOGUE_WIDE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_const_progptr_epi_staged_kernel, bwd_seg_progptr_desc, seg_body_const_progptr, false, BWD_SEG_EPILOGUE_STAGED)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_const_progptr_epi_plane_kernel, bwd_seg_progptr_desc, seg_body_const_progptr, false, BWD_SEG_EPILOGUE_PLANE)
AB_GKR_BWD_SEG_KERNEL(ab_gkr_bwd_seg_cont_const_progptr_epi_wide_kernel, bwd_seg_progptr_desc, seg_body_const_progptr, false, BWD_SEG_EPILOGUE_WIDE)

#undef AB_GKR_BWD_SEG_KERNEL

// The Stage-B AccPlacement rungs. Separate macro because the placement is baked
// into the wrapper rather than passed as the epilogue axis: these four symbols
// exist to be MEASURED against the four register-placement symbols above with the
// same epilogue and loader, and nothing else may launch them.
#define AB_GKR_BWD_SEG_ACC_KERNEL(symbol, body, is_r0)                                                                                                         \
  EXTERN __global__ void symbol(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc) { airbender::prover::gkr::body<is_r0>(desc); }

AB_GKR_BWD_SEG_ACC_KERNEL(ab_gkr_bwd_seg_r0_const_epi_plane_acc2smem_kernel, seg_body_const_inline_acc2smem, true)
AB_GKR_BWD_SEG_ACC_KERNEL(ab_gkr_bwd_seg_r0_const_epi_plane_accbothsmem_kernel, seg_body_const_inline_accbothsmem, true)
AB_GKR_BWD_SEG_ACC_KERNEL(ab_gkr_bwd_seg_cont_const_epi_plane_acc2smem_kernel, seg_body_const_inline_acc2smem, false)
AB_GKR_BWD_SEG_ACC_KERNEL(ab_gkr_bwd_seg_cont_const_epi_plane_accbothsmem_kernel, seg_body_const_inline_accbothsmem, false)

#undef AB_GKR_BWD_SEG_ACC_KERNEL

// The fold-weight prelude. `fold_weights` is the ab_gkr_bwd_seg_fold_weights
// symbol's own device address — device code cannot name a __constant__ as a
// store target, but writing through its cudaGetSymbolAddress alias between
// launches is this repo's established round-update path (the incumbent's
// round kernels update ab_gkr_main_layer_claim_point the same way).
EXTERN __global__ void ab_gkr_bwd_seg_build_fold_weights_kernel(e4 *const fold_weights, const u32 round) {
  airbender::prover::gkr::seg_build_fold_weights(fold_weights, round);
}
