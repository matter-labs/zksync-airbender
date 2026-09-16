#pragma once
// MAIN R0 window executor with recomputed endpoints: the production body behind the four
// `ab_gkr_r0_recomputed_*` kernels in recomputed.cu.
//
#include "window_geometry.cuh"
#include <type_traits>

namespace airbender::gkr::backward::recomputed {

// Recomputed programs read a layer's inputs instead of materialized roots and carry more records
// than the materialized programs; the retained corpus needs up to 7,940 words (Blake-ext L0 with
// linear tails), so the descriptor program array is 8192 words. Rust mirror:
// `WindowLaunchBinding<8192>` in src/backward/window/binding.rs.
constexpr u32 BWD_WINDOW_RECOMPUTED_PROGRAM_WORDS = 8192;

// Reuse guard: block barriers around the E4 sections keep the nine selector warps of a block
// close in time to improve reuse of shared inputs. Empirical atom-count
// cutoffs shared with the materialized executor, not cache-capacity bounds.
constexpr u32 BWD_WINDOW_RECOMPUTED_REUSE_SCORE = 120;
constexpr u32 BWD_WINDOW_RECOMPUTED_REUSE_SINGLETONS = 16;

struct alignas(BWD_WINDOW_DESC_ALIGN) bwd_window_desc {
  bwd_source_window slot[BWD_WINDOW_ADDR_SLOTS];
  // Production factored-eq low table; high tables stay in `ab_gkr_eq_high`.
  const e4 *eq_low;
  // Row-tile-major 27-cell partial tensor.
  e4 *partials;
  u32 log_rows;
  gkr_eq_sizes eq_sizes;
  // Cumulative instruction endpoints; word 4 carries the shape mask.
  u32 sections[BWD_WINDOW_SECTION_WORDS];
  u16 program[BWD_WINDOW_RECOMPUTED_PROGRAM_WORDS];
  u32 immediates[BWD_WINDOW_MAX_IMMEDIATES];
};
static_assert(sizeof(bwd_window_desc) == 19552, "recomputed bwd_window_desc/WindowLaunchBinding<8192> ABI size drift");
static_assert(alignof(bwd_window_desc) == BWD_WINDOW_DESC_ALIGN, "recomputed bwd_window_desc ABI alignment drift");
static_assert(__builtin_offsetof(bwd_window_desc, slot) == 0, "slot ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, eq_low) == 1024, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, partials) == 1032, "partials ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, log_rows) == 1040, "log_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, eq_sizes) == 1044, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, sections) == 1056, "sections ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, program) == 1120, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_window_desc, immediates) == 17504, "immediates ABI offset drift");
// The kernels take the descriptor by value plus one u32 scalar seed.
static_assert(sizeof(bwd_window_desc) + sizeof(u32) <= BWD_WINDOW_DESC_CAP, "recomputed bwd_window_desc exceeds the __grid_constant__ parameter budget");

DEVICE_FORCEINLINE bwd_window_direct_bf_source bwd_window_direct_bf(const bwd_window_desc &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  const bf *base = reinterpret_cast<const bf *>(address.base);
  return {base + (static_cast<size_t>(bwd_source_lane_column(packed)) << address.log2_stride)};
}

DEVICE_FORCEINLINE bwd_window_direct_e4_source bwd_window_direct_e4(const bwd_window_desc &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  const e4 *base = reinterpret_cast<const e4 *>(address.base);
  return {base + (static_cast<size_t>(bwd_source_lane_column(packed)) << address.log2_stride)};
}

DEVICE_FORCEINLINE void bwd_window_publish(const bwd_window_desc &desc, const u32 row_tile, const u32 lane, const bool active,
                                           const bwd_window_selector_pair selector, const e4 (&values)[3]) {
  const e4 equality = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, active ? row_tile * BWD_WINDOW_ROWS_PER_TILE + lane : 0);
  e4 sums[3];
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    sums[x2] = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    sums[x2] = bwd_window_quartet_shuffle_add(sums[x2], 1);
    sums[x2] = bwd_window_quartet_shuffle_add(sums[x2], 2);
  }
  const u32 role = lane & 3u;
  e4 value = role == 0 ? sums[0] : role == 1 ? sums[1] : role == 2 ? sums[2] : e4::ZERO();
#pragma unroll
  for (u32 mask = 4; mask < BWD_WINDOW_WARP_LANES; mask <<= 1)
    value = bwd_window_quartet_shuffle_add(value, mask);
  if (lane < 3)
    store<e4, st_modifier::cs>(desc.partials, value, static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + 9 * lane + 3 * selector.x1 + selector.x0);
}

// The three tensor cells of a product from the two operands' x2 endpoint pairs: the two Boolean
// cells and the leading (x2 = infinity) cell as the product of the endpoint differences. The pairs
// already carry the x0/x1 infinity differences, so no selector test is needed here.
template <typename T, typename Factor> DEVICE_FORCEINLINE bwd_window_triplet<T> endpoint_product(const bwd_window_pair<T> a, const bwd_window_pair<Factor> b) {
  const T leading = T::mul(bwd_window_sub(a.values[1], a.values[0]), bwd_window_sub(b.values[1], b.values[0]));
  return {{T::mul(a.values[0], b.values[0]), T::mul(a.values[1], b.values[1]), leading}};
}

struct alignas(4) bwd_window_instruction {
  u16 opcode;
  u16 factor;
  u16 source_a;
  u16 source_b;
};
static_assert(sizeof(bwd_window_instruction) == BWD_WINDOW_INSTRUCTION_WORDS * sizeof(u16), "window instruction width drift");
static_assert(alignof(bwd_window_instruction) == 4, "window instruction alignment drift");
static_assert(__builtin_offsetof(bwd_window_desc, program) % alignof(bwd_window_instruction) == 0, "the program stream must admit instruction-wide reads");

DEVICE_FORCEINLINE bwd_window_instruction bwd_window_read(const u16 *program, const u32 pc) {
  return reinterpret_cast<const bwd_window_instruction *>(program)[pc];
}

// An aligned eight-corner window never crosses a virtual-source boundary, so a procedural
// source's two x2 endpoints (or their differences on infinite axes) are affine in the row and
// computed directly instead of evaluating each corner.
DEVICE_FORCEINLINE bwd_window_pair<bf> bwd_window_procedural_pair(const bwd_window_procedural_bf_source source, const u32 row,
                                                                  const bwd_window_selector_pair selector) {
  static_assert(GKR_TIMESTAMP_COLUMNS_NUM_BITS >= 3);
  const u32 base = row << 3;
  u32 origin;
  u32 step;
  switch (source.procedural_kind) {
  case BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS:
    if (base >= (1u << 16))
      return {{bf::ZERO(), bf::ZERO()}};
    origin = base;
    step = 1;
    break;
  case BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP:
    if (base >= (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS))
      return {{bf::ZERO(), bf::ZERO()}};
    origin = base;
    step = 1;
    break;
  case BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW:
    origin = (base << 2) & 0xffffu;
    step = 4;
    break;
  case BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH: {
    const bf value = selector.has_infinity() ? bf::ZERO() : bf::from_u32_unchecked(base >> 14);
    return {{value, value}};
  }
  default:
    return {{bf::ZERO(), bf::ZERO()}};
  }
  if (selector.has_infinity()) {
    const u32 slope = selector.x0_infinity() ? (selector.x1_infinity() ? 0 : 4 * step) : 2 * step;
    const bf value = bf::from_u32_unchecked(slope);
    return {{value, value}};
  }
  const u32 value = origin + step * (4 * selector.x0 + 2 * selector.x1);
  return {{bf::from_u32_unchecked(value), bf::from_u32_unchecked(value + step)}};
}

// ── BF section ──────────────────────────────────────────────────────────────

DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_linear(const bwd_window_pair<bf> source, const bwd_window_selector_pair selector) {
  if (selector.has_infinity())
    return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
  return {{source.values[0], source.values[1], bf::ZERO()}};
}

// The source pair of a linear singleton: direct or procedural.
template <bool MayUseProcedural>
DEVICE_FORCEINLINE bwd_window_pair<bf> bwd_window_bf_linear_pair(const bwd_window_desc &desc, const u16 opcode, const u16 source_a, const u32 row,
                                                                 const bwd_window_selector_pair selector) {
  if constexpr (MayUseProcedural) {
    if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL)
      return bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector);
  }
  return bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector);
}

// A lone BF term (linear or product) as its three cells.
template <bool MayUseProcedural>
DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_term(const bwd_window_desc &desc, const u16 opcode, const u16 source_a, const u16 source_b,
                                                             const u32 row, const bwd_window_selector_pair selector) {
  const bool linear = opcode == BWD_WINDOW_OPCODE_LINEAR_BF || (MayUseProcedural && opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL);
  if (linear && selector.has_infinity())
    return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
  if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF)
    return bwd_window_bf_linear(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector), selector);
  if constexpr (MayUseProcedural) {
    if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL)
      return bwd_window_bf_linear(bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector), selector);
    if (opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B)
      return endpoint_product<bf, bf>(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector),
                                      bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_b)}, row, selector));
    if (opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB)
      return endpoint_product<bf, bf>(bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector),
                                      bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_b)}, row, selector));
  }
  return endpoint_product<bf, bf>(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector),
                                  bwd_window_pair_values(bwd_window_direct_bf(desc, source_b), row, selector));
}

// Twelve 96-bit outer accumulators with the high words packed as u16 pairs: six registers for the
// carry counts instead of twelve. Bound: `add_pair` carries at most one into each high half per
// product; a (cell, limb) component receives one product per BF atom and four per wide-linear-E4
// record, at most 8192 for a 2048-record descriptor, so each 16-bit half stays below 8192, hence
// below 65536, and never carries into its neighbour. Reduction precedes the E4 sections and the
// scalar seed. Components (cell, limb) pair as limbs (0,1) and (2,3), which share the multiplicand
// `value` in every use, so one asm block adds both products.
static_assert(BWD_WINDOW_RECOMPUTED_PROGRAM_WORDS % BWD_WINDOW_INSTRUCTION_WORDS == 0);
static_assert(4 * (BWD_WINDOW_RECOMPUTED_PROGRAM_WORDS / BWD_WINDOW_INSTRUCTION_WORDS) < (1u << 16),
              "packed outer carry halves must hold every BF and wide-linear-E4 contribution");
template <bool PredicatedCarry> struct bwd_window_outer_packed {
  u64 low[12];
  u32 hi[6];
  template <u32 Cell, u32 Pair> DEVICE_FORCEINLINE void add_pair(const u32 a0, const u32 a1, const u32 b) {
    static_assert(Cell < 3 && Pair < 2, "outer component out of range");
    // Every input is consumed before any output is written: the read/write operands are copied into
    // local registers first and stored back only at the end, so equal-valued input/output aliasing
    // is safe (no early-clobber constraints needed).
    if constexpr (PredicatedCarry) {
      // The second product's carry stays a predicate and adds 65536 under it, instead of being
      // materialized and shifted; one instruction fewer per pair on sm_120.
      asm volatile("{\n\t"
                   ".reg .u32 lo0, mid0, lo1, mid1, h, c1;\n\t"
                   ".reg .pred carry;\n\t"
                   "mov.b64 {lo0, mid0}, %0;\n\t"
                   "mov.b64 {lo1, mid1}, %1;\n\t"
                   "mov.u32 h, %2;\n\t"
                   "mad.lo.cc.u32 lo0, %3, %5, lo0;\n\t"
                   "madc.hi.cc.u32 mid0, %3, %5, mid0;\n\t"
                   "addc.u32 h, h, 0;\n\t"
                   "mad.lo.cc.u32 lo1, %4, %5, lo1;\n\t"
                   "madc.hi.cc.u32 mid1, %4, %5, mid1;\n\t"
                   "addc.u32 c1, 0, 0;\n\t"
                   "setp.ne.u32 carry, c1, 0;\n\t"
                   "@carry add.u32 h, h, 65536;\n\t"
                   "mov.b64 %0, {lo0, mid0};\n\t"
                   "mov.b64 %1, {lo1, mid1};\n\t"
                   "mov.u32 %2, h;\n\t"
                   "}"
                   : "+l"(low[Cell * 4 + Pair * 2]), "+l"(low[Cell * 4 + Pair * 2 + 1]), "+r"(hi[Cell * 2 + Pair])
                   : "r"(a0), "r"(a1), "r"(b));
    } else {
      asm volatile("{\n\t"
                   ".reg .u32 lo0, mid0, lo1, mid1, h, c1;\n\t"
                   "mov.b64 {lo0, mid0}, %0;\n\t"
                   "mov.b64 {lo1, mid1}, %1;\n\t"
                   "mov.u32 h, %2;\n\t"
                   "mad.lo.cc.u32 lo0, %3, %5, lo0;\n\t"
                   "madc.hi.cc.u32 mid0, %3, %5, mid0;\n\t"
                   "addc.u32 h, h, 0;\n\t"
                   "mad.lo.cc.u32 lo1, %4, %5, lo1;\n\t"
                   "madc.hi.cc.u32 mid1, %4, %5, mid1;\n\t"
                   "addc.u32 c1, 0, 0;\n\t"
                   "mad.lo.u32 h, c1, 65536, h;\n\t"
                   "mov.b64 %0, {lo0, mid0};\n\t"
                   "mov.b64 %1, {lo1, mid1};\n\t"
                   "mov.u32 %2, h;\n\t"
                   "}"
                   : "+l"(low[Cell * 4 + Pair * 2]), "+l"(low[Cell * 4 + Pair * 2 + 1]), "+r"(hi[Cell * 2 + Pair])
                   : "r"(a0), "r"(a1), "r"(b));
    }
  }
  template <u32 Cell, u32 Limb> DEVICE_FORCEINLINE bf reduce() const {
    static_assert(Cell < 3 && Limb < 4, "outer component out of range");
    const u32 packed = hi[Cell * 2 + Limb / 2];
    const u32 half = (Limb & 1) ? (packed >> 16) : (packed & 0xffffu);
    return bf::add(bf::red_wide(low[Cell * 4 + Limb]), bwd_window_high_word_contribution(half));
  }
};
static_assert(sizeof(bwd_window_outer_packed<false>) == 12 * 8 + 6 * 4, "packed outer layout drift");
static_assert(sizeof(bwd_window_outer_packed<true>) == sizeof(bwd_window_outer_packed<false>));

template <u32 Cell, bool PredicatedCarry>
DEVICE_FORCEINLINE void bwd_window_outer_add_cell(bwd_window_outer_packed<PredicatedCarry> &outer, const e4 core, const bf value) {
  outer.template add_pair<Cell, 0>(core[0][0].limb, core[0][1].limb, value.limb);
  outer.template add_pair<Cell, 1>(core[1][0].limb, core[1][1].limb, value.limb);
}

template <bool PredicatedCarry>
DEVICE_FORCEINLINE void bwd_window_outer_add(bwd_window_outer_packed<PredicatedCarry> &outer, const e4 core, const bwd_window_triplet<bf> value) {
  bwd_window_outer_add_cell<0>(outer, core, value.values[0]);
  bwd_window_outer_add_cell<1>(outer, core, value.values[1]);
  bwd_window_outer_add_cell<2>(outer, core, value.values[2]);
}

// A linear term has no leading cell (`bwd_window_bf_linear` returns {v0, v1, 0} on finite
// selectors), so only cells 0 and 1 receive products: eight instead of twelve.
template <bool PredicatedCarry>
DEVICE_FORCEINLINE void bwd_window_outer_add_linear(bwd_window_outer_packed<PredicatedCarry> &outer, const e4 core, const bwd_window_pair<bf> value) {
  bwd_window_outer_add_cell<0>(outer, core, value.values[0]);
  bwd_window_outer_add_cell<1>(outer, core, value.values[1]);
}

template <u32 Cell, bool PredicatedCarry> DEVICE_FORCEINLINE e4 bwd_window_reduce_outer_cell(const bwd_window_outer_packed<PredicatedCarry> &outer) {
  return e4(e2(outer.template reduce<Cell, 0>(), outer.template reduce<Cell, 1>()), e2(outer.template reduce<Cell, 2>(), outer.template reduce<Cell, 3>()));
}

template <bool PredicatedCarry> DEVICE_FORCEINLINE void bwd_window_reduce_outer(const bwd_window_outer_packed<PredicatedCarry> &outer, e4 (&values)[3]) {
  values[0] = bwd_window_reduce_outer_cell<0>(outer);
  values[1] = bwd_window_reduce_outer_cell<1>(outer);
  values[2] = bwd_window_reduce_outer_cell<2>(outer);
}

// The b3 body keeps twelve full 96-bit accumulators: it has the registers, and the packed form
// measured slower there.
DEVICE_FORCEINLINE void bwd_window_outer_add(bwd_window_u96_accumulator (&outer)[3][4], const e4 core, const bwd_window_triplet<bf> value) {
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    outer[cell][0].add_product(core[0][0].limb, value.values[cell].limb);
    outer[cell][1].add_product(core[0][1].limb, value.values[cell].limb);
    outer[cell][2].add_product(core[1][0].limb, value.values[cell].limb);
    outer[cell][3].add_product(core[1][1].limb, value.values[cell].limb);
  }
}

DEVICE_FORCEINLINE void bwd_window_reduce_outer(const bwd_window_u96_accumulator (&outer)[3][4], e4 (&values)[3]) {
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4(e2(outer[cell][0].reduce(), outer[cell][1].reduce()), e2(outer[cell][2].reduce(), outer[cell][3].reduce()));
}

// Decode a member's immediate once and scale both x2 endpoints with it.
template <bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE bwd_window_pair<bf> bwd_window_scaled_endpoints(const bwd_window_desc &desc, const u16 factor, const bwd_window_pair<bf> a) {
  const u16 id = factor & BWD_WINDOW_ID_MASK;
  if (id == BWD_PROGRAM_IMMEDIATE_ONE)
    return a;
  if constexpr (MayNegate) {
    if (id == BWD_PROGRAM_IMMEDIATE_NEG_ONE)
      return {{bf::neg(a.values[0]), bf::neg(a.values[1])}};
  }
  if constexpr (MayHaveBanked) {
    const bf f = bf::from_reduced_raw_repr(desc.immediates[id - BWD_PROGRAM_IMMEDIATE_RESERVED]);
    return {{bf::mul(f, a.values[0]), bf::mul(f, a.values[1])}};
  }
  return a;
}

// One product member of a BF group into the group's three deferred-reduction u64 sums.
// f*(a1 - a0) == f*a1 - f*a0: the two endpoints of `a` are scaled once and differenced, instead
// of scaling both endpoints and the difference.
template <bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_accumulate_product_wide_sources(const bwd_window_desc &desc, const bwd_window_instruction instruction,
                                                                   const bwd_window_pair<bf> a, const bwd_window_pair<bf> b, u64 (&sums)[3]) {
  const auto scaled = bwd_window_scaled_endpoints<MayHaveBanked, MayNegate>(desc, instruction.factor, a);
  const bf s0 = scaled.values[0];
  const bf s1 = scaled.values[1];
  const bf delta_a = bwd_window_sub(s1, s0);
  const bf delta_b = bwd_window_sub(b.values[1], b.values[0]);
  sums[2] = mad_wide(delta_a.limb, delta_b.limb, sums[2]);
  sums[0] = mad_wide(s0.limb, b.values[0].limb, sums[0]);
  sums[1] = mad_wide(s1.limb, b.values[1].limb, sums[1]);
}

template <bool MayUseProcedural, bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_accumulate_product_wide(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                           const bwd_window_selector_pair selector, u64 (&sums)[3]) {
  if constexpr (MayUseProcedural) {
    if (instruction.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B) {
      return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
          desc, instruction, bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector),
          bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(instruction.source_b)}, row, selector), sums);
    }
    if (instruction.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB) {
      return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
          desc, instruction, bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(instruction.source_a)}, row, selector),
          bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(instruction.source_b)}, row, selector), sums);
    }
  }
  return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
      desc, instruction, bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector),
      bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_b), row, selector), sums);
}

// Re-enter Montgomery form so the next products accumulate into a fresh u64 segment without
// losing the running sum.
DEVICE_FORCEINLINE void bwd_window_reduce_and_rebase_wide(u64 &sum) { sum = mul_wide(bf::red_wide(sum).limb, bf::MONT_R); }

// A linear tail member on a finite selector: one BF source (direct or procedural), its two x2
// endpoints, the member factor decoded once, added to the two Boolean cells. The leading cell of
// a linear term is zero, so `sum.values[2]` is left alone; the caller runs this only on finite
// selectors, where the term is nonzero.
template <bool MayUseProcedural, bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_accumulate_linear_tail(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                          const bwd_window_selector_pair selector, bwd_window_triplet<bf> &sum) {
  const bwd_window_pair<bf> pair = bwd_window_bf_linear_pair<MayUseProcedural>(desc, instruction.opcode, instruction.source_a, row, selector);
  const bwd_window_pair<bf> scaled = bwd_window_scaled_endpoints<MayHaveBanked, MayNegate>(desc, instruction.factor, pair);
  sum.values[0] = bf::add(sum.values[0], scaled.values[0]);
  sum.values[1] = bf::add(sum.values[1], scaled.values[1]);
}

// A BF atom is either a lone term or a group: one control record naming the shared E4 core, then
// `arity` members. A leading run of `product_prefix` members are pure BFxBF products, which
// accumulate in one deferred-reduction u64 per cell instead of one Montgomery reduction each;
// with linear tails (shape bit BF_LINEAR_TAIL) the remaining members are linear terms.
//
// The recomputed lowering never emits a group with exactly one product (the tails lowering rejects
// it, the original lowering forms groups from two or more products), so there is no single-product
// path; `bwd_window_execute` asserts the shape bit.
template <bool MayUseProcedural, bool MayHaveBanked, bool MayReduce, bool LinearTails, bool MayNegate, bool PcEnd, bool NonEmptyProducts, bool LinearTwoCells,
          typename Outer>
DEVICE_FORCEINLINE u32 bwd_window_execute_bf_atom(const bwd_window_desc &desc, const u16 *program, const bwd_window_instruction head, u32 pc, const u32 row,
                                                  const bwd_window_selector_pair selector, Outer &outer) {
  if (head.opcode != BWD_WINDOW_OPCODE_GROUP_BF) {
    const bool linear = head.opcode == BWD_WINDOW_OPCODE_LINEAR_BF || (MayUseProcedural && head.opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL);
    // Linear terms vanish on infinity selectors. Skip the complete atom, including the coefficient
    // load and the volatile outer carry chain.
    if (linear && selector.has_infinity())
      return pc;
    if constexpr (LinearTwoCells) {
      static_assert(!std::is_same_v<Outer, bwd_window_u96_accumulator[3][4]>, "LinearTwoCells is defined for the packed accumulator");
      // On a finite selector the linear term's leading cell is zero, so cell 2 receives no products.
      if (linear) {
        bwd_window_outer_add_linear(outer, bwd_window_signed_coefficient<MayNegate>(head.factor),
                                    bwd_window_bf_linear_pair<MayUseProcedural>(desc, head.opcode, head.source_a, row, selector));
        return pc;
      }
    }
    bwd_window_outer_add(outer, bwd_window_signed_coefficient<MayNegate>(head.factor),
                         bwd_window_bf_term<MayUseProcedural>(desc, head.opcode, head.source_a, head.source_b, row, selector));
    return pc;
  }

  const u16 arity = head.source_a;
  const u16 product_prefix = head.source_b & BWD_WINDOW_ID_MASK;
  if constexpr (LinearTails) {
    // A linear-only group is zero on infinity selectors, exactly like the singletons it replaces:
    // skip the core load, the tail records and the outer carry chain.
    if (product_prefix == 0 && selector.has_infinity())
      return pc + arity;
  }
  const e4 core = bwd_window_coefficient(head.factor);
  bwd_window_triplet<bf> sum{{bf::ZERO(), bf::ZERO(), bf::ZERO()}};

  [[maybe_unused]] u16 member = 0;
  // PcEnd: every member read advances pc, so pc - pc0 == member on every path; the two bounds
  // replace the u16 counter and its masking. Unused (folded away) when PcEnd is false.
  [[maybe_unused]] const u32 product_end = pc + product_prefix;
  [[maybe_unused]] const u32 atom_end = pc + arity;
  // NonEmptyProducts: formation never emits an empty group; shape bit 3 marks every linear tail
  // (including every prefix-0 group of the tails lowering) and bit 11 marks a prefix of exactly
  // one. With both bits clear every valid group has product_prefix >= 2, so the gate folds and
  // the first product is read unconditionally. The compiler cannot derive this from
  // pc + product_prefix under u32 wrap.
  static_assert(!NonEmptyProducts || (PcEnd && !LinearTails), "NonEmptyProducts needs pc bounds and a tail-free shape");
  if (NonEmptyProducts || product_prefix >= 2) {
    u64 wide_sums[3]{0, 0, 0};
    if constexpr (NonEmptyProducts) {
#pragma unroll 1
      do {
        const bwd_window_instruction instruction = bwd_window_read(program, pc++);
        bwd_window_accumulate_product_wide<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, wide_sums);
        if constexpr (MayReduce) {
          if ((instruction.factor & BWD_WINDOW_FLAG) != 0) {
            bwd_window_reduce_and_rebase_wide(wide_sums[2]);
            bwd_window_reduce_and_rebase_wide(wide_sums[0]);
            bwd_window_reduce_and_rebase_wide(wide_sums[1]);
          }
        }
      } while (pc < product_end);
    } else {
#pragma unroll 1
      for (; PcEnd ? pc < product_end : member < product_prefix; ++member) {
        const bwd_window_instruction instruction = bwd_window_read(program, pc++);
        bwd_window_accumulate_product_wide<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, wide_sums);
        if constexpr (MayReduce) {
          if ((instruction.factor & BWD_WINDOW_FLAG) != 0) {
            bwd_window_reduce_and_rebase_wide(wide_sums[2]);
            bwd_window_reduce_and_rebase_wide(wide_sums[0]);
            bwd_window_reduce_and_rebase_wide(wide_sums[1]);
          }
        }
      }
    }
    sum.values[2] = bf::red_wide(wide_sums[2]);
    sum.values[0] = bf::red_wide(wide_sums[0]);
    sum.values[1] = bf::red_wide(wide_sums[1]);
  }

  if constexpr (LinearTails) {
    // Linear members vanish on infinity selectors. The predicate is warp-uniform, so the whole
    // tail is skipped as a block and the program counter is advanced past its records.
    if (selector.has_infinity()) {
      if constexpr (PcEnd)
        pc = atom_end;
      else
        pc += arity - member;
    } else {
#pragma unroll 1
      for (; PcEnd ? pc < atom_end : member < arity; ++member) {
        const bwd_window_instruction instruction = bwd_window_read(program, pc++);
        bwd_window_accumulate_linear_tail<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, sum);
      }
    }
  }
  bwd_window_outer_add(outer, core, sum);
  return pc;
}

// ── Wide linear-E4 section ──────────────────────────────────────────────────

// An E4 linear term is four BF limbs against four consecutive basis-scaled bank slots, so it
// joins the BF section's deferred accumulators instead of costing four E4 multiplies.
DEVICE_FORCEINLINE void bwd_window_accumulate_linear_wide(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                          const bwd_window_selector_pair selector, bwd_window_u96_accumulator (&outer)[3][4]) {
  if (selector.has_infinity())
    return;
  const auto source = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_a), row, selector);
  const bf source_zero[4]{source.values[0][0][0], source.values[0][0][1], source.values[0][1][0], source.values[0][1][1]};
  const bf source_one[4]{source.values[1][0][0], source.values[1][0][1], source.values[1][1][0], source.values[1][1][1]};
#pragma unroll
  for (u32 limb = 0; limb < 4; ++limb) {
    const e4 basis = bwd_window_coefficient(static_cast<u16>(instruction.factor + limb));
    outer[0][0].add_product(basis[0][0].limb, source_zero[limb].limb);
    outer[0][1].add_product(basis[0][1].limb, source_zero[limb].limb);
    outer[0][2].add_product(basis[1][0].limb, source_zero[limb].limb);
    outer[0][3].add_product(basis[1][1].limb, source_zero[limb].limb);
    outer[1][0].add_product(basis[0][0].limb, source_one[limb].limb);
    outer[1][1].add_product(basis[0][1].limb, source_one[limb].limb);
    outer[1][2].add_product(basis[1][0].limb, source_one[limb].limb);
    outer[1][3].add_product(basis[1][1].limb, source_one[limb].limb);
  }
}

// Packed-outer form of the wide linear-E4 accumulation: same products, paired per limb pair.
template <bool PredicatedCarry>
DEVICE_FORCEINLINE void bwd_window_accumulate_linear_wide(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                          const bwd_window_selector_pair selector, bwd_window_outer_packed<PredicatedCarry> &outer) {
  if (selector.has_infinity())
    return;
  const auto source = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_a), row, selector);
  const bf source_zero[4]{source.values[0][0][0], source.values[0][0][1], source.values[0][1][0], source.values[0][1][1]};
  const bf source_one[4]{source.values[1][0][0], source.values[1][0][1], source.values[1][1][0], source.values[1][1][1]};
#pragma unroll
  for (u32 limb = 0; limb < 4; ++limb) {
    const e4 basis = bwd_window_coefficient(static_cast<u16>(instruction.factor + limb));
    outer.template add_pair<0, 0>(basis[0][0].limb, basis[0][1].limb, source_zero[limb].limb);
    outer.template add_pair<0, 1>(basis[1][0].limb, basis[1][1].limb, source_zero[limb].limb);
    outer.template add_pair<1, 0>(basis[0][0].limb, basis[0][1].limb, source_one[limb].limb);
    outer.template add_pair<1, 1>(basis[1][0].limb, basis[1][1].limb, source_one[limb].limb);
  }
}

// ── E4 product sections ─────────────────────────────────────────────────────

// A negated factor negates every cell, so the sign rides one operand's endpoints rather than the
// assembled triplet.
template <typename T> DEVICE_FORCEINLINE bwd_window_pair<T> bwd_window_negate_pair(const bwd_window_pair<T> pair) {
  return {{T::neg(pair.values[0]), T::neg(pair.values[1])}};
}

template <bool MayNegate>
DEVICE_FORCEINLINE bwd_window_triplet<e4> bwd_window_mixed_product(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                                   const bwd_window_selector_pair selector) {
  auto bf_pair = bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector);
  if constexpr (MayNegate) {
    if ((instruction.factor & BWD_WINDOW_ID_MASK) == BWD_PROGRAM_IMMEDIATE_NEG_ONE)
      bf_pair = bwd_window_negate_pair(bf_pair);
  }
  const auto e4_pair = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_b), row, selector);
  return endpoint_product<e4, bf>(e4_pair, bf_pair);
}

template <bool MayNegate>
DEVICE_FORCEINLINE bwd_window_triplet<e4> bwd_window_full_product(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                                  const bwd_window_selector_pair selector) {
  auto a = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_a), row, selector);
  const auto b = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_b), row, selector);
  if constexpr (MayNegate) {
    if ((instruction.factor & BWD_WINDOW_ID_MASK) == BWD_PROGRAM_IMMEDIATE_NEG_ONE)
      a = bwd_window_negate_pair(a);
  }
  return endpoint_product<e4, e4>(a, b);
}

template <u16 Shape>
DEVICE_FORCEINLINE bwd_window_triplet<e4> bwd_window_product(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                             const bwd_window_selector_pair selector) {
  constexpr bool has_mixed = (Shape & BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_3) != 0;
  constexpr bool has_full = (Shape & BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_5) != 0;
  if constexpr (has_mixed && has_full)
    return instruction.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_E4 ? bwd_window_mixed_product<false>(desc, instruction, row, selector)
                                                                 : bwd_window_full_product<false>(desc, instruction, row, selector);
  if constexpr (has_mixed)
    return bwd_window_mixed_product<false>(desc, instruction, row, selector);
  static_assert(has_full, "the E4 singleton section has no enabled class");
  return bwd_window_full_product<false>(desc, instruction, row, selector);
}

// A singleton E4 product: the sign rides the core (the product runs with factor 0), then the
// three cells are multiplied by the core and added. `e4::fma(e4, e4, e4)` is a multiply and an
// add; the quartic accumulator cannot absorb the addend.
template <u16 Shape>
DEVICE_FORCEINLINE void bwd_window_execute_singleton(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                     const bwd_window_selector_pair selector, e4 (&values)[3]) {
  bwd_window_instruction product = instruction;
  product.factor = 0;
  const auto term = bwd_window_product<Shape>(desc, product, row, selector);
  constexpr bool may_negate = (Shape & BWD_WINDOW_SHAPE_E4_NEGATIVE_FACTOR) != 0;
  const e4 core = bwd_window_signed_coefficient<may_negate>(instruction.factor);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::fma(core, term.values[cell], values[cell]);
}

// A fixed pair: two members whose sum is multiplied by one shared core; each member's own sign
// rides its operand endpoints.
template <bool Mixed, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_execute_pair_members(const bwd_window_desc &desc, const bwd_window_instruction head, const bwd_window_instruction first,
                                                        const bwd_window_instruction second, const u32 row, const bwd_window_selector_pair selector,
                                                        e4 (&values)[3]) {
  bwd_window_triplet<e4> first_term;
  bwd_window_triplet<e4> second_term;
  if constexpr (Mixed) {
    first_term = bwd_window_mixed_product<MayNegate>(desc, first, row, selector);
    second_term = bwd_window_mixed_product<MayNegate>(desc, second, row, selector);
  } else {
    first_term = bwd_window_full_product<MayNegate>(desc, first, row, selector);
    second_term = bwd_window_full_product<MayNegate>(desc, second, row, selector);
  }
  const e4 core = bwd_window_coefficient(head.factor);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::fma(core, e4::add(first_term.values[cell], second_term.values[cell]), values[cell]);
}

template <u16 Shape>
DEVICE_FORCEINLINE void bwd_window_execute_loaded_pair(const bwd_window_desc &desc, const bwd_window_instruction head, const bwd_window_instruction first,
                                                       const bwd_window_instruction second, const u32 row, const bwd_window_selector_pair selector,
                                                       e4 (&values)[3]) {
  constexpr bool has_mixed_pair = (Shape & BWD_WINDOW_SHAPE_E4_PAIR_CLASS_3) != 0;
  constexpr bool has_full_pair = (Shape & BWD_WINDOW_SHAPE_E4_PAIR_CLASS_5) != 0;
  constexpr bool may_negate = (Shape & BWD_WINDOW_SHAPE_E4_NEGATIVE_FACTOR) != 0;
  static_assert(has_mixed_pair || has_full_pair, "the E4 fixed-pair section has no enabled class");
  if constexpr (has_mixed_pair && has_full_pair) {
    if (first.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_E4)
      bwd_window_execute_pair_members<true, may_negate>(desc, head, first, second, row, selector, values);
    else
      bwd_window_execute_pair_members<false, may_negate>(desc, head, first, second, row, selector, values);
  } else if constexpr (has_mixed_pair) {
    bwd_window_execute_pair_members<true, may_negate>(desc, head, first, second, row, selector, values);
  } else {
    bwd_window_execute_pair_members<false, may_negate>(desc, head, first, second, row, selector, values);
  }
}

// ── Driver ──────────────────────────────────────────────────────────────────

// Four straight-line sections walked in wire order (BF atoms, wide linear E4, E4 singletons, E4
// fixed pairs), each specialized at compile time by the program's shape mask so a feature no
// program in the section uses costs no instruction. Descriptor endpoints and program counters
// are block-uniform; inactive rows still execute every barrier and only publication is masked.
//
// Varying traits (see recomputed.cu for the four instantiations):
//   PackedHi          packed outer accumulators (b4 bodies) instead of twelve 96-bit accumulators (b3);
//   PcEnd             member loops bounded by pc endpoints instead of a u16 member counter;
//   NonEmptyProducts  the first product of every group is read unconditionally (unit shape);
//   LinearTwoCells    linear singletons feed cells 0 and 1 only (unit shape);
//   PredicatedCarry   the packed accumulator keeps its second carry as a predicate.
template <u16 Shape, bool PackedHi, bool PcEnd, bool NonEmptyProducts, bool LinearTwoCells, bool PredicatedCarry>
DEVICE_FORCEINLINE void bwd_window_evaluate_selector(const bwd_window_desc &desc, const u32 row, const bwd_window_selector_pair selector, e4 (&values)[3]) {
  static_assert((Shape & ~BWD_WINDOW_SHAPE_DEFINED_BITS) == 0, "undefined shape bits");
  static_assert((Shape & BWD_WINDOW_SHAPE_BF_SINGLE_PRODUCT_PREFIX) == 0,
                "one-product BF prefixes have no path in the recomputed executor; the recomputed lowering does not emit them");
  static_assert(!PredicatedCarry || PackedHi, "PredicatedCarry requires the packed outer accumulator");
  static_assert(!LinearTwoCells || PackedHi, "LinearTwoCells is defined for the packed outer accumulator");
  const u16 *program = desc.program;
  using OuterType = std::conditional_t<PackedHi, bwd_window_outer_packed<PredicatedCarry>, bwd_window_u96_accumulator[3][4]>;
  OuterType outer{};
  u32 pc = 0;
  constexpr bool bf_may_use_procedural = (Shape & BWD_WINDOW_SHAPE_BF_PROCEDURAL) != 0;
  constexpr bool bf_may_have_banked = (Shape & BWD_WINDOW_SHAPE_BF_BANKED_IMMEDIATE) != 0;
  constexpr bool bf_may_reduce = (Shape & BWD_WINDOW_SHAPE_BF_INNER_REDUCTION) != 0;
  constexpr bool bf_linear_tails = (Shape & BWD_WINDOW_SHAPE_BF_LINEAR_TAIL) != 0;
  constexpr bool bf_may_negate = (Shape & BWD_WINDOW_SHAPE_BF_NEGATIVE_FACTOR) != 0;
  while (pc < desc.sections[BWD_WINDOW_SECTION_BF]) {
    const bwd_window_instruction head = bwd_window_read(program, pc++);
    pc = bwd_window_execute_bf_atom<bf_may_use_procedural, bf_may_have_banked, bf_may_reduce, bf_linear_tails, bf_may_negate, PcEnd, NonEmptyProducts,
                                    LinearTwoCells>(desc, program, head, pc, row, selector, outer);
  }
  while (pc < desc.sections[BWD_WINDOW_SECTION_LINEAR_E4]) {
    const bwd_window_instruction instruction = bwd_window_read(program, pc++);
    bwd_window_accumulate_linear_wide(desc, instruction, row, selector, outer);
  }
  bwd_window_reduce_outer(outer, values);
  const u32 singleton_atoms = desc.sections[BWD_WINDOW_SECTION_SINGLETON_E4] - desc.sections[BWD_WINDOW_SECTION_LINEAR_E4];
  const u32 pair_atoms = (desc.sections[BWD_WINDOW_SECTION_PAIR_E4] - desc.sections[BWD_WINDOW_SECTION_SINGLETON_E4]) / 3;
  const bool synchronize = 2 * singleton_atoms + 4 * pair_atoms >= BWD_WINDOW_RECOMPUTED_REUSE_SCORE ||
                           (pair_atoms == 0 && singleton_atoms >= BWD_WINDOW_RECOMPUTED_REUSE_SINGLETONS);
  if (synchronize)
    __syncthreads();
  constexpr bool has_e4_singleton = (Shape & (BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_3 | BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_5)) != 0;
  if constexpr (has_e4_singleton) {
    while (pc < desc.sections[BWD_WINDOW_SECTION_SINGLETON_E4]) {
      const bwd_window_instruction instruction = bwd_window_read(program, pc++);
      bwd_window_execute_singleton<Shape>(desc, instruction, row, selector, values);
      if (synchronize && (pc & 15) == 0)
        __syncthreads();
    }
  }
  if (synchronize)
    __syncthreads();
  constexpr bool has_e4_pair = (Shape & BWD_WINDOW_SHAPE_E4_FIXED_PAIR) != 0;
  if constexpr (has_e4_pair) {
    while (pc < desc.sections[BWD_WINDOW_SECTION_PAIR_E4]) {
      const bwd_window_instruction head = bwd_window_read(program, pc++);
      const bwd_window_instruction first = bwd_window_read(program, pc++);
      const bwd_window_instruction second = bwd_window_read(program, pc++);
      bwd_window_execute_loaded_pair<Shape>(desc, head, first, second, row, selector, values);
      // Each pair advances pc by three, so this fires every 16 pair atoms.
      if (synchronize && (pc & 15) == 0)
        __syncthreads();
    }
  }
}

template <u16 Shape, bool PackedHi, bool PcEnd, bool NonEmptyProducts, bool LinearTwoCells, bool PredicatedCarry>
DEVICE_FORCEINLINE void bwd_window_execute(const bwd_window_desc &desc, const u32 scalar_seed) {
  const u32 lane = bwd_window_lane();
  const u32 row_tile = bwd_window_row_tile();
  const bwd_window_selector_pair selector = bwd_window_selector(bwd_window_selector_id());
  const u32 global_row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;
  const bool active = global_row < (1u << desc.log_rows);
  const u32 row = active ? global_row : 0;
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  bwd_window_evaluate_selector<Shape, PackedHi, PcEnd, NonEmptyProducts, LinearTwoCells, PredicatedCarry>(desc, row, selector, values);
  // The scalar seed (a bank id, 0xffff for none) is a constant term of the layer expression: it
  // contributes to the Boolean cells on finite selectors only.
  if (!selector.has_infinity() && scalar_seed != 0xffffu) {
    const e4 scalar = bwd_window_coefficient(static_cast<u16>(scalar_seed));
    values[0] = e4::add(values[0], scalar);
    values[1] = e4::add(values[1], scalar);
  }
  bwd_window_publish(desc, row_tile, lane, active, selector, values);
}

} // namespace airbender::gkr::backward::recomputed
