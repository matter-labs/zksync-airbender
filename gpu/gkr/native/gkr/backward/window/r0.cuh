#pragma once
#include "window_geometry.cuh"
#include <type_traits>

namespace airbender::gkr::backward {

// Block barriers keep selector warps on nearby records to reuse shared inputs.
constexpr u32 BWD_WINDOW_R0_REUSE_SCORE = 120;
constexpr u32 BWD_WINDOW_R0_REUSE_SINGLETONS = 16;

constexpr u16 BWD_WINDOW_R0_REQUIRED_SHAPE_BITS = BWD_WINDOW_SHAPE_BF_PROCEDURAL | BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_3 |
                                                  BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_5 | BWD_WINDOW_SHAPE_E4_FIXED_PAIR | BWD_WINDOW_SHAPE_E4_NEGATIVE_FACTOR |
                                                  BWD_WINDOW_SHAPE_E4_PAIR_CLASS_3 | BWD_WINDOW_SHAPE_E4_PAIR_CLASS_5;

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

// An aligned eight-corner window stays within one virtual-source region, so
// its procedural endpoints are affine in the row.
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

DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_linear(const bwd_window_pair<bf> source) { return {{source.values[0], source.values[1], bf::ZERO()}}; }

DEVICE_FORCEINLINE bwd_window_pair<bf> bwd_window_bf_linear_pair(const bwd_window_desc &desc, const u16 opcode, const u16 source_a, const u32 row,
                                                                 const bwd_window_selector_pair selector) {
  if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL)
    return bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector);
  return bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector);
}

DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_term(const bwd_window_desc &desc, const u16 opcode, const u16 source_a, const u16 source_b,
                                                             const u32 row, const bwd_window_selector_pair selector) {
  const bool linear = opcode == BWD_WINDOW_OPCODE_LINEAR_BF || opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL;
  if (linear && selector.has_infinity())
    return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
  if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF)
    return bwd_window_bf_linear(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector));
  if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL)
    return bwd_window_bf_linear(bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector));
  if (opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B)
    return bwd_window_endpoint_product<bf, bf>(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector),
                                               bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_b)}, row, selector));
  if (opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB)
    return bwd_window_endpoint_product<bf, bf>(bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector),
                                               bwd_window_procedural_pair(bwd_window_procedural_bf_source{static_cast<u8>(source_b)}, row, selector));
  return bwd_window_endpoint_product<bf, bf>(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector),
                                             bwd_window_pair_values(bwd_window_direct_bf(desc, source_b), row, selector));
}

// Each (cell, limb) accumulates at most four products per record. With at most
// 2048 records, its carry count stays below 8192 and fits in a u16. Packing two
// counts into one register cannot carry into the neighboring half. Reduction
// precedes the E4 sections and scalar seed.
static_assert(BWD_WINDOW_PROGRAM_WORD_CAP % BWD_WINDOW_INSTRUCTION_WORDS == 0);
static_assert(4 * (BWD_WINDOW_PROGRAM_WORD_CAP / BWD_WINDOW_INSTRUCTION_WORDS) < (1u << 16),
              "packed outer carry halves must hold every BF and wide-linear-E4 contribution");
struct bwd_window_outer_packed {
  u64 low[12];
  u32 hi[6];
  template <u32 Cell, u32 Pair> DEVICE_FORCEINLINE void add_pair(const u32 a0, const u32 a1, const u32 b) {
    static_assert(Cell < 3 && Pair < 2, "outer component out of range");
    // Inputs are copied to local registers before outputs are written, allowing
    // input/output aliasing without early-clobber constraints.
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
  }
  template <u32 Cell, u32 Limb> DEVICE_FORCEINLINE bf reduce() const {
    static_assert(Cell < 3 && Limb < 4, "outer component out of range");
    const u32 packed = hi[Cell * 2 + Limb / 2];
    const u32 half = (Limb & 1) ? (packed >> 16) : (packed & 0xffffu);
    return bf::add(bf::red_wide(low[Cell * 4 + Limb]), bwd_window_high_word_contribution(half));
  }
};
static_assert(sizeof(bwd_window_outer_packed) == 12 * 8 + 6 * 4, "packed outer layout drift");

template <u32 Cell> DEVICE_FORCEINLINE void bwd_window_outer_add_cell(bwd_window_outer_packed &outer, const e4 core, const bf value) {
  outer.template add_pair<Cell, 0>(core[0][0].limb, core[0][1].limb, value.limb);
  outer.template add_pair<Cell, 1>(core[1][0].limb, core[1][1].limb, value.limb);
}

DEVICE_FORCEINLINE void bwd_window_outer_add(bwd_window_outer_packed &outer, const e4 core, const bwd_window_triplet<bf> value) {
  bwd_window_outer_add_cell<0>(outer, core, value.values[0]);
  bwd_window_outer_add_cell<1>(outer, core, value.values[1]);
  bwd_window_outer_add_cell<2>(outer, core, value.values[2]);
}

// Linear terms contribute only to the two Boolean cells.
DEVICE_FORCEINLINE void bwd_window_outer_add_linear(bwd_window_outer_packed &outer, const e4 core, const bwd_window_pair<bf> value) {
  bwd_window_outer_add_cell<0>(outer, core, value.values[0]);
  bwd_window_outer_add_cell<1>(outer, core, value.values[1]);
}

template <u32 Cell> DEVICE_FORCEINLINE e4 bwd_window_reduce_outer_cell(const bwd_window_outer_packed &outer) {
  return e4(e2(outer.template reduce<Cell, 0>(), outer.template reduce<Cell, 1>()), e2(outer.template reduce<Cell, 2>(), outer.template reduce<Cell, 3>()));
}

DEVICE_FORCEINLINE void bwd_window_reduce_outer(const bwd_window_outer_packed &outer, e4 (&values)[3]) {
  values[0] = bwd_window_reduce_outer_cell<0>(outer);
  values[1] = bwd_window_reduce_outer_cell<1>(outer);
  values[2] = bwd_window_reduce_outer_cell<2>(outer);
}

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

template <bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_accumulate_product_wide(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                           const bwd_window_selector_pair selector, u64 (&sums)[3]) {
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
  return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
      desc, instruction, bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector),
      bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_b), row, selector), sums);
}

// Restore Montgomery form before starting the next accumulation segment.
DEVICE_FORCEINLINE void bwd_window_reduce_and_rebase_wide(u64 &sum) { sum = mul_wide(bf::red_wide(sum).limb, bf::MONT_R); }

template <bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_accumulate_linear_tail(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                          const bwd_window_selector_pair selector, bwd_window_triplet<bf> &sum) {
  const bwd_window_pair<bf> pair = bwd_window_bf_linear_pair(desc, instruction.opcode, instruction.source_a, row, selector);
  const bwd_window_pair<bf> scaled = bwd_window_scaled_endpoints<MayHaveBanked, MayNegate>(desc, instruction.factor, pair);
  sum.values[0] = bf::add(sum.values[0], scaled.values[0]);
  sum.values[1] = bf::add(sum.values[1], scaled.values[1]);
}

// A group header names a shared E4 coefficient followed by product_prefix
// products and arity - product_prefix linear terms. The lowering rejects
// groups with exactly one product.
template <bool MayHaveBanked, bool MayReduce, bool LinearTails, bool MayNegate, bool PcEnd, bool NonEmptyProducts, typename Outer>
DEVICE_FORCEINLINE u32 bwd_window_execute_bf_atom(const bwd_window_desc &desc, const u16 *program, const bwd_window_instruction head, u32 pc, const u32 row,
                                                  const bwd_window_selector_pair selector, Outer &outer) {
  if (head.opcode != BWD_WINDOW_OPCODE_GROUP_BF) {
    const bool linear = head.opcode == BWD_WINDOW_OPCODE_LINEAR_BF || head.opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL;
    // Linear terms vanish on infinity selectors, including their coefficient loads.
    if (linear && selector.has_infinity())
      return pc;
    if constexpr (NonEmptyProducts) {
      static_assert(!std::is_same_v<Outer, bwd_window_u96_accumulator[3][4]>, "the two-cell linear path is defined for the packed accumulator");
      if (linear) {
        bwd_window_outer_add_linear(outer, bwd_window_signed_coefficient<MayNegate>(head.factor),
                                    bwd_window_bf_linear_pair(desc, head.opcode, head.source_a, row, selector));
        return pc;
      }
    }
    bwd_window_outer_add(outer, bwd_window_signed_coefficient<MayNegate>(head.factor),
                         bwd_window_bf_term(desc, head.opcode, head.source_a, head.source_b, row, selector));
    return pc;
  }

  const u16 arity = head.source_a;
  const u16 product_prefix = head.source_b & BWD_WINDOW_ID_MASK;
  if constexpr (LinearTails) {
    // Linear-only groups vanish on infinity selectors.
    if (product_prefix == 0 && selector.has_infinity())
      return pc + arity;
  }
  const e4 core = bwd_window_coefficient(head.factor);
  bwd_window_triplet<bf> sum{{bf::ZERO(), bf::ZERO(), bf::ZERO()}};

  [[maybe_unused]] u16 member = 0;
  [[maybe_unused]] const u32 product_end = pc + product_prefix;
  [[maybe_unused]] const u32 atom_end = pc + arity;
  // Without linear tails or single-product prefixes, every nonempty group has
  // at least two products; the first read needs no runtime bound check.
  static_assert(!NonEmptyProducts || (PcEnd && !LinearTails), "NonEmptyProducts needs pc bounds and a tail-free shape");
  if (NonEmptyProducts || product_prefix >= 2) {
    u64 wide_sums[3]{0, 0, 0};
    if constexpr (NonEmptyProducts) {
#pragma unroll 1
      do {
        const bwd_window_instruction instruction = bwd_window_read(program, pc++);
        bwd_window_accumulate_product_wide<MayHaveBanked, MayNegate>(desc, instruction, row, selector, wide_sums);
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
        bwd_window_accumulate_product_wide<MayHaveBanked, MayNegate>(desc, instruction, row, selector, wide_sums);
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
    // Linear tail members vanish on infinity selectors.
    if (selector.has_infinity()) {
      if constexpr (PcEnd)
        pc = atom_end;
      else
        pc += arity - member;
    } else {
#pragma unroll 1
      for (; PcEnd ? pc < atom_end : member < arity; ++member) {
        const bwd_window_instruction instruction = bwd_window_read(program, pc++);
        bwd_window_accumulate_linear_tail<MayHaveBanked, MayNegate>(desc, instruction, row, selector, sum);
      }
    }
  }
  bwd_window_outer_add(outer, core, sum);
  return pc;
}

// Four BF limbs use consecutive basis-scaled coefficient slots, allowing E4
// linear terms to share the BF deferred accumulators.
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

DEVICE_FORCEINLINE void bwd_window_accumulate_linear_wide(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                          const bwd_window_selector_pair selector, bwd_window_outer_packed &outer) {
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

// Negating one operand negates all three product cells.
template <typename T> DEVICE_FORCEINLINE bwd_window_pair<T> bwd_window_negate_pair(const bwd_window_pair<T> pair) {
  return {{T::neg(pair.values[0]), T::neg(pair.values[1])}};
}

DEVICE_FORCEINLINE bwd_window_triplet<e4> bwd_window_mixed_product(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                                   const bwd_window_selector_pair selector) {
  auto bf_pair = bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector);
  if ((instruction.factor & BWD_WINDOW_ID_MASK) == BWD_PROGRAM_IMMEDIATE_NEG_ONE)
    bf_pair = bwd_window_negate_pair(bf_pair);
  const auto e4_pair = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_b), row, selector);
  return bwd_window_endpoint_product<e4, bf>(e4_pair, bf_pair);
}

DEVICE_FORCEINLINE bwd_window_triplet<e4> bwd_window_full_product(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                                  const bwd_window_selector_pair selector) {
  auto a = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_a), row, selector);
  const auto b = bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_b), row, selector);
  if ((instruction.factor & BWD_WINDOW_ID_MASK) == BWD_PROGRAM_IMMEDIATE_NEG_ONE)
    a = bwd_window_negate_pair(a);
  return bwd_window_endpoint_product<e4, e4>(a, b);
}

// Scaling the E4 endpoints takes two quartic multiplies instead of scaling
// three product cells. Keeping the BF operand unscaled preserves mixed products.
DEVICE_FORCEINLINE void bwd_window_execute_singleton(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                     const bwd_window_selector_pair selector, e4 (&values)[3]) {
  const e4 core = bwd_window_signed_coefficient<true>(instruction.factor);
  const bool mixed = instruction.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_E4;
  auto a = bwd_window_pair_values(bwd_window_direct_e4(desc, mixed ? instruction.source_b : instruction.source_a), row, selector);
#pragma unroll
  for (u32 i = 0; i < 2; ++i)
    a.values[i] = e4::mul(core, a.values[i]);
  const auto term = mixed ? bwd_window_endpoint_product<e4, bf>(a, bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector))
                          : bwd_window_endpoint_product<e4, e4>(a, bwd_window_pair_values(bwd_window_direct_e4(desc, instruction.source_b), row, selector));
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::add(term.values[cell], values[cell]);
}

template <bool Mixed>
DEVICE_FORCEINLINE void bwd_window_execute_pair_members(const bwd_window_desc &desc, const bwd_window_instruction head, const bwd_window_instruction first,
                                                        const bwd_window_instruction second, const u32 row, const bwd_window_selector_pair selector,
                                                        e4 (&values)[3]) {
  bwd_window_triplet<e4> first_term;
  bwd_window_triplet<e4> second_term;
  if constexpr (Mixed) {
    first_term = bwd_window_mixed_product(desc, first, row, selector);
    second_term = bwd_window_mixed_product(desc, second, row, selector);
  } else {
    first_term = bwd_window_full_product(desc, first, row, selector);
    second_term = bwd_window_full_product(desc, second, row, selector);
  }
  const e4 core = bwd_window_coefficient(head.factor);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::fma(core, e4::add(first_term.values[cell], second_term.values[cell]), values[cell]);
}

DEVICE_FORCEINLINE void bwd_window_execute_loaded_pair(const bwd_window_desc &desc, const bwd_window_instruction head, const bwd_window_instruction first,
                                                       const bwd_window_instruction second, const u32 row, const bwd_window_selector_pair selector,
                                                       e4 (&values)[3]) {
  if (first.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_E4)
    bwd_window_execute_pair_members<true>(desc, head, first, second, row, selector, values);
  else
    bwd_window_execute_pair_members<false>(desc, head, first, second, row, selector, values);
}

// Descriptor endpoints are block-uniform. Inactive rows must execute every
// barrier; only publication is masked.
template <u16 Shape>
DEVICE_FORCEINLINE void bwd_window_evaluate_selector(const bwd_window_desc &desc, const u32 row, const bwd_window_selector_pair selector, const u32 start,
                                                     const u32 (&ends)[4], e4 (&values)[3]) {
  static_assert((Shape & ~BWD_WINDOW_SHAPE_DEFINED_BITS) == 0, "undefined shape bits");
  static_assert((Shape & BWD_WINDOW_R0_REQUIRED_SHAPE_BITS) == BWD_WINDOW_R0_REQUIRED_SHAPE_BITS,
                "every compiled shape carries the unconditional sections; a narrower shape needs its guards restored");
  constexpr bool unit_groups = Shape == 0x771;
  constexpr bool linear_tails = (Shape & BWD_WINDOW_SHAPE_BF_LINEAR_TAIL) != 0;
  constexpr bool pc_end = unit_groups || linear_tails;
  const u16 *program = desc.program;
  using OuterType = std::conditional_t<pc_end, bwd_window_outer_packed, bwd_window_u96_accumulator[3][4]>;
  OuterType outer{};
  u32 pc = start;
  constexpr bool bf_may_have_banked = (Shape & BWD_WINDOW_SHAPE_BF_BANKED_IMMEDIATE) != 0;
  constexpr bool bf_may_reduce = (Shape & BWD_WINDOW_SHAPE_BF_INNER_REDUCTION) != 0;
  constexpr bool bf_may_negate = (Shape & BWD_WINDOW_SHAPE_BF_NEGATIVE_FACTOR) != 0;
  while (pc < ends[BWD_WINDOW_SECTION_BF]) {
    const bwd_window_instruction head = bwd_window_read(program, pc++);
    pc = bwd_window_execute_bf_atom<bf_may_have_banked, bf_may_reduce, linear_tails, bf_may_negate, pc_end, unit_groups>(desc, program, head, pc, row, selector,
                                                                                                                         outer);
  }
  while (pc < ends[BWD_WINDOW_SECTION_LINEAR_E4]) {
    const bwd_window_instruction instruction = bwd_window_read(program, pc++);
    bwd_window_accumulate_linear_wide(desc, instruction, row, selector, outer);
  }
  bwd_window_reduce_outer(outer, values);
  const u32 singleton_atoms = ends[BWD_WINDOW_SECTION_SINGLETON_E4] - ends[BWD_WINDOW_SECTION_LINEAR_E4];
  const u32 pair_atoms = (ends[BWD_WINDOW_SECTION_PAIR_E4] - ends[BWD_WINDOW_SECTION_SINGLETON_E4]) / 3;
  const bool synchronize =
      2 * singleton_atoms + 4 * pair_atoms >= BWD_WINDOW_R0_REUSE_SCORE || (pair_atoms == 0 && singleton_atoms >= BWD_WINDOW_R0_REUSE_SINGLETONS);
  if (synchronize)
    __syncthreads();
  while (pc < ends[BWD_WINDOW_SECTION_SINGLETON_E4]) {
    const bwd_window_instruction instruction = bwd_window_read(program, pc++);
    bwd_window_execute_singleton(desc, instruction, row, selector, values);
    if (synchronize && ((pc - start) & 15) == 0)
      __syncthreads();
  }
  if (synchronize)
    __syncthreads();
  while (pc < ends[BWD_WINDOW_SECTION_PAIR_E4]) {
    const bwd_window_instruction head = bwd_window_read(program, pc++);
    const bwd_window_instruction first = bwd_window_read(program, pc++);
    const bwd_window_instruction second = bwd_window_read(program, pc++);
    bwd_window_execute_loaded_pair(desc, head, first, second, row, selector, values);
    // Each pair advances pc by three, so this fires every 16 pair atoms.
    if (synchronize && ((pc - start) & 15) == 0)
      __syncthreads();
  }
}

template <u16 Shape>
DEVICE_FORCEINLINE void bwd_window_execute(const bwd_window_desc &desc, const u32 scalar_seed, const u32 start, const u32 (&ends)[4], const u32 part = 0) {
  const u32 lane = bwd_window_lane();
  const u32 row_tile = bwd_window_row_tile();
  const bwd_window_selector_pair selector = bwd_window_selector(bwd_window_selector_id());
  const u32 global_row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;
  const bool active = global_row < (1u << desc.log_rows);
  const u32 row = active ? global_row : 0;
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  bwd_window_evaluate_selector<Shape>(desc, row, selector, start, ends, values);
  // A scalar term contributes only to finite Boolean cells; 0xffff means absent.
  if (part == 0 && !selector.has_infinity() && scalar_seed != 0xffffu) {
    const e4 scalar = bwd_window_coefficient(static_cast<u16>(scalar_seed));
    values[0] = e4::add(values[0], scalar);
    values[1] = e4::add(values[1], scalar);
  }
  // All nine selector warps use the same row's equality weight.
  __shared__ e4 equality_by_lane[BWD_WINDOW_ROWS_PER_TILE];
  if (bwd_window_selector_id() == 0)
    equality_by_lane[lane] = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, row);
  __syncthreads();
  e4 *partials = desc.partials + static_cast<size_t>(part) * gridDim.x * BWD_WINDOW_TENSOR_CELLS;
  bwd_window_publish(partials, row_tile, lane, active, selector, equality_by_lane[lane], values);
}

} // namespace airbender::gkr::backward
