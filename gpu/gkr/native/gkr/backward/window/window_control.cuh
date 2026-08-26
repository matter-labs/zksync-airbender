#pragma once

// The sectioned window-3 executor: four straight-line sections walked in wire
// order, each specialized at compile time by the program's shape mask so a
// feature no program in the section uses costs no instruction.
#include "window_geometry.cuh"

namespace airbender::gkr::backward {

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

// ── BF section ──────────────────────────────────────────────────────────────

DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_product(const bwd_window_pair<bf> source_a, const bwd_window_pair<bf> source_b,
                                                                const bwd_window_selector_pair selector) {
  return bwd_window_product_tensor<bf, bf>(source_a, source_b, selector);
}

DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_linear(const bwd_window_pair<bf> source, const bwd_window_selector_pair selector) {
  if (selector.has_infinity())
    return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
  return {{source.values[0], source.values[1], bf::ZERO()}};
}

template <bool MayUseProcedural = true>
DEVICE_FORCEINLINE bwd_window_triplet<bf> bwd_window_bf_term(const bwd_window_desc &desc, const u16 opcode, const u16 source_a, const u16 source_b,
                                                             const u32 row, const bwd_window_selector_pair selector) {
  if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF)
    return bwd_window_bf_linear(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector), selector);
  if constexpr (MayUseProcedural) {
    if (opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL)
      return bwd_window_bf_linear(bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector), selector);
    if (opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B)
      return bwd_window_bf_product(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector),
                                   bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(source_b)}, row, selector), selector);
    if (opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB)
      return bwd_window_bf_product(bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(source_a)}, row, selector),
                                   bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(source_b)}, row, selector), selector);
  }
  return bwd_window_bf_product(bwd_window_pair_values(bwd_window_direct_bf(desc, source_a), row, selector),
                               bwd_window_pair_values(bwd_window_direct_bf(desc, source_b), row, selector), selector);
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

// The deferred-reduction form of `bwd_window_product_tensor`: one u64 segment
// per cell, and the two Boolean cells only where an infinite axis makes them
// live.
template <bool MayHaveBanked = true, bool MayNegate = true>
DEVICE_FORCEINLINE void bwd_window_accumulate_product_wide_sources(const bwd_window_desc &desc, const bwd_window_instruction instruction,
                                                                   const bwd_window_pair<bf> a, const bwd_window_pair<bf> b,
                                                                   const bwd_window_selector_pair selector, u64 (&sums)[3]) {
  bf delta_a = bwd_window_sub(a.values[1], a.values[0]);
  const bf delta_b = bwd_window_sub(b.values[1], b.values[0]);
  delta_a = bwd_window_apply_immediate<MayHaveBanked, MayNegate>(desc, instruction.factor, delta_a);
  sums[2] = mad_wide(delta_a.limb, delta_b.limb, sums[2]);
  if (!selector.has_infinity())
    return;
#pragma unroll
  for (u32 cell = 0; cell < 2; ++cell) {
    const bf scaled = bwd_window_apply_immediate<MayHaveBanked, MayNegate>(desc, instruction.factor, a.values[cell]);
    sums[cell] = mad_wide(scaled.limb, b.values[cell].limb, sums[cell]);
  }
}

template <bool MayUseProcedural = true, bool MayHaveBanked = true, bool MayNegate = true>
DEVICE_FORCEINLINE void bwd_window_accumulate_product_wide(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                           const bwd_window_selector_pair selector, u64 (&sums)[3]) {
  if constexpr (MayUseProcedural) {
    if (instruction.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B) {
      return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
          desc, instruction, bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector),
          bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(instruction.source_b)}, row, selector), selector, sums);
    }
    if (instruction.opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB) {
      return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
          desc, instruction, bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(instruction.source_a)}, row, selector),
          bwd_window_pair_values(bwd_window_procedural_bf_source{static_cast<u8>(instruction.source_b)}, row, selector), selector, sums);
    }
  }
  return bwd_window_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
      desc, instruction, bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_a), row, selector),
      bwd_window_pair_values(bwd_window_direct_bf(desc, instruction.source_b), row, selector), selector, sums);
}

// Re-enter Montgomery form so the next products accumulate into a fresh u64
// segment without losing the running sum.
DEVICE_FORCEINLINE void bwd_window_reduce_and_rebase_wide(u64 &sum) { sum = mul_wide(bf::red_wide(sum).limb, bf::MONT_R); }

template <bool MayUseProcedural, bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void bwd_window_accumulate_bf_member(const bwd_window_desc &desc, const bwd_window_instruction instruction, const u32 row,
                                                        const bwd_window_selector_pair selector, bwd_window_triplet<bf> &sum) {
  auto term = bwd_window_bf_term<MayUseProcedural>(desc, instruction.opcode, instruction.source_a, instruction.source_b, row, selector);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    term.values[cell] = bwd_window_apply_immediate<MayHaveBanked, MayNegate>(desc, instruction.factor, term.values[cell]);
    sum.values[cell] = bf::add(sum.values[cell], term.values[cell]);
  }
}

// A BF atom is either a lone term or a group: one control record naming the
// shared E4 core, then `arity` members. A leading run of `product_prefix`
// members are pure BFxBF products, which accumulate in one deferred-reduction
// u64 instead of one Montgomery reduction each.
template <bool MayUseProcedural = true, bool MayHaveBanked = true, bool MayReduce = true, bool HasLinearTail = true, bool MayNegate = true,
          bool MayHaveSingleProduct = true>
DEVICE_FORCEINLINE u32 bwd_window_execute_bf_atom(const bwd_window_desc &desc, const u16 *program, const bwd_window_instruction head, u32 pc, const u32 row,
                                                  const bwd_window_selector_pair selector, bwd_window_u96_accumulator (&outer)[3][4]) {
  if (head.opcode != BWD_WINDOW_OPCODE_GROUP_BF) {
    bwd_window_outer_add(outer, bwd_window_signed_coefficient<MayNegate>(head.factor),
                         bwd_window_bf_term<MayUseProcedural>(desc, head.opcode, head.source_a, head.source_b, row, selector));
    return pc;
  }

  const u16 arity = head.source_a;
  const u16 product_prefix = head.source_b & BWD_WINDOW_ID_MASK;
  const e4 core = bwd_window_coefficient(head.factor);
  bwd_window_triplet<bf> sum{{bf::ZERO(), bf::ZERO(), bf::ZERO()}};

  u16 member = 0;
  if (product_prefix >= 2) {
    u64 wide_sums[3]{0, 0, 0};
    const bool infinite = selector.has_infinity();
#pragma unroll 1
    for (; member < product_prefix; ++member) {
      const bwd_window_instruction instruction = bwd_window_read(program, pc++);
      bwd_window_accumulate_product_wide<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, wide_sums);
      if constexpr (MayReduce) {
        if ((instruction.factor & BWD_WINDOW_FLAG) != 0) {
          bwd_window_reduce_and_rebase_wide(wide_sums[2]);
          if (infinite) {
            bwd_window_reduce_and_rebase_wide(wide_sums[0]);
            bwd_window_reduce_and_rebase_wide(wide_sums[1]);
          }
        }
      }
    }
    sum.values[2] = bf::red_wide(wide_sums[2]);
    if (infinite) {
      sum.values[0] = bf::red_wide(wide_sums[0]);
      sum.values[1] = bf::red_wide(wide_sums[1]);
    }
  }

  if constexpr (MayHaveSingleProduct) {
    if (product_prefix < 2) {
      const bwd_window_instruction instruction = bwd_window_read(program, pc++);
      bwd_window_accumulate_bf_member<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, sum);
      ++member;
    }
  }
  if constexpr (HasLinearTail) {
    if (member < arity) {
      const bwd_window_instruction instruction = bwd_window_read(program, pc++);
      bwd_window_accumulate_bf_member<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, sum);
    }
  }
  bwd_window_outer_add(outer, core, sum);
  return pc;
}

// ── Wide linear-E4 section ──────────────────────────────────────────────────

// An E4 linear term is four BF limbs against four consecutive basis-scaled bank
// slots, so it joins the BF section's deferred accumulators instead of costing
// four E4 multiplies.
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

// ── E4 product sections ─────────────────────────────────────────────────────

// A negated factor negates every cell, so the sign rides one operand's
// endpoints rather than the assembled triplet.
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
  return bwd_window_product_tensor<e4, bf>(e4_pair, bf_pair, selector);
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
  return bwd_window_product_tensor<e4, e4>(a, b, selector);
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

template <u16 Shape>
DEVICE_FORCEINLINE void bwd_window_evaluate_selector(const bwd_window_desc &desc, const u32 row, const bwd_window_selector_pair selector, e4 (&values)[3]) {
  const u16 *program = desc.program;
  bwd_window_u96_accumulator outer[3][4]{};
  u32 pc = 0;
  constexpr bool bf_may_use_procedural = (Shape & BWD_WINDOW_SHAPE_BF_PROCEDURAL) != 0;
  constexpr bool bf_may_have_banked = (Shape & BWD_WINDOW_SHAPE_BF_BANKED_IMMEDIATE) != 0;
  constexpr bool bf_may_reduce = (Shape & BWD_WINDOW_SHAPE_BF_INNER_REDUCTION) != 0;
  constexpr bool bf_has_linear_tail = (Shape & BWD_WINDOW_SHAPE_BF_LINEAR_TAIL) != 0;
  constexpr bool bf_may_negate = (Shape & BWD_WINDOW_SHAPE_BF_NEGATIVE_FACTOR) != 0;
  constexpr bool bf_may_have_single_product = (Shape & BWD_WINDOW_SHAPE_BF_SINGLE_PRODUCT_PREFIX) != 0;
  while (pc < desc.sections[BWD_WINDOW_SECTION_BF]) {
    const bwd_window_instruction head = bwd_window_read(program, pc++);
    pc = bwd_window_execute_bf_atom<bf_may_use_procedural, bf_may_have_banked, bf_may_reduce, bf_has_linear_tail, bf_may_negate, bf_may_have_single_product>(
        desc, program, head, pc, row, selector, outer);
  }
  while (pc < desc.sections[BWD_WINDOW_SECTION_LINEAR_E4]) {
    const bwd_window_instruction instruction = bwd_window_read(program, pc++);
    bwd_window_accumulate_linear_wide(desc, instruction, row, selector, outer);
  }
  bwd_window_reduce_outer(outer, values);
  constexpr bool has_e4_singleton = (Shape & (BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_3 | BWD_WINDOW_SHAPE_E4_SINGLETON_CLASS_5)) != 0;
  if constexpr (has_e4_singleton) {
    while (pc < desc.sections[BWD_WINDOW_SECTION_SINGLETON_E4]) {
      const bwd_window_instruction instruction = bwd_window_read(program, pc++);
      bwd_window_execute_singleton<Shape>(desc, instruction, row, selector, values);
    }
  }
  constexpr bool has_e4_pair = (Shape & BWD_WINDOW_SHAPE_E4_FIXED_PAIR) != 0;
  if constexpr (has_e4_pair) {
    while (pc < desc.sections[BWD_WINDOW_SECTION_PAIR_E4]) {
      const bwd_window_instruction head = bwd_window_read(program, pc++);
      const bwd_window_instruction first = bwd_window_read(program, pc++);
      const bwd_window_instruction second = bwd_window_read(program, pc++);
      bwd_window_execute_loaded_pair<Shape>(desc, head, first, second, row, selector, values);
    }
  }
}

template <u16 Shape> DEVICE_FORCEINLINE void bwd_window_execute(const bwd_window_desc &desc) {
  const u32 lane = bwd_window_lane();
  const u32 row_tile = bwd_window_row_tile();
  const bwd_window_selector_pair selector = bwd_window_selector(bwd_window_selector_id());
  const u32 global_row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;
  const bool active = global_row < (1u << desc.log_rows);
  const u32 row = active ? global_row : 0;
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  bwd_window_evaluate_selector<Shape>(desc, row, selector, values);
  bwd_window_publish(desc, row_tile, lane, active, selector, values);
}

#define AB_GKR_BWD_WINDOW_DEFINE_KERNEL(Name, Shape, MinBlocks)                                                                                                \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_WINDOW_BLOCK_THREADS,                                                                      \
                                      MinBlocks) void Name(const __grid_constant__ airbender::gkr::backward::bwd_window_desc desc) {                           \
    if (blockDim.x != airbender::gkr::backward::BWD_WINDOW_BLOCK_THREADS)                                                                                      \
      return;                                                                                                                                                  \
    airbender::gkr::backward::bwd_window_execute<Shape>(desc);                                                                                                 \
  }

} // namespace airbender::gkr::backward
