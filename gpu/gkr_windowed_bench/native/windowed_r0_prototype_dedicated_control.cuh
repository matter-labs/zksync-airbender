#pragma once

#include "windowed_r0_prototype_kernel.cuh"

namespace airbender::gkr_windowed_bench {

// Dedicated control for the architecture proven by the original 79-register
// first-window kernel. Keep the BF and E4 phases structurally separate and
// consume grouped atoms directly; do not materialize decoded_r0_op or retain
// the generic source/group policy state.
template <typename T, u32 Count> struct alignas((sizeof(T) * Count < 32) ? sizeof(T) * Count : 32) r0pb_control_packed_values {
  T values[Count];
};

template <typename T> struct r0pb_control_pair {
  T values[2];
};

template <typename T> struct r0pb_control_triplet {
  T values[3];
};

struct alignas(4) r0pb_control_instruction {
  u16 term_class;
  u16 factor;
  u16 source_a;
  u16 source_b;
};

static_assert(sizeof(r0pb_control_instruction) == 8 && alignof(r0pb_control_instruction) == 4);
static_assert(__builtin_offsetof(r0_grouped_slot_ordinary, program) % alignof(r0pb_control_instruction) == 0);

DEVICE_FORCEINLINE r0pb_control_instruction r0pb_control_read_instruction(const u16 *program, const u32 pc) {
  return reinterpret_cast<const r0pb_control_instruction *>(program)[pc];
}

constexpr u16 R0PB_CONTROL_GROUP_BF = 6;
constexpr u16 R0PB_CONTROL_GROUP_E4 = 7;
constexpr u16 R0PB_CONTROL_LINEAR_BF_PROCEDURAL = 4;
constexpr u16 R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_B = 8;
constexpr u16 R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_AB = 9;
constexpr u16 R0PB_CONTROL_LINEAR_E4_WIDE = 10;
constexpr u16 R0PB_CONTROL_FLAG = 1u << 15;
constexpr u16 R0PB_CONTROL_ID_MASK = R0PB_CONTROL_FLAG - 1;

constexpr u16 R0PB_SHAPE_BF_PROCEDURAL = 1u << 0;
constexpr u16 R0PB_SHAPE_BF_BANKED_IMMEDIATE = 1u << 1;
constexpr u16 R0PB_SHAPE_BF_INNER_REDUCTION = 1u << 2;
constexpr u16 R0PB_SHAPE_BF_LINEAR_TAIL = 1u << 3;
constexpr u16 R0PB_SHAPE_E4_SINGLETON_CLASS_3 = 1u << 4;
constexpr u16 R0PB_SHAPE_E4_SINGLETON_CLASS_5 = 1u << 5;
constexpr u16 R0PB_SHAPE_E4_FIXED_PAIR = 1u << 6;
constexpr u16 R0PB_SHAPE_BF_NEGATIVE_FACTOR = 1u << 7;
constexpr u16 R0PB_SHAPE_E4_NEGATIVE_FACTOR = 1u << 8;
constexpr u16 R0PB_SHAPE_E4_PAIR_CLASS_3 = 1u << 9;
constexpr u16 R0PB_SHAPE_E4_PAIR_CLASS_5 = 1u << 10;
constexpr u16 R0PB_SHAPE_BF_SINGLE_PRODUCT_PREFIX = 1u << 11;
constexpr u16 R0PB_SHAPE_UNIVERSAL = (1u << 12) - 1;

template <typename T, u32 Count> DEVICE_FORCEINLINE r0pb_control_packed_values<T, Count> r0pb_control_load(const T *column, const u32 index) {
  using packed = r0pb_control_packed_values<T, Count>;
  return load<packed, ld_modifier::ca>(reinterpret_cast<const packed *>(column + index));
}

template <typename T> DEVICE_FORCEINLINE r0pb_control_pair<T> r0pb_control_direct_pair(const T *column, const u32 row, const r0_selector_pair selector) {
  if (!selector.x0_infinity() && !selector.x1_infinity()) {
    const auto values = r0pb_control_load<T, 2>(column, r0_corner_index(row, selector.x0, selector.x1, 0));
    return {{values.values[0], values.values[1]}};
  }
  if (selector.x0_infinity() && !selector.x1_infinity()) {
    const auto zero = r0pb_control_load<T, 2>(column, r0_corner_index(row, 0, selector.x1, 0));
    const auto one = r0pb_control_load<T, 2>(column, r0_corner_index(row, 1, selector.x1, 0));
    return {{r0_sub(one.values[0], zero.values[0]), r0_sub(one.values[1], zero.values[1])}};
  }
  if (!selector.x0_infinity() && selector.x1_infinity()) {
    const auto values = r0pb_control_load<T, 4>(column, r0_corner_index(row, selector.x0, 0, 0));
    return {{r0_sub(values.values[2], values.values[0]), r0_sub(values.values[3], values.values[1])}};
  }
  const auto values = r0pb_control_load<T, 8>(column, r0_corner_index(row, 0, 0, 0));
  const T at_x1_zero_0 = r0_sub(values.values[4], values.values[0]);
  const T at_x1_zero_1 = r0_sub(values.values[5], values.values[1]);
  const T at_x1_one_0 = r0_sub(values.values[6], values.values[2]);
  const T at_x1_one_1 = r0_sub(values.values[7], values.values[3]);
  return {{r0_sub(at_x1_one_0, at_x1_zero_0), r0_sub(at_x1_one_1, at_x1_zero_1)}};
}

struct r0pb_control_direct_bf_source {
  const bf *column;
  DEVICE_FORCEINLINE bf value(const u32 index) const { return load<bf, ld_modifier::ca>(column, index); }
};

DEVICE_FORCEINLINE bf r0pb_control_procedural_bf_value(const u8 procedural_kind, const u32 index) {
  return bf::from_u32_unchecked(r0_procedural_raw(procedural_kind, index));
}

struct r0pb_control_procedural_bf_source {
  u8 procedural_kind;
  DEVICE_FORCEINLINE bf value(const u32 index) const { return r0pb_control_procedural_bf_value(procedural_kind, index); }
};

struct r0pb_control_direct_e4_source {
  const e4 *column;
  DEVICE_FORCEINLINE e4 value(const u32 index) const { return load<e4, ld_modifier::ca>(column, index); }
};

DEVICE_FORCEINLINE r0pb_control_pair<bf> r0pb_control_pair_values(const r0pb_control_procedural_bf_source source, const u32 row,
                                                                  const r0_selector_pair selector) {
  return {{r0_xy_endpoint<bf>(source, row, selector, 0), r0_xy_endpoint<bf>(source, row, selector, 1)}};
}

DEVICE_FORCEINLINE r0pb_control_pair<e4> r0pb_control_pair_values(const r0_e4_source source, const u32 row, const r0_selector_pair selector) {
  return {{r0_xy_endpoint<e4>(source, row, selector, 0), r0_xy_endpoint<e4>(source, row, selector, 1)}};
}

DEVICE_FORCEINLINE r0pb_control_pair<bf> r0pb_control_pair_values(const r0pb_control_direct_bf_source source, const u32 row, const r0_selector_pair selector) {
  return r0pb_control_direct_pair(source.column, row, selector);
}

DEVICE_FORCEINLINE r0pb_control_pair<e4> r0pb_control_pair_values(const r0pb_control_direct_e4_source source, const u32 row, const r0_selector_pair selector) {
  return r0pb_control_direct_pair(source.column, row, selector);
}

DEVICE_FORCEINLINE r0pb_control_direct_bf_source r0pb_control_direct_bf(const r0_grouped_slot_ordinary &desc, const u16 packed) {
  const u16 window = packed >> R0_SOURCE_COLUMN_BITS;
  const u16 column = packed & R0_SOURCE_COLUMN_MASK;
  const r0_window_addr &address = desc.common.window_bases[window];
  const bf *base = reinterpret_cast<const bf *>(address.base);
  return {base + (static_cast<size_t>(column) << address.log2_stride)};
}

DEVICE_FORCEINLINE r0pb_control_direct_e4_source r0pb_control_direct_e4(const r0_grouped_slot_ordinary &desc, const u16 packed) {
  const u16 window = packed >> R0_SOURCE_COLUMN_BITS;
  const u16 column = packed & R0_SOURCE_COLUMN_MASK;
  const r0_window_addr &address = desc.common.window_bases[window];
  const e4 *base = reinterpret_cast<const e4 *>(address.base);
  return {base + (static_cast<size_t>(column) << address.log2_stride)};
}

DEVICE_FORCEINLINE r0pb_control_triplet<bf> r0pb_control_bf_product(const r0pb_control_pair<bf> source_a, const r0pb_control_pair<bf> source_b) {
  const bf product = bf::mul(r0_sub(source_a.values[1], source_a.values[0]), r0_sub(source_b.values[1], source_b.values[0]));
  return {{bf::ZERO(), product, product}};
}

DEVICE_FORCEINLINE r0pb_control_triplet<bf> r0pb_control_bf_linear(const r0pb_control_pair<bf> source, const r0_selector_pair selector) {
  if (selector.has_infinity())
    return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
  return {{source.values[0], source.values[1], bf::ZERO()}};
}

template <bool MayUseProcedural = true>
DEVICE_FORCEINLINE r0pb_control_triplet<bf> r0pb_control_bf_term(const r0_grouped_slot_ordinary &desc, const u16 opcode, const u16 source_a, const u16 source_b,
                                                                 const u32 row, const r0_selector_pair selector) {
  if (opcode == 0)
    return r0pb_control_bf_linear(r0pb_control_pair_values(r0pb_control_direct_bf(desc, source_a), row, selector), selector);
  if constexpr (MayUseProcedural) {
    if (opcode == R0PB_CONTROL_LINEAR_BF_PROCEDURAL)
      return r0pb_control_bf_linear(r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(source_a)}, row, selector), selector);
    if (opcode == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_B)
      return r0pb_control_bf_product(r0pb_control_pair_values(r0pb_control_direct_bf(desc, source_a), row, selector),
                                     r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(source_b)}, row, selector));
    if (opcode == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_AB)
      return r0pb_control_bf_product(r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(source_a)}, row, selector),
                                     r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(source_b)}, row, selector));
  }
  return r0pb_control_bf_product(r0pb_control_pair_values(r0pb_control_direct_bf(desc, source_a), row, selector),
                                 r0pb_control_pair_values(r0pb_control_direct_bf(desc, source_b), row, selector));
}

template <typename E4Source>
DEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_control_bf_e4_product(const r0pb_control_pair<bf> source_a, const E4Source source_b, const u32 row,
                                                                       const r0_selector_pair selector) {
  const e4 product = e4::mul(r0_x2_delta<e4>(source_b, row, selector), r0_sub(source_a.values[1], source_a.values[0]));
  return {{e4::ZERO(), product, product}};
}

DEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_control_e4_term(const r0_grouped_slot_ordinary &desc, const u16 opcode, const u16 source_a, const u16 source_b,
                                                                 const u32 row, const r0_selector_pair selector) {
  if (opcode == 0 || opcode == 2 || opcode == R0PB_CONTROL_LINEAR_BF_PROCEDURAL || opcode == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_B ||
      opcode == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_AB) {
    const auto value = r0pb_control_bf_term(desc, opcode, source_a, source_b, row, selector);
    return {{e4::from_scalar(value.values[0]), e4::from_scalar(value.values[1]), e4::from_scalar(value.values[2])}};
  }
  if (opcode == 1) {
    if (selector.has_infinity())
      return {{e4::ZERO(), e4::ZERO(), e4::ZERO()}};
    const auto endpoints = r0pb_control_pair_values(r0pb_control_direct_e4(desc, source_a), row, selector);
    return {{endpoints.values[0], endpoints.values[1], e4::ZERO()}};
  }
  if (opcode == 3)
    return r0pb_control_bf_e4_product(r0pb_control_pair_values(r0pb_control_direct_bf(desc, source_a), row, selector), r0pb_control_direct_e4(desc, source_b),
                                      row, selector);
  const e4 product =
      e4::mul(r0_x2_delta<e4>(r0pb_control_direct_e4(desc, source_a), row, selector), r0_x2_delta<e4>(r0pb_control_direct_e4(desc, source_b), row, selector));
  return {{e4::ZERO(), product, product}};
}

DEVICE_FORCEINLINE bf r0pb_control_immediate(const r0_grouped_slot_ordinary &desc, const u16 id) {
  if (id == 0)
    return bf::ONE();
  if (id == 1)
    return bf::neg(bf::ONE());
  return bf::from_reduced_raw_repr(desc.immediates[id - 2]);
}

template <bool MayNegate> DEVICE_FORCEINLINE e4 r0pb_sectioned_coefficient(const u16 encoded) {
  const e4 value = r0_coefficient(encoded & R0PB_CONTROL_ID_MASK);
  if constexpr (MayNegate)
    return (encoded & R0PB_CONTROL_FLAG) != 0 ? e4::neg(value) : value;
  return value;
}

DEVICE_FORCEINLINE void r0pb_control_outer_add(e4 (&outer)[3], const e4 core, const r0pb_control_triplet<bf> value) {
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    outer[cell] = e4::fma(core, value.values[cell], outer[cell]);
}

DEVICE_FORCEINLINE void r0pb_control_outer_add_wide(r0_u96_accumulator (&outer)[3][4], const e4 core, const r0pb_control_triplet<bf> value) {
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    outer[cell][0].add_product(core[0][0].limb, value.values[cell].limb);
    outer[cell][1].add_product(core[0][1].limb, value.values[cell].limb);
    outer[cell][2].add_product(core[1][0].limb, value.values[cell].limb);
    outer[cell][3].add_product(core[1][1].limb, value.values[cell].limb);
  }
}

DEVICE_FORCEINLINE void r0pb_control_reduce_outer(const r0_u96_accumulator (&outer)[3][4], e4 (&values)[3]) {
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4(e2(outer[cell][0].reduce(), outer[cell][1].reduce()), e2(outer[cell][2].reduce(), outer[cell][3].reduce()));
}

template <bool MayHaveBanked = true, bool MayNegate = true>
DEVICE_FORCEINLINE bf r0pb_control_apply_immediate(const r0_grouped_slot_ordinary &desc, const u16 factor, const bf value) {
  const u16 id = factor & R0PB_CONTROL_ID_MASK;
  if (id == 0)
    return value;
  if constexpr (MayNegate) {
    if (id == 1)
      return bf::neg(value);
  }
  if constexpr (MayHaveBanked)
    return bf::mul(bf::from_reduced_raw_repr(desc.immediates[id - 2]), value);
  return value;
}

DEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_control_e4_group_member(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction,
                                                                         const u32 row, const r0_selector_pair selector) {
  if (instruction.term_class == 0 || instruction.term_class == 2 || instruction.term_class == R0PB_CONTROL_LINEAR_BF_PROCEDURAL ||
      instruction.term_class == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_B || instruction.term_class == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_AB) {
    auto bf_term = r0pb_control_bf_term(desc, instruction.term_class, instruction.source_a, instruction.source_b, row, selector);
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      bf_term.values[cell] = r0pb_control_apply_immediate(desc, instruction.factor, bf_term.values[cell]);
    return {{e4::from_scalar(bf_term.values[0]), e4::from_scalar(bf_term.values[1]), e4::from_scalar(bf_term.values[2])}};
  }

  if (instruction.term_class == 3) {
    const auto bf_pair = r0pb_control_pair_values(r0pb_control_direct_bf(desc, instruction.source_a), row, selector);
    bf delta_bf = r0_sub(bf_pair.values[1], bf_pair.values[0]);
    delta_bf = r0pb_control_apply_immediate(desc, instruction.factor, delta_bf);
    const e4 delta_e4 = r0_x2_delta<e4>(r0pb_control_direct_e4(desc, instruction.source_b), row, selector);
    const e4 product = e4::mul(delta_e4, delta_bf);
    return {{e4::ZERO(), product, product}};
  }

  auto term = r0pb_control_e4_term(desc, instruction.term_class, instruction.source_a, instruction.source_b, row, selector);
  const u16 id = instruction.factor & R0PB_CONTROL_ID_MASK;
  if (id == 0)
    return term;
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    if (id == 1)
      term.values[cell] = e4::neg(term.values[cell]);
    else
      term.values[cell] = e4::mul(term.values[cell], r0pb_control_immediate(desc, id));
  }
  return term;
}

template <bool MayHaveBanked = true, bool MayNegate = true>
DEVICE_FORCEINLINE void r0pb_control_accumulate_product_wide_sources(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction,
                                                                     const r0pb_control_pair<bf> a, const r0pb_control_pair<bf> b, u64 &sum) {
  bf delta_a = r0_sub(a.values[1], a.values[0]);
  const bf delta_b = r0_sub(b.values[1], b.values[0]);
  delta_a = r0pb_control_apply_immediate<MayHaveBanked, MayNegate>(desc, instruction.factor, delta_a);
  sum = mad_wide(delta_a.limb, delta_b.limb, sum);
}

template <bool MayUseProcedural = true, bool MayHaveBanked = true, bool MayNegate = true>
DEVICE_FORCEINLINE void r0pb_control_accumulate_product_wide(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction, const u32 row,
                                                             const r0_selector_pair selector, u64 &sum) {
  if constexpr (MayUseProcedural) {
    if (instruction.term_class == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_B) {
      return r0pb_control_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
          desc, instruction, r0pb_control_pair_values(r0pb_control_direct_bf(desc, instruction.source_a), row, selector),
          r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(instruction.source_b)}, row, selector), sum);
    }
    if (instruction.term_class == R0PB_CONTROL_PRODUCT_BF_BF_PROCEDURAL_AB) {
      return r0pb_control_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
          desc, instruction, r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(instruction.source_a)}, row, selector),
          r0pb_control_pair_values(r0pb_control_procedural_bf_source{static_cast<u8>(instruction.source_b)}, row, selector), sum);
    }
  }
  return r0pb_control_accumulate_product_wide_sources<MayHaveBanked, MayNegate>(
      desc, instruction, r0pb_control_pair_values(r0pb_control_direct_bf(desc, instruction.source_a), row, selector),
      r0pb_control_pair_values(r0pb_control_direct_bf(desc, instruction.source_b), row, selector), sum);
}

DEVICE_FORCEINLINE void r0pb_control_reduce_and_rebase_bf_wide(u64 &sum) { sum = mul_wide(bf::red_wide(sum).limb, bf::MONT_R); }

DEVICE_FORCEINLINE bf r0pb_control_reduce_bf_wide(const u64 sum) { return bf::red_wide(sum); }

template <bool MayUseProcedural, bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void r0pb_control_accumulate_bf_member(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction, const u32 row,
                                                          const r0_selector_pair selector, r0pb_control_triplet<bf> &sum) {
  auto term = r0pb_control_bf_term<MayUseProcedural>(desc, instruction.term_class, instruction.source_a, instruction.source_b, row, selector);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    term.values[cell] = r0pb_control_apply_immediate<MayHaveBanked, MayNegate>(desc, instruction.factor, term.values[cell]);
    sum.values[cell] = bf::add(sum.values[cell], term.values[cell]);
  }
}

template <bool MayUseProcedural = true, bool MayHaveBanked = true, bool MayReduce = true, bool HasLinearTail = true, bool MayNegate = true,
          bool MayHaveSingleProduct = true>
DEVICE_FORCEINLINE u32 r0pb_control_execute_bf_atom(const r0_grouped_slot_ordinary &desc, const u16 *program, const r0pb_control_instruction head, u32 pc,
                                                    const u32 row, const r0_selector_pair selector, r0_u96_accumulator (&outer)[3][4]) {
  if (head.term_class != R0PB_CONTROL_GROUP_BF) {
    r0pb_control_outer_add_wide(outer, r0pb_sectioned_coefficient<MayNegate>(head.factor),
                                r0pb_control_bf_term<MayUseProcedural>(desc, head.term_class, head.source_a, head.source_b, row, selector));
    return pc;
  }

  const u16 arity = head.source_a;
  const u16 product_prefix = head.source_b & R0PB_CONTROL_ID_MASK;
  const e4 core = r0_coefficient(head.factor);
  r0pb_control_triplet<bf> sum{{bf::ZERO(), bf::ZERO(), bf::ZERO()}};

  u16 member = 0;
  if (product_prefix >= 2) {
    u64 wide_sum = 0;
#pragma unroll 1
    for (; member < product_prefix; ++member) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
      r0pb_control_accumulate_product_wide<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, wide_sum);
      if constexpr (MayReduce) {
        if ((instruction.factor & R0PB_CONTROL_FLAG) != 0)
          r0pb_control_reduce_and_rebase_bf_wide(wide_sum);
      }
    }
    const bf reduced = r0pb_control_reduce_bf_wide(wide_sum);
    sum.values[1] = reduced;
    sum.values[2] = reduced;
  }

  if constexpr (MayHaveSingleProduct) {
    if (product_prefix < 2) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
      r0pb_control_accumulate_bf_member<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, sum);
      ++member;
    }
  }
  if constexpr (HasLinearTail) {
    if (member < arity) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
      r0pb_control_accumulate_bf_member<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selector, sum);
    }
  }
  r0pb_control_outer_add_wide(outer, core, sum);
  return pc;
}

DEVICE_FORCEINLINE u32 r0pb_control_execute_e4_atom(const r0_grouped_slot_ordinary &desc, const u16 *program, const r0pb_control_instruction head, u32 pc,
                                                    const u32 row, const r0_selector_pair selector, e4 (&values)[3]) {
  if (head.term_class != R0PB_CONTROL_GROUP_E4) {
    const auto term = r0pb_control_e4_term(desc, head.term_class, head.source_a, head.source_b, row, selector);
    const e4 core = r0_coefficient(head.factor);
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      values[cell] = e4::fma(core, term.values[cell], values[cell]);
    return pc;
  }

  const e4 core = r0_coefficient(head.factor);
  r0pb_control_triplet<e4> sum{{e4::ZERO(), e4::ZERO(), e4::ZERO()}};
#pragma unroll 1
  for (u32 member = 0; member < 2; ++member) {
    const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
    const auto term = r0pb_control_e4_group_member(desc, instruction, row, selector);
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      sum.values[cell] = e4::add(sum.values[cell], term.values[cell]);
  }
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::fma(core, sum.values[cell], values[cell]);
  return pc;
}

DEVICE_FORCEINLINE void r0pb_sectioned_accumulate_linear_wide(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction, const u32 row,
                                                              const r0_selector_pair selector, r0_u96_accumulator (&outer)[3][4]) {
  if (selector.has_infinity())
    return;
  const auto source = r0pb_control_pair_values(r0pb_control_direct_e4(desc, instruction.source_a), row, selector);
  const bf source_zero[4]{source.values[0][0][0], source.values[0][0][1], source.values[0][1][0], source.values[0][1][1]};
  const bf source_one[4]{source.values[1][0][0], source.values[1][0][1], source.values[1][1][0], source.values[1][1][1]};
#pragma unroll
  for (u32 limb = 0; limb < 4; ++limb) {
    const e4 basis = r0_coefficient(instruction.factor + limb);
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

template <bool MayNegate>
DEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_sectioned_mixed_product(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction,
                                                                         const u32 row, const r0_selector_pair selector) {
  const auto bf_pair = r0pb_control_pair_values(r0pb_control_direct_bf(desc, instruction.source_a), row, selector);
  bf delta_bf = r0_sub(bf_pair.values[1], bf_pair.values[0]);
  if constexpr (MayNegate) {
    if ((instruction.factor & R0PB_CONTROL_ID_MASK) == 1)
      delta_bf = bf::neg(delta_bf);
  }
  const e4 delta_e4 = r0_x2_delta<e4>(r0pb_control_direct_e4(desc, instruction.source_b), row, selector);
  const e4 product = e4::mul(delta_e4, delta_bf);
  return {{e4::ZERO(), product, product}};
}

template <bool MayNegate>
DEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_sectioned_full_product(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction,
                                                                        const u32 row, const r0_selector_pair selector) {
  e4 product = e4::mul(r0_x2_delta<e4>(r0pb_control_direct_e4(desc, instruction.source_a), row, selector),
                       r0_x2_delta<e4>(r0pb_control_direct_e4(desc, instruction.source_b), row, selector));
  if constexpr (MayNegate) {
    if ((instruction.factor & R0PB_CONTROL_ID_MASK) == 1)
      product = e4::neg(product);
  }
  return {{e4::ZERO(), product, product}};
}

template <u16 Shape>
DEVICE_FORCEINLINE r0pb_control_triplet<e4> r0pb_sectioned_product(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction,
                                                                   const u32 row, const r0_selector_pair selector) {
  constexpr bool has_mixed = (Shape & R0PB_SHAPE_E4_SINGLETON_CLASS_3) != 0;
  constexpr bool has_full = (Shape & R0PB_SHAPE_E4_SINGLETON_CLASS_5) != 0;
  if constexpr (has_mixed && has_full)
    return instruction.term_class == 3 ? r0pb_sectioned_mixed_product<false>(desc, instruction, row, selector)
                                       : r0pb_sectioned_full_product<false>(desc, instruction, row, selector);
  if constexpr (has_mixed)
    return r0pb_sectioned_mixed_product<false>(desc, instruction, row, selector);
  static_assert(has_full, "sectioned E4 product loop has no enabled class");
  return r0pb_sectioned_full_product<false>(desc, instruction, row, selector);
}

template <u16 Shape>
DEVICE_FORCEINLINE void r0pb_sectioned_execute_singleton(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction instruction, const u32 row,
                                                         const r0_selector_pair selector, e4 (&values)[3]) {
  r0pb_control_instruction product = instruction;
  product.factor = 0;
  const auto term = r0pb_sectioned_product<Shape>(desc, product, row, selector);
  constexpr bool may_negate = (Shape & R0PB_SHAPE_E4_NEGATIVE_FACTOR) != 0;
  const e4 core = r0pb_sectioned_coefficient<may_negate>(instruction.factor);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::fma(core, term.values[cell], values[cell]);
}

template <bool Mixed, bool MayNegate>
DEVICE_FORCEINLINE void r0pb_sectioned_execute_pair_members(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction head,
                                                            const r0pb_control_instruction first, const r0pb_control_instruction second, const u32 row,
                                                            const r0_selector_pair selector, e4 (&values)[3]) {
  r0pb_control_triplet<e4> first_term;
  r0pb_control_triplet<e4> second_term;
  if constexpr (Mixed) {
    first_term = r0pb_sectioned_mixed_product<MayNegate>(desc, first, row, selector);
    second_term = r0pb_sectioned_mixed_product<MayNegate>(desc, second, row, selector);
  } else {
    first_term = r0pb_sectioned_full_product<MayNegate>(desc, first, row, selector);
    second_term = r0pb_sectioned_full_product<MayNegate>(desc, second, row, selector);
  }
  const e4 core = r0_coefficient(head.factor);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    values[cell] = e4::fma(core, e4::add(first_term.values[cell], second_term.values[cell]), values[cell]);
}

template <u16 Shape>
DEVICE_FORCEINLINE void r0pb_sectioned_execute_loaded_pair(const r0_grouped_slot_ordinary &desc, const r0pb_control_instruction head,
                                                           const r0pb_control_instruction first, const r0pb_control_instruction second, const u32 row,
                                                           const r0_selector_pair selector, e4 (&values)[3]) {
  constexpr bool has_mixed_pair = (Shape & R0PB_SHAPE_E4_PAIR_CLASS_3) != 0;
  constexpr bool has_full_pair = (Shape & R0PB_SHAPE_E4_PAIR_CLASS_5) != 0;
  constexpr bool may_negate = (Shape & R0PB_SHAPE_E4_NEGATIVE_FACTOR) != 0;
  static_assert(has_mixed_pair || has_full_pair, "sectioned fixed-pair loop has no enabled class");
  if constexpr (has_mixed_pair && has_full_pair) {
    if (first.term_class == 3)
      r0pb_sectioned_execute_pair_members<true, may_negate>(desc, head, first, second, row, selector, values);
    else
      r0pb_sectioned_execute_pair_members<false, may_negate>(desc, head, first, second, row, selector, values);
  } else if constexpr (has_mixed_pair) {
    r0pb_sectioned_execute_pair_members<true, may_negate>(desc, head, first, second, row, selector, values);
  } else {
    r0pb_sectioned_execute_pair_members<false, may_negate>(desc, head, first, second, row, selector, values);
  }
}

template <u16 Shape>
DEVICE_FORCEINLINE u32 r0pb_sectioned_execute_pair(const r0_grouped_slot_ordinary &desc, const u16 *program, const r0pb_control_instruction head, u32 pc,
                                                   const u32 row, const r0_selector_pair selector, e4 (&values)[3]) {
  const r0pb_control_instruction first = r0pb_control_read_instruction(program, pc++);
  const r0pb_control_instruction second = r0pb_control_read_instruction(program, pc++);
  r0pb_sectioned_execute_loaded_pair<Shape>(desc, head, first, second, row, selector, values);
  return pc;
}

struct r0pb_sectioned_wide9_placement {
  static constexpr u32 block_threads = 288;
  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x; }
  DEVICE_FORCEINLINE static u32 selector_id() { return threadIdx.x >> 5; }
};

struct r0pb_sectioned_split3_placement {
  static constexpr u32 block_threads = 96;
  DEVICE_FORCEINLINE static u32 row_tile() { return blockIdx.x / 3; }
  DEVICE_FORCEINLINE static u32 selector_id() { return 3 * (blockIdx.x % 3) + (threadIdx.x >> 5); }
};

DEVICE_FORCEINLINE r0_selector_pair r0pb_sectioned_selector(const u32 selector_id) {
  const u32 selector_x0 = selector_id / 3;
  const u32 selector_x1 = selector_id % 3;
  return {selector_x0, selector_x1, __all_sync(0xffffffffu, selector_x0 == 2) != 0, __all_sync(0xffffffffu, selector_x1 == 2) != 0};
}

template <u16 Shape>
DEVICE_FORCEINLINE void r0pb_evaluate_sectioned_selector(const r0_grouped_slot_ordinary &desc, const u32 row, const r0_selector_pair selector,
                                                         e4 (&values)[3]) {
  const u16 *program = desc.program;
  r0_u96_accumulator outer[3][4]{};
  u32 pc = 0;
  constexpr bool bf_may_use_procedural = (Shape & R0PB_SHAPE_BF_PROCEDURAL) != 0;
  constexpr bool bf_may_have_banked = (Shape & R0PB_SHAPE_BF_BANKED_IMMEDIATE) != 0;
  constexpr bool bf_may_reduce = (Shape & R0PB_SHAPE_BF_INNER_REDUCTION) != 0;
  constexpr bool bf_has_linear_tail = (Shape & R0PB_SHAPE_BF_LINEAR_TAIL) != 0;
  constexpr bool bf_may_negate = (Shape & R0PB_SHAPE_BF_NEGATIVE_FACTOR) != 0;
  constexpr bool bf_may_have_single_product = (Shape & R0PB_SHAPE_BF_SINGLE_PRODUCT_PREFIX) != 0;
  while (pc < desc.meta.sections[0]) {
    const r0pb_control_instruction head = r0pb_control_read_instruction(program, pc++);
    pc = r0pb_control_execute_bf_atom<bf_may_use_procedural, bf_may_have_banked, bf_may_reduce, bf_has_linear_tail, bf_may_negate, bf_may_have_single_product>(
        desc, program, head, pc, row, selector, outer);
  }
  while (pc < desc.meta.sections[1]) {
    const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
    r0pb_sectioned_accumulate_linear_wide(desc, instruction, row, selector, outer);
  }
  r0pb_control_reduce_outer(outer, values);
  constexpr bool has_e4_singleton = (Shape & (R0PB_SHAPE_E4_SINGLETON_CLASS_3 | R0PB_SHAPE_E4_SINGLETON_CLASS_5)) != 0;
  if constexpr (has_e4_singleton) {
    while (pc < desc.meta.sections[2]) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
      r0pb_sectioned_execute_singleton<Shape>(desc, instruction, row, selector, values);
    }
  }
  constexpr bool has_e4_pair = (Shape & R0PB_SHAPE_E4_FIXED_PAIR) != 0;
  if constexpr (has_e4_pair) {
    while (pc < desc.meta.sections[3]) {
      const r0pb_control_instruction head = r0pb_control_read_instruction(program, pc++);
      pc = r0pb_sectioned_execute_pair<Shape>(desc, program, head, pc, row, selector, values);
    }
  }
}

template <u16 Shape, typename Geometry, typename Placement> DEVICE_FORCEINLINE void r0pb_execute_sectioned(const r0_grouped_slot_ordinary &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = Placement::row_tile();
  const r0_selector_pair selector = r0pb_sectioned_selector(Placement::selector_id());
  const u32 global_row = row_tile * 32 + lane;
  const bool active = global_row < (1u << desc.common.log_rows);
  const u32 row = active ? global_row : 0;
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  r0pb_evaluate_sectioned_selector<Shape>(desc, row, selector, values);
  r0pb_publish<r0_grouped_slot_ordinary, Geometry>(desc, row_tile, lane, active, values);
}

DEVICE_FORCEINLINE void r0pb_publish_sectioned_triplet(const r0_grouped_slot_ordinary &desc, const u32 row_tile, const u32 lane, const bool active,
                                                       const u32 selector_id, e4 (&values)[3]) {
  const e4 equality = r0pb_eq(desc, active ? row_tile * 32 + lane : 0);
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    e4 value = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    value = r0_warp_sum(value);
    if (lane == 0)
      store<e4, st_modifier::cs>(r0pb_partials(desc), value, static_cast<size_t>(row_tile) * R0_WINDOW_CELLS + 3 * selector_id + x2);
  }
}

template <u16 Shape> DEVICE_FORCEINLINE void r0pb_execute_sectioned_serial3_low(const r0_grouped_slot_ordinary &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = blockIdx.x;
  const u32 owner_x0 = threadIdx.x >> 5;
  const u32 global_row = row_tile * 32 + lane;
  const bool active = global_row < (1u << desc.common.log_rows);
  const u32 row = active ? global_row : 0;
#pragma unroll 1
  for (u32 partition_x1 = 0; partition_x1 < 3; ++partition_x1) {
    const u32 selector_id = 3 * owner_x0 + partition_x1;
    const r0_selector_pair selector = r0pb_sectioned_selector(selector_id);
    e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
    r0pb_evaluate_sectioned_selector<Shape>(desc, row, selector, values);
    r0pb_publish_sectioned_triplet(desc, row_tile, lane, active, selector_id, values);
  }
}

template <bool MayUseProcedural, bool MayHaveBanked, bool MayReduce, bool HasLinearTail, bool MayNegate, bool MayHaveSingleProduct>
DEVICE_FORCEINLINE u32 r0pb_control_execute_bf_atom_serial3_high(const r0_grouped_slot_ordinary &desc, const u16 *program, const r0pb_control_instruction head,
                                                                 u32 pc, const u32 row, const r0_selector_pair (&selectors)[3],
                                                                 r0_u96_accumulator (&outer)[3][3][4]) {
  if (head.term_class != R0PB_CONTROL_GROUP_BF) {
    const e4 core = r0pb_sectioned_coefficient<MayNegate>(head.factor);
#pragma unroll
    for (u32 partition = 0; partition < 3; ++partition)
      r0pb_control_outer_add_wide(outer[partition], core,
                                  r0pb_control_bf_term<MayUseProcedural>(desc, head.term_class, head.source_a, head.source_b, row, selectors[partition]));
    return pc;
  }

  const u16 arity = head.source_a;
  const u16 product_prefix = head.source_b & R0PB_CONTROL_ID_MASK;
  const e4 core = r0_coefficient(head.factor);
  r0pb_control_triplet<bf> sum[3]{};
  u16 member = 0;
  if (product_prefix >= 2) {
    u64 wide_sum[3]{};
#pragma unroll 1
    for (; member < product_prefix; ++member) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
#pragma unroll
      for (u32 partition = 0; partition < 3; ++partition) {
        r0pb_control_accumulate_product_wide<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selectors[partition], wide_sum[partition]);
        if constexpr (MayReduce) {
          if ((instruction.factor & R0PB_CONTROL_FLAG) != 0)
            r0pb_control_reduce_and_rebase_bf_wide(wide_sum[partition]);
        }
      }
    }
#pragma unroll
    for (u32 partition = 0; partition < 3; ++partition) {
      const bf reduced = r0pb_control_reduce_bf_wide(wide_sum[partition]);
      sum[partition].values[1] = reduced;
      sum[partition].values[2] = reduced;
    }
  }

  if constexpr (MayHaveSingleProduct) {
    if (product_prefix < 2) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
#pragma unroll
      for (u32 partition = 0; partition < 3; ++partition)
        r0pb_control_accumulate_bf_member<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selectors[partition], sum[partition]);
      ++member;
    }
  }

  if constexpr (HasLinearTail) {
    if (member < arity) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
#pragma unroll
      for (u32 partition = 0; partition < 3; ++partition)
        r0pb_control_accumulate_bf_member<MayUseProcedural, MayHaveBanked, MayNegate>(desc, instruction, row, selectors[partition], sum[partition]);
    }
  }
#pragma unroll
  for (u32 partition = 0; partition < 3; ++partition)
    r0pb_control_outer_add_wide(outer[partition], core, sum[partition]);
  return pc;
}

template <u16 Shape> DEVICE_FORCEINLINE void r0pb_execute_sectioned_serial3_high(const r0_grouped_slot_ordinary &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = blockIdx.x;
  const u32 owner_x0 = threadIdx.x >> 5;
  const u32 global_row = row_tile * 32 + lane;
  const bool active = global_row < (1u << desc.common.log_rows);
  const u32 row = active ? global_row : 0;
  const r0_selector_pair selectors[3]{r0pb_sectioned_selector(3 * owner_x0), r0pb_sectioned_selector(3 * owner_x0 + 1),
                                      r0pb_sectioned_selector(3 * owner_x0 + 2)};
  const u16 *program = desc.program;
  r0_u96_accumulator outer[3][3][4]{};
  u32 pc = 0;
  constexpr bool bf_may_use_procedural = (Shape & R0PB_SHAPE_BF_PROCEDURAL) != 0;
  constexpr bool bf_may_have_banked = (Shape & R0PB_SHAPE_BF_BANKED_IMMEDIATE) != 0;
  constexpr bool bf_may_reduce = (Shape & R0PB_SHAPE_BF_INNER_REDUCTION) != 0;
  constexpr bool bf_has_linear_tail = (Shape & R0PB_SHAPE_BF_LINEAR_TAIL) != 0;
  constexpr bool bf_may_negate = (Shape & R0PB_SHAPE_BF_NEGATIVE_FACTOR) != 0;
  constexpr bool bf_may_have_single_product = (Shape & R0PB_SHAPE_BF_SINGLE_PRODUCT_PREFIX) != 0;
  while (pc < desc.meta.sections[0]) {
    const r0pb_control_instruction head = r0pb_control_read_instruction(program, pc++);
    pc = r0pb_control_execute_bf_atom_serial3_high<bf_may_use_procedural, bf_may_have_banked, bf_may_reduce, bf_has_linear_tail, bf_may_negate,
                                                   bf_may_have_single_product>(desc, program, head, pc, row, selectors, outer);
  }
  while (pc < desc.meta.sections[1]) {
    const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
#pragma unroll
    for (u32 partition = 0; partition < 3; ++partition)
      r0pb_sectioned_accumulate_linear_wide(desc, instruction, row, selectors[partition], outer[partition]);
  }
  e4 partition_values[3][3]{};
#pragma unroll
  for (u32 partition = 0; partition < 3; ++partition)
    r0pb_control_reduce_outer(outer[partition], partition_values[partition]);
  constexpr bool has_e4_singleton = (Shape & (R0PB_SHAPE_E4_SINGLETON_CLASS_3 | R0PB_SHAPE_E4_SINGLETON_CLASS_5)) != 0;
  if constexpr (has_e4_singleton) {
    while (pc < desc.meta.sections[2]) {
      const r0pb_control_instruction instruction = r0pb_control_read_instruction(program, pc++);
#pragma unroll
      for (u32 partition = 0; partition < 3; ++partition)
        r0pb_sectioned_execute_singleton<Shape>(desc, instruction, row, selectors[partition], partition_values[partition]);
    }
  }
  constexpr bool has_e4_pair = (Shape & R0PB_SHAPE_E4_FIXED_PAIR) != 0;
  if constexpr (has_e4_pair) {
    while (pc < desc.meta.sections[3]) {
      const r0pb_control_instruction head = r0pb_control_read_instruction(program, pc++);
      const r0pb_control_instruction first = r0pb_control_read_instruction(program, pc++);
      const r0pb_control_instruction second = r0pb_control_read_instruction(program, pc++);
#pragma unroll
      for (u32 partition = 0; partition < 3; ++partition)
        r0pb_sectioned_execute_loaded_pair<Shape>(desc, head, first, second, row, selectors[partition], partition_values[partition]);
    }
  }
  e4 values[9];
#pragma unroll
  for (u32 partition = 0; partition < 3; ++partition)
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      values[3 * partition + cell] = partition_values[partition][cell];
  r0pb_publish<r0_grouped_slot_ordinary, r0pb_sectioned_serial3_high_geometry>(desc, row_tile, lane, active, values);
}

#define AB_R0PB_DEFINE_SECTIONED_WIDE9_KERNEL(Name, Shape)                                                                                                     \
  EXTERN __global__ __launch_bounds__(288, 3) void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                               \
    if (blockDim.x != r0pb_sectioned_wide9_placement::block_threads)                                                                                           \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned<Shape, r0pb_sectioned_wide9_geometry, r0pb_sectioned_wide9_placement>(desc);                                                        \
  }

#define AB_R0PB_DEFINE_SECTIONED_WIDE9_BOUNDED_KERNEL(Name, Shape, MinBlocks)                                                                                  \
  EXTERN __global__ __launch_bounds__(288, MinBlocks) void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                       \
    if (blockDim.x != r0pb_sectioned_wide9_placement::block_threads)                                                                                           \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned<Shape, r0pb_sectioned_wide9_geometry, r0pb_sectioned_wide9_placement>(desc);                                                        \
  }

#define AB_R0PB_DEFINE_SECTIONED_SPLIT3_KERNEL(Name, Shape)                                                                                                    \
  EXTERN __global__ void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                                                         \
    if (blockDim.x != r0pb_sectioned_split3_placement::block_threads)                                                                                          \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned<Shape, r0pb_sectioned_split3_geometry, r0pb_sectioned_split3_placement>(desc);                                                      \
  }

#define AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(Name, Shape, MinBlocks)                                                                                 \
  EXTERN __global__ __launch_bounds__(96, MinBlocks) void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                        \
    if (blockDim.x != r0pb_sectioned_split3_placement::block_threads)                                                                                          \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned<Shape, r0pb_sectioned_split3_geometry, r0pb_sectioned_split3_placement>(desc);                                                      \
  }

#define AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_KERNEL(Name, Shape)                                                                                               \
  EXTERN __global__ void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                                                         \
    if (blockDim.x != r0pb_sectioned_serial3_low_geometry::threads)                                                                                            \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned_serial3_low<Shape>(desc);                                                                                                           \
  }

#define AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(Name, Shape, MinBlocks)                                                                            \
  EXTERN __global__ __launch_bounds__(96, MinBlocks) void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                        \
    if (blockDim.x != r0pb_sectioned_serial3_low_geometry::threads)                                                                                            \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned_serial3_low<Shape>(desc);                                                                                                           \
  }

#define AB_R0PB_DEFINE_SECTIONED_SERIAL3_HIGH_KERNEL(Name, Shape)                                                                                              \
  EXTERN __global__ void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                                                         \
    if (blockDim.x != r0pb_sectioned_serial3_high_geometry::threads)                                                                                           \
      return;                                                                                                                                                  \
    r0pb_execute_sectioned_serial3_high<Shape>(desc);                                                                                                          \
  }

DEVICE_FORCEINLINE void r0pb_execute_dedicated_grouped_u64_u96_partitioned(const r0_grouped_slot_ordinary &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = blockIdx.x / 3;
  const u32 selector_id = 3 * (blockIdx.x % 3) + (threadIdx.x >> 5);
  const u32 selector_x0 = selector_id / 3;
  const u32 selector_x1 = selector_id % 3;
  const r0_selector_pair selector{selector_x0, selector_x1, __all_sync(0xffffffffu, selector_x0 == 2) != 0, __all_sync(0xffffffffu, selector_x1 == 2) != 0};
  const u32 global_row = row_tile * 32 + lane;
  const bool active = global_row < (1u << desc.common.log_rows);
  const u32 row = active ? global_row : 0;
  const u16 *program = desc.program;
  r0_u96_accumulator outer[3][4]{};
  u32 pc = 0;
  while (pc < desc.meta.sections[0]) {
    const r0pb_control_instruction head = r0pb_control_read_instruction(program, pc++);
    pc = r0pb_control_execute_bf_atom(desc, program, head, pc, row, selector, outer);
  }
  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  r0pb_control_reduce_outer(outer, values);
  while (pc < desc.meta.sections[1]) {
    const r0pb_control_instruction head = r0pb_control_read_instruction(program, pc++);
    pc = r0pb_control_execute_e4_atom(desc, program, head, pc, row, selector, values);
  }
  r0pb_publish<r0_grouped_slot_ordinary, r0pb_cta96_partitioned_geometry>(desc, row_tile, lane, active, values);
}

#define AB_R0PB_DEFINE_DEDICATED_GROUPED_U64_U96_PARTITIONED_KERNEL(Name)                                                                                      \
  EXTERN __global__ void Name(const __grid_constant__ r0_grouped_slot_ordinary desc) {                                                                         \
    if (blockDim.x != 96)                                                                                                                                      \
      return;                                                                                                                                                  \
    r0pb_execute_dedicated_grouped_u64_u96_partitioned(desc);                                                                                                  \
  }

} // namespace airbender::gkr_windowed_bench
