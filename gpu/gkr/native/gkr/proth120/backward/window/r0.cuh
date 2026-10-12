#pragma once

#include "../../../backward/window/window_geometry.cuh"
#include "../accumulator_pr.cuh"

namespace airbender::gkr::proth120::backward {

using ::airbender::gkr::bwd_source_lane_column;
using ::airbender::gkr::bwd_source_lane_slot;
using ::airbender::gkr::bwd_source_window;
using ::airbender::gkr::gkr_eq_sizes;
using ::airbender::gkr::backward::bwd_window_corner_index;
using ::airbender::gkr::backward::BWD_WINDOW_FLAG;
using ::airbender::gkr::backward::BWD_WINDOW_ID_MASK;
using ::airbender::gkr::backward::bwd_window_lane;
using ::airbender::gkr::backward::BWD_WINDOW_OPCODE_GROUP_BF;
using ::airbender::gkr::backward::BWD_WINDOW_OPCODE_LINEAR_BF;
using ::airbender::gkr::backward::BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL;
using ::airbender::gkr::backward::BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB;
using ::airbender::gkr::backward::BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B;
using ::airbender::gkr::backward::bwd_window_pair;
using ::airbender::gkr::backward::BWD_WINDOW_SECTION_BF;
using ::airbender::gkr::backward::bwd_window_selector;
using ::airbender::gkr::backward::bwd_window_selector_id;
using ::airbender::gkr::backward::bwd_window_selector_pair;
using ::airbender::gkr::backward::BWD_WINDOW_SHAPE_BF_BANKED_IMMEDIATE;
using ::airbender::gkr::backward::BWD_WINDOW_SHAPE_BF_LINEAR_TAIL;
using ::airbender::gkr::backward::BWD_WINDOW_SHAPE_BF_NEGATIVE_FACTOR;
using ::airbender::gkr::backward::BWD_WINDOW_SHAPE_DEFINED_BITS;
using ::airbender::gkr::backward::bwd_window_triplet;

constexpr u32 PR_WINDOW_ADDR_SLOTS = 64;
constexpr u32 PR_WINDOW_SECTION_WORDS = 4;
constexpr u32 PR_WINDOW_PROGRAM_WORD_CAP = 9216;
constexpr u32 PR_WINDOW_ROWS_PER_TILE = 32;
constexpr u32 PR_WINDOW_SELECTOR_PAIRS = 9;
constexpr u32 PR_WINDOW_TENSOR_CELLS = 27;
constexpr u32 PR_WINDOW_BLOCK_THREADS = 288;
constexpr u32 PR_WINDOW_MAX_PARTS = 16;
constexpr u32 PR_WINDOW_MIN_BLOCKS = 2;
constexpr u32 PR_WINDOW_SCALAR_SEED_NONE = 0xffffu;
constexpr u16 PR_WINDOW_SHAPE_GENERAL = 0x7f7;
constexpr u16 PR_WINDOW_SHAPE_UNIT = 0x771;
constexpr u16 PR_WINDOW_SHAPE_TAILS = 0x7ff;

static_assert(PR_WINDOW_ADDR_SLOTS == ::airbender::gkr::BWD_SOURCE_WINDOW_SLOTS);
static_assert(PR_WINDOW_SECTION_WORDS == ::airbender::gkr::backward::BWD_WINDOW_SECTION_WORDS);
static_assert(PR_WINDOW_PROGRAM_WORD_CAP == ::airbender::gkr::backward::BWD_WINDOW_PROGRAM_WORD_CAP);
static_assert(PR_WINDOW_ROWS_PER_TILE == ::airbender::gkr::backward::BWD_WINDOW_ROWS_PER_TILE);
static_assert(PR_WINDOW_TENSOR_CELLS == ::airbender::gkr::backward::BWD_WINDOW_TENSOR_CELLS);
static_assert(PR_WINDOW_BLOCK_THREADS == PR_WINDOW_SELECTOR_PAIRS * PR_WINDOW_ROWS_PER_TILE);
static_assert(PR_WINDOW_BLOCK_THREADS == ::airbender::gkr::backward::BWD_WINDOW_BLOCK_THREADS);

struct alignas(16) bwd_window_desc_pr {
  bwd_source_window slot[PR_WINDOW_ADDR_SLOTS];
  const pr *eq_low;
  pr *partials;
  u32 log_rows;
  gkr_eq_sizes eq_sizes;
  u32 sections[PR_WINDOW_SECTION_WORDS];
  u16 program[PR_WINDOW_PROGRAM_WORD_CAP];
  const pr *eq_high;
  const pr *coefficients;
  const pr *immediates;
  u32 immediate_count;
  u32 _pad;
};

struct bwd_window_partition_bounds_pr {
  u32 parts;
  u32 ends[PR_WINDOW_MAX_PARTS][PR_WINDOW_SECTION_WORDS];
};

struct alignas(4) pr_window_instruction {
  u16 opcode;
  u16 factor;
  u16 source_a;
  u16 source_b;
};

static_assert(sizeof(bwd_window_desc_pr) == 19536 && alignof(bwd_window_desc_pr) == 16);
static_assert(__builtin_offsetof(bwd_window_desc_pr, slot) == 0);
static_assert(__builtin_offsetof(bwd_window_desc_pr, eq_low) == 1024);
static_assert(__builtin_offsetof(bwd_window_desc_pr, partials) == 1032);
static_assert(__builtin_offsetof(bwd_window_desc_pr, log_rows) == 1040);
static_assert(__builtin_offsetof(bwd_window_desc_pr, eq_sizes) == 1044);
static_assert(__builtin_offsetof(bwd_window_desc_pr, sections) == 1056);
static_assert(__builtin_offsetof(bwd_window_desc_pr, program) == 1072);
static_assert(__builtin_offsetof(bwd_window_desc_pr, eq_high) == 19504);
static_assert(__builtin_offsetof(bwd_window_desc_pr, coefficients) == 19512);
static_assert(__builtin_offsetof(bwd_window_desc_pr, immediates) == 19520);
static_assert(__builtin_offsetof(bwd_window_desc_pr, immediate_count) == 19528);
static_assert(__builtin_offsetof(bwd_window_desc_pr, _pad) == 19532);
static_assert(sizeof(bwd_window_partition_bounds_pr) == 260 && alignof(bwd_window_partition_bounds_pr) == 4);
static_assert(__builtin_offsetof(bwd_window_partition_bounds_pr, ends) == 4);
static_assert(sizeof(pr_window_instruction) == 8 && alignof(pr_window_instruction) == 4);
static_assert(__builtin_offsetof(bwd_window_desc_pr, program) % alignof(pr_window_instruction) == 0);
static_assert(PR_WINDOW_PROGRAM_WORD_CAP % 4 == 0);
static_assert(sizeof(bwd_window_desc_pr) + sizeof(u32) + sizeof(bwd_window_partition_bounds_pr) <= 32764);

DEVICE_FORCEINLINE pr_window_instruction pr_window_read(const u16 *program, const u32 pc) {
  return reinterpret_cast<const pr_window_instruction *>(program)[pc];
}

DEVICE_FORCEINLINE pr pr_window_small(const u32 value) {
  const u32 natural[4] = {value, 0, 0, 0};
  return pr::from_u128_with_reduction(natural);
}

DEVICE_FORCEINLINE void pr_window_push(PrSum32 &sum, const pr term) {
  if (sum.full()) {
    const pr total = sum.flush();
    sum.add(total);
  }
  sum.add(term);
}

DEVICE_FORCEINLINE const pr *pr_window_column(const bwd_window_desc_pr &desc, const u16 packed) {
  const bwd_source_window &address = desc.slot[bwd_source_lane_slot(packed)];
  return reinterpret_cast<const pr *>(address.base + static_cast<size_t>(bwd_source_lane_column(packed)) * address.r0_stride_bytes);
}

template <u32 Count> DEVICE_FORCEINLINE auto pr_window_load(const pr *column, const u32 index) {
  return ::airbender::gkr::backward::bwd_window_load<pr, Count>(column, index);
}

DEVICE_FORCEINLINE bwd_window_pair<pr> pr_window_direct_pair(const pr *column, const u32 row, const bwd_window_selector_pair selector) {
  if (!selector.x0_infinity() && !selector.x1_infinity()) {
    const auto values = pr_window_load<2>(column, bwd_window_corner_index(row, selector.x0, selector.x1, 0));
    return {{values.values[0], values.values[1]}};
  }
  if (selector.x0_infinity() && !selector.x1_infinity()) {
    const auto zero = pr_window_load<2>(column, bwd_window_corner_index(row, 0, selector.x1, 0));
    const auto one = pr_window_load<2>(column, bwd_window_corner_index(row, 1, selector.x1, 0));
    return {{pr::sub(one.values[0], zero.values[0]), pr::sub(one.values[1], zero.values[1])}};
  }
  if (!selector.x0_infinity() && selector.x1_infinity()) {
    const auto values = pr_window_load<4>(column, bwd_window_corner_index(row, selector.x0, 0, 0));
    return {{pr::sub(values.values[2], values.values[0]), pr::sub(values.values[3], values.values[1])}};
  }
  const auto values = pr_window_load<8>(column, bwd_window_corner_index(row, 0, 0, 0));
  const pr at_x1_zero_0 = pr::sub(values.values[4], values.values[0]);
  const pr at_x1_zero_1 = pr::sub(values.values[5], values.values[1]);
  const pr at_x1_one_0 = pr::sub(values.values[6], values.values[2]);
  const pr at_x1_one_1 = pr::sub(values.values[7], values.values[3]);
  return {{pr::sub(at_x1_one_0, at_x1_zero_0), pr::sub(at_x1_one_1, at_x1_zero_1)}};
}

DEVICE_FORCEINLINE bwd_window_pair<pr> pr_window_procedural_pair(const u8 procedural_kind, const u32 row, const bwd_window_selector_pair selector) {
  static_assert(GKR_TIMESTAMP_COLUMNS_NUM_BITS >= 3);
  const u32 base = row << 3;
  u32 origin;
  u32 step;
  switch (procedural_kind) {
  case BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS:
    if (base >= (1u << 16))
      return {{pr_zero(), pr_zero()}};
    origin = base;
    step = 1;
    break;
  case BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP:
    if (base >= (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS))
      return {{pr_zero(), pr_zero()}};
    origin = base;
    step = 1;
    break;
  case BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW:
    origin = (base << 2) & 0xffffu;
    step = 4;
    break;
  case BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH: {
    const pr value = selector.has_infinity() ? pr_zero() : pr_window_small(base >> 14);
    return {{value, value}};
  }
  default:
    return {{pr_zero(), pr_zero()}};
  }
  if (selector.has_infinity()) {
    const u32 slope = selector.x0_infinity() ? (selector.x1_infinity() ? 0 : 4 * step) : 2 * step;
    const pr value = pr_window_small(slope);
    return {{value, value}};
  }
  const u32 value = origin + step * (4 * selector.x0 + 2 * selector.x1);
  return {{pr_window_small(value), pr_window_small(value + step)}};
}

DEVICE_FORCEINLINE bwd_window_pair<pr> pr_window_operand(const bwd_window_desc_pr &desc, const bool procedural, const u16 operand, const u32 row,
                                                         const bwd_window_selector_pair selector) {
  if (procedural)
    return pr_window_procedural_pair(static_cast<u8>(operand), row, selector);
  return pr_window_direct_pair(pr_window_column(desc, operand), row, selector);
}

DEVICE_FORCEINLINE bool pr_window_is_linear(const u16 opcode) {
  return opcode == BWD_WINDOW_OPCODE_LINEAR_BF || opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL;
}

DEVICE_FORCEINLINE bool pr_window_procedural_a(const u16 opcode) {
  return opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL || opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB;
}

DEVICE_FORCEINLINE bool pr_window_procedural_b(const u16 opcode) {
  return opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_B || opcode == BWD_WINDOW_OPCODE_PRODUCT_BF_BF_PROCEDURAL_AB;
}

DEVICE_FORCEINLINE pr pr_window_coefficient(const bwd_window_desc_pr &desc, const u32 id) { return load<pr, ld_modifier::ca>(desc.coefficients, id); }

template <bool MayNegate> DEVICE_FORCEINLINE pr pr_window_signed_coefficient(const bwd_window_desc_pr &desc, const u16 encoded) {
  const pr value = pr_window_coefficient(desc, encoded & BWD_WINDOW_ID_MASK);
  if constexpr (MayNegate)
    return (encoded & BWD_WINDOW_FLAG) != 0 ? pr_neg(value) : value;
  return value;
}

template <bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE bwd_window_pair<pr> pr_window_scaled_endpoints(const bwd_window_desc_pr &desc, const u16 factor, const bwd_window_pair<pr> a) {
  const u16 id = factor & BWD_WINDOW_ID_MASK;
  if (id == BWD_PROGRAM_IMMEDIATE_ONE)
    return a;
  if constexpr (MayNegate) {
    if (id == BWD_PROGRAM_IMMEDIATE_NEG_ONE)
      return {{pr_neg(a.values[0]), pr_neg(a.values[1])}};
  }
  if constexpr (MayHaveBanked) {
    const pr f = load<pr, ld_modifier::ca>(desc.immediates, id - BWD_PROGRAM_IMMEDIATE_RESERVED);
    return {{pr::mul(f, a.values[0]), pr::mul(f, a.values[1])}};
  }
  return a;
}

DEVICE_FORCEINLINE bwd_window_triplet<pr> pr_window_endpoint_product(const bwd_window_pair<pr> a, const bwd_window_pair<pr> b) {
  const pr leading = pr::mul(pr::sub(a.values[1], a.values[0]), pr::sub(b.values[1], b.values[0]));
  return {{pr::mul(a.values[0], b.values[0]), pr::mul(a.values[1], b.values[1]), leading}};
}

template <bool MayHaveBanked, bool MayNegate>
DEVICE_FORCEINLINE void pr_window_accumulate_product(const bwd_window_desc_pr &desc, const pr_window_instruction instruction, const u32 row,
                                                     const bwd_window_selector_pair selector, PrSum32 (&inner)[3]) {
  const auto a = pr_window_operand(desc, pr_window_procedural_a(instruction.opcode), instruction.source_a, row, selector);
  const auto b = pr_window_operand(desc, pr_window_procedural_b(instruction.opcode), instruction.source_b, row, selector);
  const auto term = pr_window_endpoint_product(pr_window_scaled_endpoints<MayHaveBanked, MayNegate>(desc, instruction.factor, a), b);
  pr_window_push(inner[0], term.values[0]);
  pr_window_push(inner[1], term.values[1]);
  pr_window_push(inner[2], term.values[2]);
}

template <bool MayHaveBanked, bool LinearTails, bool MayNegate, bool PcEnd, bool NonEmptyProducts>
DEVICE_FORCEINLINE u32 pr_window_execute_atom(const bwd_window_desc_pr &desc, const pr_window_instruction head, u32 pc, const u32 row,
                                              const bwd_window_selector_pair selector, PrSum32 (&outer)[3]) {
  static_assert(!LinearTails || PcEnd, "linear tails need pc bounds");
  static_assert(!NonEmptyProducts || (PcEnd && !LinearTails), "NonEmptyProducts needs pc bounds and a tail-free shape");
  if (head.opcode != BWD_WINDOW_OPCODE_GROUP_BF) {
    const bool linear = pr_window_is_linear(head.opcode);
    if (linear && selector.has_infinity())
      return pc;
    const pr coefficient = pr_window_signed_coefficient<MayNegate>(desc, head.factor);
    const auto a = pr_window_operand(desc, pr_window_procedural_a(head.opcode), head.source_a, row, selector);
    if (linear) {
      pr_window_push(outer[0], pr::mul(coefficient, a.values[0]));
      pr_window_push(outer[1], pr::mul(coefficient, a.values[1]));
      return pc;
    }
    const auto b = pr_window_operand(desc, pr_window_procedural_b(head.opcode), head.source_b, row, selector);
    const auto term = pr_window_endpoint_product({{pr::mul(coefficient, a.values[0]), pr::mul(coefficient, a.values[1])}}, b);
    pr_window_push(outer[0], term.values[0]);
    pr_window_push(outer[1], term.values[1]);
    pr_window_push(outer[2], term.values[2]);
    return pc;
  }
  const u16 arity = head.source_a;
  const u16 product_prefix = head.source_b & BWD_WINDOW_ID_MASK;
  if constexpr (LinearTails) {
    if (product_prefix == 0 && selector.has_infinity())
      return pc + arity;
  }
  const pr core = pr_window_coefficient(desc, head.factor);
  pr sum[3] = {pr_zero(), pr_zero(), pr_zero()};
  const u32 product_end = pc + product_prefix;
  const u32 atom_end = pc + arity;
  if (NonEmptyProducts || product_prefix >= 2) {
    PrSum32 inner[3] = {PrSum32::zero(), PrSum32::zero(), PrSum32::zero()};
    if constexpr (NonEmptyProducts) {
#pragma unroll 1
      do {
        const pr_window_instruction instruction = pr_window_read(desc.program, pc++);
        pr_window_accumulate_product<MayHaveBanked, MayNegate>(desc, instruction, row, selector, inner);
      } while (pc < product_end);
    } else {
#pragma unroll 1
      for (; pc < product_end;) {
        const pr_window_instruction instruction = pr_window_read(desc.program, pc++);
        pr_window_accumulate_product<MayHaveBanked, MayNegate>(desc, instruction, row, selector, inner);
      }
    }
    sum[0] = inner[0].flush();
    sum[1] = inner[1].flush();
    sum[2] = inner[2].flush();
  }
  if constexpr (LinearTails) {
    if (selector.has_infinity()) {
      pc = atom_end;
    } else {
#pragma unroll 1
      for (; pc < atom_end;) {
        const pr_window_instruction instruction = pr_window_read(desc.program, pc++);
        const auto pair = pr_window_operand(desc, instruction.opcode == BWD_WINDOW_OPCODE_LINEAR_BF_PROCEDURAL, instruction.source_a, row, selector);
        const auto scaled = pr_window_scaled_endpoints<MayHaveBanked, MayNegate>(desc, instruction.factor, pair);
        sum[0] = pr::add(sum[0], scaled.values[0]);
        sum[1] = pr::add(sum[1], scaled.values[1]);
      }
    }
  }
  pr_window_push(outer[0], pr::mul(core, sum[0]));
  pr_window_push(outer[1], pr::mul(core, sum[1]));
  pr_window_push(outer[2], pr::mul(core, sum[2]));
  return pc;
}

DEVICE_FORCEINLINE pr pr_window_quartet_shuffle_add(const pr value, const u32 mask) {
  return pr::add(value, ::airbender::primitives::memory::shfl_xor(0xffffffffu, value, static_cast<int>(mask), static_cast<int>(PR_WINDOW_ROWS_PER_TILE)));
}

DEVICE_FORCEINLINE void pr_window_publish(pr *partials, const size_t tile_slot, const u32 lane, const bool active, const bwd_window_selector_pair selector,
                                          const pr equality, const pr (&values)[3]) {
  pr sums[3];
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    sums[x2] = active ? pr::mul(equality, values[x2]) : pr_zero();
    sums[x2] = pr_window_quartet_shuffle_add(sums[x2], 1);
    sums[x2] = pr_window_quartet_shuffle_add(sums[x2], 2);
  }
  const u32 role = lane & 3u;
  pr value = role == 0 ? sums[0] : role == 1 ? sums[1] : role == 2 ? sums[2] : pr_zero();
#pragma unroll
  for (u32 mask = 4; mask < PR_WINDOW_ROWS_PER_TILE; mask <<= 1)
    value = pr_window_quartet_shuffle_add(value, mask);
  if (lane < 3)
    store<pr, st_modifier::cs>(partials, value, tile_slot * PR_WINDOW_TENSOR_CELLS + 9 * lane + 3 * selector.x1 + selector.x0);
}

template <u16 Shape>
DEVICE_FORCEINLINE void pr_window_execute(const bwd_window_desc_pr &desc, const u32 scalar_seed, const u32 start, const u32 end, const u32 part,
                                          pr *equality_by_lane) {
  static_assert((Shape & ~BWD_WINDOW_SHAPE_DEFINED_BITS) == 0, "undefined shape bits");
  constexpr bool unit_groups = Shape == PR_WINDOW_SHAPE_UNIT;
  constexpr bool linear_tails = (Shape & BWD_WINDOW_SHAPE_BF_LINEAR_TAIL) != 0;
  constexpr bool pc_end = unit_groups || linear_tails;
  constexpr bool may_have_banked = (Shape & BWD_WINDOW_SHAPE_BF_BANKED_IMMEDIATE) != 0;
  constexpr bool may_negate = (Shape & BWD_WINDOW_SHAPE_BF_NEGATIVE_FACTOR) != 0;
  const u32 lane = bwd_window_lane();
  const u32 row_tile = blockIdx.x;
  const bwd_window_selector_pair selector = bwd_window_selector(bwd_window_selector_id());
  const u32 global_row = row_tile * PR_WINDOW_ROWS_PER_TILE + lane;
  const bool active = global_row < (1u << desc.log_rows);
  const u32 row = active ? global_row : 0;
  PrSum32 outer[3] = {PrSum32::zero(), PrSum32::zero(), PrSum32::zero()};
#pragma unroll 1
  for (u32 pc = start; pc < end;) {
    const pr_window_instruction head = pr_window_read(desc.program, pc++);
    pc = pr_window_execute_atom<may_have_banked, linear_tails, may_negate, pc_end, unit_groups>(desc, head, pc, row, selector, outer);
  }
  pr values[3] = {outer[0].flush(), outer[1].flush(), outer[2].flush()};
  if (part == 0 && !selector.has_infinity() && scalar_seed != PR_WINDOW_SCALAR_SEED_NONE) {
    const pr scalar = pr_window_coefficient(desc, scalar_seed);
    values[0] = pr::add(values[0], scalar);
    values[1] = pr::add(values[1], scalar);
  }
  if (bwd_window_selector_id() == 0)
    equality_by_lane[lane] = gkr_compute_eq_inline_global<pr>(desc.eq_high, desc.eq_high + GKR_EQ_GROUP_TABLE_LEN, desc.eq_low, desc.eq_sizes, row);
  __syncthreads();
  pr *partials = desc.partials + static_cast<size_t>(part) * gridDim.x * PR_WINDOW_TENSOR_CELLS;
  pr_window_publish(partials, row_tile, lane, active, selector, equality_by_lane[lane], values);
}

} // namespace airbender::gkr::proth120::backward
